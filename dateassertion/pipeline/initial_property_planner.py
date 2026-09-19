"""Requirement 8.1 deterministic initial-property bootstrap planner.

The planner deliberately works before Formal feedback.  It expands exact RTL
relations into fixed primitive families, attaches every property to a semantic
region and (where applicable) concrete cross-module dependency edges, estimates
structural coverage potential, and greedily selects non-duplicate candidates by
marginal structural gain.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from math import ceil, sqrt
from pathlib import Path
import json
import re
from typing import Any

from dateassertion.ir.schema import ContractIR
from dateassertion.ontology.primitives import expression_signals
from dateassertion.pipeline.region_contracts import RULE_FIELD
from dateassertion.rtl_frontend.parser import RTLDesign
from dateassertion.rtl_frontend.semantic_graph import expression_role


SEMANTIC_WORDS = re.compile(
    r"valid|ready|req|ack|state|pc|data|addr|flush|stall|enable|wen|write|read|irq|exception",
    re.I,
)


@dataclass
class BootstrapCandidate:
    candidate_id: str
    contract: ContractIR
    scope: str
    primitive: str
    property_family: str
    region_id: str
    region_kind: str
    module: str
    function: str
    generation_reason: str
    rtl_relation: dict[str, Any]
    cross_dependency_ids: list[str]
    downstream_modules: list[str]
    structural_scope: list[str]
    score_components: dict[str, float]
    static_coverage_score: float
    estimated_marginal_gain: int = 0
    selection_rank: int | None = None
    selected: bool = False
    disposition: str = "CANDIDATE"
    rejection_reason: str = ""


def _safe_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_$]+", "_", value).strip("_").lower()


def _assignment_id(assignment: Any) -> str:
    return f"{assignment.module}:{Path(assignment.file).name}:{assignment.line}:{assignment.lhs}"


def _evidence(assignment: Any, scope: str, edge_ids: list[str]) -> list[dict[str, Any]]:
    path = Path(assignment.file)
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines() if path.is_file() else []
    start = max(1, assignment.line - 2)
    end = min(len(lines), assignment.line + 2)
    return [{
        "files": [assignment.file],
        "line_start": start,
        "line_end": end,
        "snippet": "\n".join(lines[start - 1:end]),
        "region_flow_scope": scope,
        "cross_dependency_ids": edge_ids,
    }]


def _safety_rejection(assignment: Any, design: RTLDesign) -> str:
    known = set(design.module_signals.get(assignment.module, {}))
    if assignment.lhs not in known:
        return "assignment target is absent from the module symbol table"
    target_info = design.module_signals[assignment.module][assignment.lhs]
    if target_info.kind.endswith("_array"):
        return "unpacked array target requires an elaborated element binding"
    if not assignment.rhs or assignment.rhs == assignment.lhs:
        return "empty or self-only assignment has no useful relation"
    referenced = expression_signals(assignment.rhs)
    guard = expression_signals(assignment.guard)
    if not referenced:
        return "constant-only relation is reserved for RESET family expansion"
    unknown = (referenced | guard) - known
    if unknown:
        return f"expression contains unresolved module symbols: {sorted(unknown)}"
    array_references = sorted(
        name for name in referenced | guard
        if design.module_signals[assignment.module][name].kind.endswith("_array")
    )
    if array_references:
        return (
            "unpacked array reference requires an elaborated element binding: "
            f"{array_references}"
        )
    if len(assignment.rhs) > 240 or len(assignment.guard) > 240:
        return "expression exceeds the bounded deterministic grounding limit"
    if "`" in assignment.rhs or "`" in assignment.guard or "//" in assignment.rhs:
        return "preprocessor/comment-bearing expression is not a stable binding"
    if re.match(r"\s*#", assignment.rhs):
        return "intra-assignment delay is not legal inside a bound SVA expression"
    if re.search(r"\b(?:function|task|force|release)\b", assignment.rhs):
        return "unsupported procedural expression"
    # A loop/genvar name embedded in an index is not visible from a module bind.
    # Reject it generically instead of relying on a library-specific name.
    for name in referenced | guard:
        signal = design.module_signals[assignment.module].get(name)
        if signal and signal.kind in {"integer", "genvar"}:
            return f"generate/procedural index {name!r} is not bind-visible"
    return ""


def _is_reset_guard(guard: str, reset: str, active_low: bool = True) -> bool:
    if reset not in expression_signals(guard):
        return False
    compact = re.sub(r"\s+", "", guard)
    escaped = re.escape(reset)
    zero = r"(?:1'[bBdDhH]0|0)(?![A-Za-z0-9_$'])"
    one = r"(?:1'[bBdDhH]1|1)(?![A-Za-z0-9_$'])"
    if active_low:
        # A negated equality is the deasserted branch even though the reset
        # comparison still occurs textually inside the guard.
        if re.search(rf"!\(+(?:[!~]{escaped}|{escaped}={{2,3}}{zero})\)+", compact):
            return False
        return bool(re.search(
            rf"(?<![!~])(?:!|~){escaped}\b|{escaped}={{2,3}}{zero}|{zero}={{2,3}}{escaped}",
            compact,
        ))
    if re.search(rf"!\(+{escaped}={{2,3}}{one}\)+", compact):
        return False
    if re.search(rf"{escaped}={{2,3}}{one}|{one}={{2,3}}{escaped}", compact):
        return True
    if re.search(rf"{escaped}={{2,3}}{zero}|{zero}={{2,3}}{escaped}|(?:!|~){escaped}\b", compact):
        return False
    return bool(re.search(rf"(?<![!~A-Za-z0-9_$]){escaped}(?![A-Za-z0-9_$])", compact))


def _one_bit_alias(assignment: Any, design: RTLDesign) -> bool:
    match = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_$]*)\s*", assignment.rhs)
    if not match:
        return False
    signals = design.module_signals.get(assignment.module, {})
    left, right = signals.get(assignment.lhs), signals.get(match.group(1))
    return bool(left and right and not left.width and not right.width)


def _boolean_constant(expression: str) -> int | None:
    compact = re.sub(r"[\s()]", "", expression or "").lower()
    if compact in {"0", "1'b0", "1'd0", "1'h0", "'0"}:
        return 0
    if compact in {"1", "1'b1", "1'd1", "1'h1", "'1"}:
        return 1
    return None


def _region_index(regions_doc: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    by_id = {item["region_id"]: item for item in regions_doc.get("regions", [])}
    by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for region in regions_doc.get("regions", []):
        by_module[region["module"]].append(region)
    return by_id, by_module


def _best_region(
    assignment: Any,
    by_module: dict[str, list[dict[str, Any]]],
    graph_assignment_id: str | None,
) -> dict[str, Any]:
    regions = by_module.get(assignment.module, [])
    wanted_node = graph_assignment_id or ""
    related = [
        region for region in regions
        if wanted_node in region.get("coi", {}).get("node_ids", [])
        or assignment.lhs in region.get("seed_signals", [])
    ]
    if not related:
        related = [region for region in regions if region.get("kind") == "MODULE"]
    kind_priority = {"FSM": 5, "HANDSHAKE": 4, "PIPELINE_VALID_FLOW": 3, "ALWAYS_BLOCK_CLUSTER": 2, "MODULE": 1}
    return max(
        related or [{"region_id": f"region_module_{_safe_id(assignment.module)}", "kind": "MODULE", "score": 0}],
        key=lambda item: (kind_priority.get(item.get("kind", ""), 0), item.get("score", 0)),
    )


def _edge_index(design_map: dict[str, Any]) -> dict[tuple[str, str], list[dict[str, Any]]]:
    result: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for edge in design_map.get("cross_module_dependencies", []):
        for endpoint in (edge["source"], edge["target"]):
            result[(endpoint["module"], endpoint["signal"])].append(edge)
    return result


def _graph_indexes(graph: dict[str, Any]) -> tuple[dict[tuple[str, str, int, str], str], Counter[str]]:
    assignment_ids: dict[tuple[str, str, int, str], str] = {}
    for item in graph.get("assignments", []):
        source = item.get("source", {})
        assignment_ids[(item.get("module", ""), source.get("file", ""), int(source.get("line", 0)), item.get("lhs", ""))] = item["id"]
    degree: Counter[str] = Counter()
    for edge in graph.get("edges", []):
        degree[edge.get("source", "")] += 1
        degree[edge.get("target", "")] += 1
    return assignment_ids, degree


def _primitive_rule(
    assignment: Any, design: RTLDesign, reset: str, reset_active_low: bool = True,
) -> tuple[str, dict[str, Any], str]:
    if assignment.kind == "nonblocking" and _is_reset_guard(
        assignment.guard, reset, reset_active_low
    ):
        return "RESET", {
            "RESET": assignment.guard,
            "TARGET": assignment.lhs,
            "VALUE": assignment.rhs,
        }, "reset value"
    lhs_role = expression_role(assignment.lhs, design, assignment.module)
    rhs_role = expression_role(assignment.rhs, design, assignment.module)
    boolean_value = _boolean_constant(assignment.rhs)
    if (
        assignment.kind == "nonblocking"
        and lhs_role.get("width") == 1
        and boolean_value is not None
    ):
        primitive = "CONTROL_ASSERT" if boolean_value else "CONTROL_DEASSERT"
        return primitive, {
            "CONDITION": assignment.guard or "1'b1",
            "TARGET": assignment.lhs,
            "DELAY": 1,
        }, "guarded control assertion" if boolean_value else "guarded control deassertion"
    if (
        assignment.kind == "nonblocking"
        and lhs_role.get("width") == 1
        and rhs_role.get("width") == 1
        and lhs_role.get("role") in {"predicate", "event", "control"}
        and rhs_role.get("role") in {"predicate", "event", "control"}
    ):
        return "CAUSALITY", {
            "CAUSE": assignment.rhs,
            "EFFECT": assignment.lhs,
            "DELAY": 1,
        }, "next-cycle control propagation"
    if assignment.kind == "nonblocking":
        return "UPDATE", {
            "CONDITION": assignment.guard or "1'b1",
            "TARGET": assignment.lhs,
            "VALUE": assignment.rhs,
            "DELAY": 1,
        }, "guarded register update"
    if _one_bit_alias(assignment, design) or (
        lhs_role.get("width") == 1
        and rhs_role.get("width") == 1
        and lhs_role.get("role") in {"predicate", "event", "control"}
        and rhs_role.get("role") in {"predicate", "event", "control"}
    ):
        return "CAUSALITY", {
            "CAUSE": assignment.rhs,
            "EFFECT": assignment.lhs,
            "DELAY": 0,
        }, "same-cycle control propagation"
    return "DATA_INTEGRITY", {
        "CONDITION": assignment.guard or "1'b1",
        "SOURCE": assignment.rhs,
        "TARGET": assignment.lhs,
        "DELAY": 0,
    }, "same-cycle data/control transformation"


def _primitive_applicability_rejection(
    assignment: Any, design: RTLDesign, primitive: str
) -> str:
    """Mirror the fixed primitive's type gate before spending selection budget."""

    if primitive != "DATA_INTEGRITY":
        return ""
    for role_name, expression in (("SOURCE", assignment.rhs), ("TARGET", assignment.lhs)):
        inferred = expression_role(expression, design, assignment.module)
        if inferred.get("status") != "DETERMINISTIC":
            return (
                f"{role_name} semantic role/width remains ambiguous and deterministic-first "
                "selection does not spend the initial Formal budget on it"
            )
        if inferred.get("width") == 1 and inferred.get("role") in {"predicate", "event", "control"}:
            return (
                f"{role_name} is a one-bit predicate/control value and is not applicable to "
                "the fixed DATA_INTEGRITY primitive"
            )
    return ""


def _make_contract(
    candidate_id: str,
    module: str,
    region_id: str,
    primitive: str,
    roles: dict[str, Any],
    scope: str,
    semantics: str,
    evidence: list[dict[str, Any]],
    provenance: str,
) -> ContractIR:
    fields: dict[str, list[dict[str, Any]]] = {name: [] for name in RULE_FIELD.values()}
    rule = {
        "primitive": primitive,
        "roles": roles,
        "semantics": semantics,
        "confidence": 1.0,
        "region_flow_scope": scope,
        "provenance": provenance,
        "planner_candidate_id": candidate_id,
    }
    fields[RULE_FIELD[primitive]] = [rule]
    return ContractIR(
        contract_id=f"contract_coverage_closure_{candidate_id}",
        object_type="INITIAL_PROPERTY_BOOTSTRAP",
        ontology_classification="NEW_OBJECT_CANDIDATE",
        region=f"coverage_closure_{candidate_id}",
        module=module,
        evidence=evidence,
        reused_primitives=[primitive],
        **fields,
    )


def _function_description(region_kind: str, relation: str, assignment: Any, scope: str) -> str:
    subject = {
        "FSM": "state-machine behavior",
        "HANDSHAKE": "request/response handshake behavior",
        "PIPELINE_VALID_FLOW": "pipeline control propagation",
        "ALWAYS_BLOCK_CLUSTER": "register-group behavior",
        "MODULE": "module-local data/control behavior",
    }.get(region_kind, "RTL behavior")
    boundary = " across a region boundary" if scope == "CROSS_REGION" else ""
    return f"{subject}{boundary}: {assignment.lhs} {relation}"


def _candidate_from_assignment(
    assignment: Any,
    design: RTLDesign,
    region: dict[str, Any],
    graph_id: str | None,
    degree: Counter[str],
    edges: list[dict[str, Any]],
    reset: str,
    serial: int,
    reset_active_low: bool = True,
) -> BootstrapCandidate:
    primitive, roles, relation = _primitive_rule(
        assignment, design, reset, reset_active_low
    )
    edge_ids = sorted({edge["id"] for edge in edges})
    downstream = sorted({
        endpoint["module"] for edge in edges for endpoint in (edge["source"], edge["target"])
        if endpoint["module"] != assignment.module
    })
    scope = "CROSS_REGION" if edge_ids else "LOCAL"
    candidate_id = f"cand_{serial:05d}_{_safe_id(assignment.module)}_{_safe_id(assignment.lhs)}_{primitive.lower()}"
    signals = sorted(expression_signals(assignment.rhs) | expression_signals(assignment.guard) | {assignment.lhs})
    structural_scope = sorted({
        *(f"signal:{assignment.module}.{name}" for name in signals),
        *(f"cross:{edge_id}" for edge_id in edge_ids),
        f"region:{region['region_id']}",
        *([graph_id] if graph_id else []),
    })
    ownership = int(
        assignment.kind == "nonblocking" or region.get("kind") in {"FSM", "ALWAYS_BLOCK_CLUSTER"}
    )
    graph_degree = sum(degree[f"signal:{assignment.module}.{name}"] for name in signals)
    semantic = int(bool(SEMANTIC_WORDS.search(f"{assignment.lhs} {assignment.rhs}")))
    components = {
        "region_priority": float(region.get("score", 0)) / 20.0,
        "state_or_register_ownership": 5.0 * ownership,
        "fanin_fanout": min(12.0, float(graph_degree) / 2.0),
        "cross_dependencies": min(20.0, 3.0 * len(edge_ids)),
        "downstream_regions": min(10.0, 2.0 * len(downstream)),
        "semantic_hub": 6.0 * semantic,
        "family_value": {
            "RESET": 7.0, "UPDATE": 6.0, "DATA_INTEGRITY": 5.0,
            "CAUSALITY": 5.0, "CONTROL_ASSERT": 6.0,
            "CONTROL_DEASSERT": 6.0,
        }[primitive],
    }
    score = round(sum(components.values()), 3)
    semantics = (
        f"[{scope}] exact {relation} derived from {assignment.kind} assignment at "
        f"{Path(assignment.file).name}:{assignment.line}."
    )
    contract = _make_contract(
        candidate_id, assignment.module, region["region_id"], primitive, roles, scope,
        semantics, _evidence(assignment, scope, edge_ids),
        "DETERMINISTIC_INITIAL_PROPERTY_PLANNER",
    )
    return BootstrapCandidate(
        candidate_id=candidate_id,
        contract=contract,
        scope=scope,
        primitive=primitive,
        property_family=f"PRIMITIVE_{primitive}",
        region_id=region["region_id"],
        region_kind=region.get("kind", "MODULE"),
        module=assignment.module,
        function=_function_description(region.get("kind", "MODULE"), relation, assignment, scope),
        generation_reason=(
            "The fixed primitive is an exact consequence of one parsed RTL assignment; "
            "the ranking score favors its ownership, connectivity, semantic role, and boundary reach."
        ),
        rtl_relation={
            "assignment_id": graph_id,
            "lhs": assignment.lhs,
            "rhs": assignment.rhs,
            "guard": assignment.guard,
            "kind": assignment.kind,
            "file": assignment.file,
            "line": assignment.line,
        },
        cross_dependency_ids=edge_ids,
        downstream_modules=downstream,
        structural_scope=structural_scope,
        score_components=components,
        static_coverage_score=score,
    )


def _hold_candidates(
    design: RTLDesign,
    candidates: list[BootstrapCandidate],
    reset: str,
    start_serial: int,
    reset_active_low: bool = True,
) -> list[BootstrapCandidate]:
    """Expand guarded register updates with an exact no-spurious-write family."""

    grouped: dict[tuple[str, str], list[Any]] = defaultdict(list)
    for assignment in design.assignments:
        if assignment.kind == "nonblocking" and not _safety_rejection(assignment, design):
            grouped[(assignment.module, assignment.lhs)].append(assignment)
    representative = {(item.module, item.rtl_relation["lhs"]): item for item in candidates}
    result: list[BootstrapCandidate] = []
    serial = start_serial
    for key, assignments in sorted(grouped.items()):
        base = representative.get(key)
        if base is None:
            continue
        guards = sorted({
            item.guard or "1'b1" for item in assignments
            if not _is_reset_guard(item.guard, reset, reset_active_low)
        })
        if not guards or any(re.sub(r"[\s()]", "", guard).lower() in {"1'b1", "1", "true"} for guard in guards):
            continue
        condition = "!(" + " || ".join(f"({guard})" for guard in guards) + ")"
        if expression_signals(condition) - set(design.module_signals.get(key[0], {})):
            continue
        serial += 1
        candidate_id = f"cand_{serial:05d}_{_safe_id(key[0])}_{_safe_id(key[1])}_hold"
        contract = _make_contract(
            candidate_id, key[0], base.region_id, "HOLD",
            {"CONDITION": condition, "TARGET": key[1]}, base.scope,
            f"[{base.scope}] {key[1]} holds when no parsed non-reset write guard is active.",
            base.contract.evidence, "DETERMINISTIC_PROPERTY_FAMILY_EXPANSION",
        )
        result.append(BootstrapCandidate(
            candidate_id=candidate_id,
            contract=contract,
            scope=base.scope,
            primitive="HOLD",
            property_family="PRIMITIVE_HOLD",
            region_id=base.region_id,
            region_kind=base.region_kind,
            module=key[0],
            function=f"register-group behavior: {key[1]} no-spurious-write/hold",
            generation_reason=(
                "All parsed non-reset writes to the register are guarded; the complement of their "
                "union is therefore a deterministic hold condition."
            ),
            rtl_relation={"lhs": key[1], "write_guards": guards, "derived_condition": condition},
            cross_dependency_ids=base.cross_dependency_ids,
            downstream_modules=base.downstream_modules,
            structural_scope=sorted(set(base.structural_scope) | {f"family:HOLD:{key[0]}.{key[1]}"}),
            score_components={**base.score_components, "family_value": 6.0},
            static_coverage_score=round(base.static_coverage_score + 1.0, 3),
        ))
    return result


def _select(
    candidates: list[BootstrapCandidate],
    *,
    budget: int,
    cross_fraction: float,
    min_marginal_gain: int,
    per_module_cap: int,
) -> list[BootstrapCandidate]:
    selected: list[BootstrapCandidate] = []
    covered: set[str] = set()
    module_counts: Counter[str] = Counter()

    def choose(pool: list[BootstrapCandidate], limit: int) -> None:
        while pool and len(selected) < limit:
            ranked = []
            for item in pool:
                if module_counts[item.module] >= per_module_cap:
                    continue
                new_scope = set(item.structural_scope) - covered
                overlap = len(item.structural_scope) - len(new_scope)
                value = item.static_coverage_score + 2.5 * len(new_scope) - 0.75 * overlap
                ranked.append((value, len(new_scope), item.static_coverage_score, item.candidate_id, item))
            if not ranked:
                break
            _value, gain, _score, _candidate_id, best = max(ranked)
            if gain < min_marginal_gain:
                break
            best.selected = True
            best.selection_rank = len(selected) + 1
            best.estimated_marginal_gain = gain
            best.disposition = "SELECTED_FOR_INITIAL_FORMAL"
            selected.append(best)
            covered.update(best.structural_scope)
            module_counts[best.module] += 1
            pool.remove(best)

    cross_target = min(budget, ceil(budget * cross_fraction))
    choose([item for item in candidates if item.scope == "CROSS_REGION"], cross_target)
    # Treat cross_fraction as a diversity allocation, not merely a lower bound;
    # otherwise the extra boundary score can crowd every local owner property
    # out of a large hierarchical design.
    choose([item for item in candidates if item.scope == "LOCAL" and not item.selected], budget)
    if len(selected) < budget:
        choose([item for item in candidates if not item.selected], budget)
    for item in candidates:
        if item.selected:
            continue
        item.disposition = "NOT_SELECTED"
        if module_counts[item.module] >= per_module_cap:
            item.rejection_reason = "per-module diversity cap reached"
        elif len(set(item.structural_scope) - covered) < min_marginal_gain:
            item.rejection_reason = "estimated marginal structural gain below threshold"
        else:
            item.rejection_reason = "scale-derived initial property budget reached"
    return selected


def plan_initial_properties(
    design: RTLDesign,
    graph: dict[str, Any],
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    config: dict[str, Any] | None = None,
) -> tuple[list[ContractIR], dict[str, Any]]:
    """Return selected contracts and a complete, auditable candidate inventory."""

    cfg = config or {}
    reset = str(cfg.get("reset", "rst_n"))
    reset_active_low = bool(cfg.get("reset_active_low", True))
    planner_cfg = cfg.get("planner", cfg)
    by_id, regions_by_module = _region_index(regions_doc)
    edge_by_signal = _edge_index(design_map)
    assignment_ids, degree = _graph_indexes(graph)
    candidates: list[BootstrapCandidate] = []
    rejected: list[dict[str, Any]] = []
    semantic_seen: set[str] = set()
    serial = 0
    for assignment in design.assignments:
        rejection = _safety_rejection(assignment, design)
        if rejection:
            rejected.append({
                "source": _assignment_id(assignment),
                "module": assignment.module,
                "lhs": assignment.lhs,
                "disposition": "REJECTED_DURING_ENUMERATION",
                "reason": rejection,
            })
            continue
        graph_id = assignment_ids.get((assignment.module, assignment.file, assignment.line, assignment.lhs))
        region = _best_region(assignment, regions_by_module, graph_id)
        signals = expression_signals(assignment.rhs) | expression_signals(assignment.guard) | {assignment.lhs}
        edges = [edge for name in signals for edge in edge_by_signal.get((assignment.module, name), [])]
        primitive, _roles, _relation = _primitive_rule(
            assignment, design, reset, reset_active_low
        )
        applicability = _primitive_applicability_rejection(assignment, design, primitive)
        if applicability:
            rejected.append({
                "source": _assignment_id(assignment),
                "module": assignment.module,
                "lhs": assignment.lhs,
                "primitive": primitive,
                "disposition": "REJECTED_PRIMITIVE_APPLICABILITY",
                "reason": applicability,
            })
            continue
        serial += 1
        item = _candidate_from_assignment(
            assignment, design, region, graph_id, degree, edges, reset, serial,
            reset_active_low,
        )
        semantic_key = json.dumps({
            "module": item.module,
            "primitive": item.primitive,
            "roles": next(
                rule["roles"] for field in RULE_FIELD.values()
                for rule in getattr(item.contract, field)
            ),
        }, sort_keys=True)
        if semantic_key in semantic_seen:
            item.disposition = "DUPLICATE_FILTERED"
            item.rejection_reason = "identical module/primitive/role semantics already enumerated"
            rejected.append({
                "candidate_id": item.candidate_id,
                "module": item.module,
                "lhs": assignment.lhs,
                "disposition": item.disposition,
                "reason": item.rejection_reason,
            })
            continue
        semantic_seen.add(semantic_key)
        candidates.append(item)

    candidates.extend(_hold_candidates(
        design, candidates, reset, serial, reset_active_low
    ))
    node_count = max(1, int(graph.get("node_count", len(graph.get("nodes", [])))))
    computed_budget = ceil(sqrt(node_count) * float(planner_cfg.get("scale_factor", 0.95)))
    budget = min(
        int(planner_cfg.get("max_properties", 96)),
        max(int(planner_cfg.get("min_properties", 16)), computed_budget),
        len(candidates),
    )
    reachable_modules = max(1, int(design_map.get("summary", {}).get("reachable_modules", 1)))
    per_module_cap = int(planner_cfg.get("per_module_cap", max(4, ceil(budget / sqrt(reachable_modules)))))
    selected = _select(
        candidates,
        budget=budget,
        cross_fraction=float(planner_cfg.get("cross_fraction", 0.35)),
        min_marginal_gain=int(planner_cfg.get("min_marginal_gain", 2)),
        per_module_cap=per_module_cap,
    )
    selected_scope = Counter(item.scope for item in selected)
    selected_families = Counter(item.primitive for item in selected)
    selected_regions = Counter(item.region_kind for item in selected)
    all_scope = Counter(item.scope for item in candidates)
    inventory = [
        {
            **{key: value for key, value in asdict(item).items() if key != "contract"},
            "contract_id": item.contract.contract_id,
            "contract_region": item.contract.region,
        }
        for item in sorted(candidates, key=lambda value: value.candidate_id)
    ]
    plan = {
        "schema": "region_flow.1-initial-property-plan.v1",
        "strategy": "static-coverage-potential-greedy-marginal-gain",
        "strategy_parameters": {
            "scale_factor": float(planner_cfg.get("scale_factor", 0.95)),
            "computed_budget_before_limits": computed_budget,
            "selected_budget": budget,
            "min_properties": int(planner_cfg.get("min_properties", 16)),
            "max_properties": int(planner_cfg.get("max_properties", 96)),
            "cross_fraction": float(planner_cfg.get("cross_fraction", 0.35)),
            "min_marginal_gain": int(planner_cfg.get("min_marginal_gain", 2)),
            "per_module_cap": per_module_cap,
        },
        "statistics": {
            "enumerated_candidates": len(candidates) + len(rejected),
            "eligible_candidates": len(candidates),
            "selected_properties": len(selected),
            "selected_local_properties": selected_scope["LOCAL"],
            "selected_cross_region_properties": selected_scope["CROSS_REGION"],
            "eligible_local_candidates": all_scope["LOCAL"],
            "eligible_cross_region_candidates": all_scope["CROSS_REGION"],
            "rejected_candidates": len(rejected),
            "duplicate_filtered_candidates": sum(item.get("disposition") == "DUPLICATE_FILTERED" for item in rejected),
            "overlap_or_budget_filtered_candidates": sum(not item.selected for item in candidates),
            "llm_required_candidates": 0,
            "selected_property_families": dict(selected_families),
            "selected_region_kinds": dict(selected_regions),
            "selected_modules": len({item.module for item in selected}),
            "cross_dependency_edges_utilized": len({edge for item in selected for edge in item.cross_dependency_ids}),
            "estimated_structural_scope_items": len({scope for item in selected for scope in item.structural_scope}),
        },
        "selection_order": [item.candidate_id for item in selected],
        "candidates": inventory,
        "enumeration_rejections": rejected,
        "future_strategy_interface": {
            "version": 1,
            "pluggable_inputs": ["score_components", "structural_scope", "strategy_parameters"],
            "supported_selection_policy": "greedy_marginal_gain",
        },
        "region_count": len(by_id),
    }
    return [item.contract for item in selected], plan
