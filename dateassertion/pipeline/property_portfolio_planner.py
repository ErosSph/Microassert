"""Requirement 8.2 obligation-aware property portfolio planner.

This module deliberately remains design agnostic.  It starts from the exact
assignment relations used by Requirement 8.1, adds evidence-backed obligation
variants and bounded semantic paths, estimates proof/vacuity risk, and selects
properties by marginal value relative to the portfolio already selected.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from copy import deepcopy
from dataclasses import asdict, dataclass
from math import ceil, log2, sqrt
from pathlib import Path
import json
import re
from typing import Any

from dateassertion.ir.schema import ContractIR
from dateassertion.ontology.primitives import expression_signals
from dateassertion.pipeline.initial_property_planner import (
    BootstrapCandidate,
    _best_region,
    _candidate_from_assignment,
    _edge_index,
    _graph_indexes,
    _hold_candidates,
    _is_reset_guard,
    _make_contract,
    _primitive_applicability_rejection,
    _region_index,
    _safe_id,
    _safety_rejection,
)
from dateassertion.pipeline.contract_grounding import ground_contracts
from dateassertion.rtl_frontend.parser import RTLDesign
from dateassertion.rtl_frontend.semantic_graph import expression_role


TRUE_EXPRESSIONS = {"1", "1'b1", "true"}
REJECTION_CODES = {
    "unresolved": "INSUFFICIENT_EVIDENCE",
    "type": "TYPE_CONFLICT",
    "width": "TYPE_CONFLICT",
    "delay": "TIMING_CONFLICT",
    "duplicate": "DUPLICATE_OBLIGATION",
    "expression": "INSUFFICIENT_EVIDENCE",
}


@dataclass
class PortfolioCandidate:
    candidate_id: str
    contract: ContractIR
    module: str
    region_id: str
    region_kind: str
    scope: str
    primitive: str
    property_family: str
    obligation: str
    functional_meaning: str
    generation_reason: str
    rtl_evidence: list[dict[str, Any]]
    rtl_relation: dict[str, Any]
    dependency_ids: list[str]
    semantic_path: list[dict[str, Any]]
    structural_scope: list[str]
    score_components: dict[str, float]
    static_coverage_score: float
    proofability_score: float
    proofability_reasons: list[str]
    vacuity_risk: float
    vacuity_risk_reasons: list[str]
    historical_gap_items: int = 0


def _truthy(expression: str) -> bool:
    compact = re.sub(r"[\s()]", "", expression or "").lower()
    # The parser uses an empty guard for an unconditional assignment.
    return not compact or compact in TRUE_EXPRESSIONS


def _reason_code(reason: str, default: str = "INSUFFICIENT_EVIDENCE") -> str:
    lower = reason.lower()
    return next((code for token, code in REJECTION_CODES.items() if token in lower), default)


def _clone_contract(contract: ContractIR, candidate_id: str) -> ContractIR:
    result = deepcopy(contract)
    result.contract_id = f"contract_candidate_planning_{candidate_id}"
    result.region = f"candidate_planning_{candidate_id}"
    for field in (
        "invariants", "update_rules", "hold_rules", "ordering", "causality",
        "stability", "data_integrity", "mutual_exclusion", "reset_behavior",
    ):
        for rule in getattr(result, field):
            rule["planner_candidate_id"] = candidate_id
            rule["provenance"] = str(rule.get("provenance", "")).replace("REQ8_1", "REQ8_2")
    return result


def _instance_counts(design_map: dict[str, Any]) -> Counter[str]:
    return Counter(item["module"] for item in design_map.get("instances", []))


def _operator_complexity(*expressions: str) -> int:
    return sum(len(re.findall(r"&&|\|\||==|!=|<=|>=|[?:+*/%&|^<>]", item or "")) for item in expressions)


def _risk_scores(
    primitive: str,
    relation: dict[str, Any],
    structural_scope: list[str],
    semantic_path: list[dict[str, Any]],
    instance_count: int,
) -> tuple[float, list[str], float, list[str]]:
    rhs = str(relation.get("rhs", relation.get("source_expression", "")))
    guard = str(relation.get("guard", relation.get("condition", "1'b1")))
    complexity = _operator_complexity(rhs, guard)
    proofability = 0.96
    proof_reasons = ["exact fixed-template RTL relation"]
    if complexity > 3:
        proofability -= min(0.28, 0.035 * (complexity - 3))
        proof_reasons.append(f"expression complexity={complexity}")
    if len(expression_signals(rhs) | expression_signals(guard)) > 8:
        proofability -= 0.12
        proof_reasons.append("wide structural cone")
    if len(semantic_path) > 2:
        proofability -= 0.08 * (len(semantic_path) - 2)
        proof_reasons.append(f"semantic path length={len(semantic_path)}")
    if primitive in {"PROGRESS", "ORDERING"}:
        proofability -= 0.18
        proof_reasons.append("temporal relation has elevated proof risk")
    if instance_count > 1:
        proofability -= min(0.28, 0.04 * log2(instance_count))
        proof_reasons.append(f"must hold in {instance_count} elaborated instances")
    proofability = round(max(0.05, min(1.0, proofability)), 3)

    antecedent = guard
    if primitive == "CAUSALITY":
        antecedent = str(relation.get("cause", rhs))
    elif primitive == "PERSISTENCE":
        antecedent = str(relation.get("persistence_antecedent", relation.get("lhs", "")))
    vacuity = 0.04 if _truthy(antecedent) else 0.10
    vacuity_reasons = ["unconditional relation" if _truthy(antecedent) else "event/guard antecedent"]
    conjunctions = len(re.findall(r"&&|\|\|", antecedent))
    vacuity += min(0.45, conjunctions * 0.08)
    if conjunctions:
        vacuity_reasons.append(f"compound antecedent terms={conjunctions + 1}")
    if re.search(r"state|exception|irq|flush|error|overflow", antecedent, re.I):
        vacuity += 0.10
        vacuity_reasons.append("potentially rare state/event trigger")
    if len(expression_signals(antecedent)) > 5:
        vacuity += 0.10
        vacuity_reasons.append("large trigger cone")
    return proofability, proof_reasons, round(min(1.0, vacuity), 3), vacuity_reasons


def _obligation(item: BootstrapCandidate) -> str:
    if item.primitive == "RESET":
        return "RESET"
    if item.primitive == "HOLD":
        return "NO_SPURIOUS_WRITE"
    if item.primitive == "UPDATE":
        return "REGISTER_UPDATE"
    if item.primitive == "DATA_INTEGRITY":
        return "DATAFLOW_INTEGRITY"
    if item.primitive == "PERSISTENCE":
        return "HANDSHAKE_PERSISTENCE"
    if item.primitive == "CONTROL_ASSERT":
        return "CONTROL_ASSERTION"
    if item.primitive == "CONTROL_DEASSERT":
        return "CONTROL_DEASSERTION"
    if item.region_kind == "HANDSHAKE":
        return "REQUEST_CAUSALITY"
    return "CONTROL_PROPAGATION"


def _historical_gap_index(items: list[Any] | None) -> Counter[tuple[str, int]]:
    result: Counter[tuple[str, int]] = Counter()
    for item in items or []:
        if getattr(item, "status", "") == "covered_and_checked":
            continue
        file = str(getattr(item, "file", ""))
        start = int(getattr(item, "line_start", 0))
        end = int(getattr(item, "line_end", start))
        for line in range(start, end + 1):
            result[(file, line)] += 1
    return result


def _adapt(
    base: BootstrapCandidate,
    candidate_id: str,
    instances: Counter[str],
    historical_gap: Counter[tuple[str, int]],
) -> PortfolioCandidate:
    contract = _clone_contract(base.contract, candidate_id)
    relation = dict(base.rtl_relation)
    evidence = deepcopy(contract.evidence)
    gap = sum(
        historical_gap[(str(file), line)]
        for item in evidence
        for file in item.get("files", [])
        for line in range(int(item.get("line_start", 0)), int(item.get("line_end", 0)) + 1)
    )
    proof, proof_reasons, vacuity, vacuity_reasons = _risk_scores(
        base.primitive, relation, base.structural_scope, [], instances[base.module]
    )
    components = {
        "coverage_closure_static_value": round(min(30.0, base.static_coverage_score / 2.0), 3),
        "hub_importance": round(min(20.0, base.score_components.get("fanin_fanout", 0.0) + base.score_components.get("cross_dependencies", 0.0) / 2.0), 3),
        "proofability": round(22.0 * proof, 3),
        "vacuity_safety": round(12.0 * (1.0 - vacuity), 3),
        "historical_gap_potential": round(min(12.0, 1.5 * gap), 3),
        "obligation_value": 9.0,
        "instance_reuse_penalty": round(-min(14.0, 2.0 * log2(max(1, instances[base.module]))), 3),
    }
    return PortfolioCandidate(
        candidate_id=candidate_id,
        contract=contract,
        module=base.module,
        region_id=base.region_id,
        region_kind=base.region_kind,
        scope=base.scope,
        primitive=base.primitive,
        property_family=base.property_family,
        obligation=_obligation(base),
        functional_meaning=base.function,
        generation_reason=base.generation_reason,
        rtl_evidence=evidence,
        rtl_relation=relation,
        dependency_ids=list(base.cross_dependency_ids),
        semantic_path=[],
        structural_scope=list(base.structural_scope) + [f"obligation:{base.region_id}:{_obligation(base)}"],
        score_components=components,
        static_coverage_score=round(sum(components.values()), 3),
        proofability_score=proof,
        proofability_reasons=proof_reasons,
        vacuity_risk=vacuity,
        vacuity_risk_reasons=vacuity_reasons,
        historical_gap_items=gap,
    )


def _enumerate_direct(
    design: RTLDesign,
    graph: dict[str, Any],
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    reset: str,
    reset_active_low: bool,
) -> tuple[list[BootstrapCandidate], list[dict[str, Any]]]:
    _by_id, regions_by_module = _region_index(regions_doc)
    edge_by_signal = _edge_index(design_map)
    assignment_ids, degree = _graph_indexes(graph)
    candidates: list[BootstrapCandidate] = []
    rejected: list[dict[str, Any]] = []
    seen: set[str] = set()
    serial = 0
    for assignment in design.assignments:
        rejection = _safety_rejection(assignment, design)
        # Req8.1 conservatively discarded constant RHS updates.  They are exact
        # and useful when a real guard supplies the functional evidence.
        rhs_signals = expression_signals(assignment.rhs)
        guard_signals = expression_signals(assignment.guard)
        allow_guarded_constant = (
            rejection == "constant-only relation is reserved for RESET family expansion"
            and assignment.kind == "nonblocking" and not rhs_signals and bool(guard_signals)
        )
        if rejection and not allow_guarded_constant:
            rejected.append({
                "candidate_id": f"enumeration_{len(rejected) + 1:05d}",
                "module": assignment.module,
                "source": f"{assignment.file}:{assignment.line}:{assignment.lhs}",
                "disposition": "NOT_GENERATED",
                "reason_code": _reason_code(rejection),
                "reason": rejection,
            })
            continue
        graph_id = assignment_ids.get((assignment.module, assignment.file, assignment.line, assignment.lhs))
        region = _best_region(assignment, regions_by_module, graph_id)
        signals = rhs_signals | guard_signals | {assignment.lhs}
        edges = [edge for name in signals for edge in edge_by_signal.get((assignment.module, name), [])]
        serial += 1
        base = _candidate_from_assignment(
            assignment, design, region, graph_id, degree, edges, reset, serial,
            reset_active_low,
        )
        # A guarded one-bit register update is not unconditional causality.
        # Re-express it with UPDATE so the guard remains in the antecedent.
        if base.primitive == "CAUSALITY" and assignment.kind == "nonblocking" and not _truthy(assignment.guard):
            roles = {
                "CONDITION": assignment.guard,
                "TARGET": assignment.lhs,
                "VALUE": assignment.rhs,
                "DELAY": 1,
            }
            base.primitive = "UPDATE"
            base.property_family = "PRIMITIVE_UPDATE"
            base.function = base.function.replace("next-cycle control propagation", "guarded register update")
            base.contract = _make_contract(
                base.candidate_id, base.module, base.region_id, "UPDATE", roles, base.scope,
                f"[{base.scope}] guarded register update retained with its parsed enable condition.",
                base.contract.evidence, "DETERMINISTIC_OBLIGATION_EXPANSION",
            )
        applicability = _primitive_applicability_rejection(assignment, design, base.primitive)
        if applicability:
            rejected.append({
                "candidate_id": base.candidate_id,
                "module": assignment.module,
                "source": f"{assignment.file}:{assignment.line}:{assignment.lhs}",
                "disposition": "NOT_GENERATED",
                "reason_code": _reason_code(applicability),
                "reason": applicability,
            })
            continue
        key = json.dumps({
            "module": base.module,
            "primitive": base.primitive,
            "relation": base.rtl_relation,
        }, sort_keys=True)
        if key in seen:
            rejected.append({
                "candidate_id": base.candidate_id,
                "module": assignment.module,
                "source": f"{assignment.file}:{assignment.line}:{assignment.lhs}",
                "disposition": "NOT_GENERATED",
                "reason_code": "DUPLICATE_OBLIGATION",
                "reason": "identical module/primitive/RTL relation already enumerated",
            })
            continue
        seen.add(key)
        candidates.append(base)
    candidates.extend(_hold_candidates(
        design, candidates, reset, serial, reset_active_low
    ))
    return candidates, rejected


def _boolean_literal(value: str) -> int | None:
    compact = re.sub(r"[\s()]", "", value or "").lower()
    if compact in {"0", "1'b0", "1'd0", "1'h0", "'0"}:
        return 0
    if compact in {"1", "1'b1", "1'd1", "1'h1", "'1"}:
        return 1
    return None


def _assignment_evidence(assignment: Any) -> dict[str, Any]:
    path = Path(assignment.file)
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines() if path.is_file() else []
    start = max(1, int(assignment.line) - 2)
    end = min(len(lines), int(assignment.line) + 2)
    return {
        "files": [assignment.file],
        "line_start": start,
        "line_end": end,
        "snippet": "\n".join(lines[start - 1:end]),
        "region_flow_scope": "LOCAL",
    }


def _persistence_candidates(
    direct: list[PortfolioCandidate], design: RTLDesign, graph: dict[str, Any],
    instances: Counter[str], reset: str, reset_active_low: bool,
) -> list[PortfolioCandidate]:
    """Derive lifecycle persistence from a complete one-bit write set.

    Generation requires every parsed non-reset write to be a guarded Boolean
    set or clear.  Therefore, if the bit is asserted and no clear guard is
    active, no assignment can deassert it on the following clock edge.
    """

    grouped: dict[tuple[str, str], list[Any]] = defaultdict(list)
    for assignment in design.assignments:
        if assignment.kind == "nonblocking":
            grouped[(assignment.module, assignment.lhs)].append(assignment)
    direct_by_target: dict[tuple[str, str], list[PortfolioCandidate]] = defaultdict(list)
    for item in direct:
        lhs = str(item.rtl_relation.get("lhs", ""))
        if lhs:
            direct_by_target[(item.module, lhs)].append(item)
    assignment_ids, _degree = _graph_indexes(graph)
    known_by_module = {
        module: set(signals) for module, signals in design.module_signals.items()
    }
    result: list[PortfolioCandidate] = []
    for (module, lhs), assignments in sorted(grouped.items()):
        signal = design.module_signals.get(module, {}).get(lhs)
        bases = direct_by_target.get((module, lhs), [])
        if signal is None or signal.width or not bases:
            continue
        non_reset = [
            item for item in assignments
            if not _is_reset_guard(item.guard, reset, reset_active_low)
        ]
        if len(non_reset) < 2:
            continue
        classified: list[tuple[Any, int, str]] = []
        invalid = False
        for assignment in non_reset:
            literal = _boolean_literal(assignment.rhs)
            guard = assignment.guard or "1'b1"
            graph_id = assignment_ids.get(
                (module, assignment.file, int(assignment.line), lhs)
            )
            if (
                literal is None or _truthy(guard) or not graph_id
                or expression_signals(guard) - known_by_module.get(module, set())
                or len(guard) > 240 or "`" in guard or "//" in guard
            ):
                invalid = True
                break
            classified.append((assignment, literal, graph_id))
        if invalid:
            continue
        set_items = [item for item in classified if item[1] == 1]
        clear_items = [item for item in classified if item[1] == 0]
        if not set_items or not clear_items:
            continue
        # A pure self-clear (`if (active) active <= 0`) makes the antecedent
        # false whenever the state is high.  Require an independent completion
        # or control input before spending a Formal candidate on persistence.
        if not any(
            expression_signals(item[0].guard) - {reset, lhs}
            for item in clear_items
        ):
            continue
        clear_guards = sorted({item[0].guard for item in clear_items})
        set_guards = sorted({item[0].guard for item in set_items})
        end = " || ".join(f"({guard})" for guard in clear_guards)
        antecedent = f"({lhs}) && !({end})"
        all_ids = [item[2] for item in classified]
        set_ids = [item[2] for item in set_items]
        clear_ids = [item[2] for item in clear_items]
        base = max(bases, key=lambda item: (item.static_coverage_score, item.candidate_id))
        candidate_id = f"persistence_{_safe_id(module)}_{_safe_id(lhs)}"
        evidence = [_assignment_evidence(item[0]) for item in classified]
        contract = _make_contract(
            candidate_id, module, base.region_id, "PERSISTENCE",
            {"START": lhs, "END": end}, "LOCAL",
            f"[LOCAL] {lhs} persists while none of its complete parsed clear guards is active.",
            evidence, "DETERMINISTIC_COMPLETE_WRITESET_EXPANSION",
        )
        contract = _clone_contract(contract, candidate_id)
        for rule in contract.invariants:
            rule["supporting_assignment_ids"] = all_ids
            rule["set_assignment_ids"] = set_ids
            rule["clear_assignment_ids"] = clear_ids
        relation = {
            "assignment_id": set_ids[0],
            "assignment_ids": all_ids,
            "set_assignment_ids": set_ids,
            "clear_assignment_ids": clear_ids,
            "lhs": lhs,
            "set_guards": set_guards,
            "clear_guards": clear_guards,
            "derived_end": end,
            "persistence_antecedent": antecedent,
        }
        structural = sorted(set(base.structural_scope) | set(all_ids) | {
            f"signal:{module}.{lhs}",
            f"family:PERSISTENCE:{module}.{lhs}",
            f"obligation:{base.region_id}:HANDSHAKE_PERSISTENCE",
        })
        proof, proof_reasons, vacuity, vacuity_reasons = _risk_scores(
            "PERSISTENCE", relation, structural, [], instances[module]
        )
        components = dict(base.score_components)
        components.update({
            "proofability": round(22.0 * proof, 3),
            "vacuity_safety": round(12.0 * (1.0 - vacuity), 3),
            "obligation_value": 13.0,
            "complete_writeset_value": min(8.0, float(len(all_ids))),
        })
        result.append(PortfolioCandidate(
            candidate_id=candidate_id,
            contract=contract,
            module=module,
            region_id=base.region_id,
            region_kind=base.region_kind,
            scope="LOCAL",
            primitive="PERSISTENCE",
            property_family="PRIMITIVE_PERSISTENCE",
            obligation="HANDSHAKE_PERSISTENCE",
            functional_meaning=f"one-bit lifecycle persistence for {lhs}",
            generation_reason=(
                "Every parsed non-reset write is a guarded Boolean set/clear; "
                "the union of all clear guards is the complete structural end event."
            ),
            rtl_evidence=evidence,
            rtl_relation=relation,
            dependency_ids=sorted({
                edge for item in bases for edge in item.dependency_ids
            }),
            semantic_path=[],
            structural_scope=structural,
            score_components=components,
            static_coverage_score=round(sum(components.values()), 3),
            proofability_score=proof,
            proofability_reasons=proof_reasons,
            vacuity_risk=vacuity,
            vacuity_risk_reasons=vacuity_reasons,
            historical_gap_items=max(
                (item.historical_gap_items for item in bases), default=0
            ),
        ))
    return result


def _complement_candidates(
    direct: list[PortfolioCandidate], design: RTLDesign, instances: Counter[str]
) -> list[PortfolioCandidate]:
    result: list[PortfolioCandidate] = []
    for base in direct:
        relation = base.rtl_relation
        rhs = str(relation.get("rhs", "")).strip()
        lhs = str(relation.get("lhs", "")).strip()
        if (
            base.primitive != "CAUSALITY" or not rhs or not lhs
            or not _truthy(str(relation.get("guard", "1'b1")))
            or len(rhs) > 260 or "`" in rhs or "//" in rhs
            or expression_signals(rhs) - set(design.module_signals.get(base.module, {}))
        ):
            continue
        target = design.module_signals.get(base.module, {}).get(lhs)
        rhs_role = expression_role(rhs, design, base.module)
        if (
            not target or target.width
            or rhs_role.get("status") != "DETERMINISTIC"
            or rhs_role.get("width") != 1
        ):
            continue
        candidate_id = f"{base.candidate_id}_deassertion"
        roles = {
            "CAUSE": f"!({rhs})", "EFFECT": f"!({lhs})",
            "DELAY": 1 if relation.get("kind") == "nonblocking" else 0,
        }
        contract = _make_contract(
            candidate_id, base.module, base.region_id, "CAUSALITY", roles, base.scope,
            f"[{base.scope}] false value of exact one-bit expression {rhs} propagates to deassertion of {lhs}.",
            deepcopy(base.rtl_evidence), "DETERMINISTIC_OBLIGATION_COMPLEMENT",
        )
        contract = _clone_contract(contract, candidate_id)
        structural = sorted(set(base.structural_scope) | {f"obligation:{base.region_id}:CONTROL_DEASSERTION"})
        proof, proof_reasons, vacuity, vacuity_reasons = _risk_scores(
            "CAUSALITY", {**relation, "cause": roles["CAUSE"]}, structural, [], instances[base.module]
        )
        components = dict(base.score_components)
        components["obligation_value"] = 8.0
        components["complement_expansion_adjustment"] = -3.0
        result.append(PortfolioCandidate(
            candidate_id, contract, base.module, base.region_id, base.region_kind, base.scope,
            "CAUSALITY", "PRIMITIVE_CAUSALITY", "CONTROL_DEASSERTION",
            f"{base.functional_meaning}; deassertion behavior",
            "The exact parsed one-bit assignment proves both asserted and deasserted propagation; this candidate covers the complementary control obligation.",
            deepcopy(base.rtl_evidence), {**relation, "cause": roles["CAUSE"], "effect": roles["EFFECT"]},
            list(base.dependency_ids), [], structural, components, round(sum(components.values()), 3),
            proof, proof_reasons, vacuity, vacuity_reasons, base.historical_gap_items,
        ))
    return result


def _exact_boolean_relation_candidates(
    direct: list[PortfolioCandidate], design: RTLDesign, instances: Counter[str]
) -> list[PortfolioCandidate]:
    """Preserve an exact one-bit assignment as one unconditional equality.

    The direct CAUSALITY candidate and its complement separately encode the
    true and false halves of the same parsed assignment.  Their event
    antecedents can be difficult to cover in a large integrated CPU even when
    the assignment equality itself is immediate.  A CAUSALITY obligation with
    a literal true cause expresses the complete relation without inventing behavior
    and has no semantic vacuity question.
    """

    result: list[PortfolioCandidate] = []
    write_counts = Counter(
        (assignment.module, assignment.lhs) for assignment in design.assignments
    )
    for base in direct:
        relation = base.rtl_relation
        rhs = str(relation.get("rhs", "")).strip()
        lhs = str(relation.get("lhs", "")).strip()
        if (
            base.primitive != "CAUSALITY" or not rhs or not lhs
            or relation.get("kind") != "continuous"
            or write_counts[(base.module, lhs)] != 1
            or not _truthy(str(relation.get("guard", "1'b1")))
            or len(rhs) > 260 or "`" in rhs or "//" in rhs
            or expression_signals(rhs) - set(design.module_signals.get(base.module, {}))
        ):
            continue
        target = design.module_signals.get(base.module, {}).get(lhs)
        rhs_role = expression_role(rhs, design, base.module)
        if (
            not target or target.width
            or rhs_role.get("status") != "DETERMINISTIC"
            or rhs_role.get("width") != 1
        ):
            continue
        delay = 1 if relation.get("kind") == "nonblocking" else 0
        candidate_id = f"{base.candidate_id}_exact_relation"
        effect = f"{lhs} == ({rhs})"
        roles = {"CAUSE": "1'b1", "EFFECT": effect, "DELAY": delay}
        contract = _make_contract(
            candidate_id, base.module, base.region_id, "CAUSALITY", roles, base.scope,
            f"[{base.scope}] exact one-bit assignment {lhs} equals {rhs} with its parsed timing.",
            deepcopy(base.rtl_evidence), "DETERMINISTIC_EXACT_RELATION_EXPANSION",
        )
        contract = _clone_contract(contract, candidate_id)
        structural = sorted(
            set(base.structural_scope)
            | {f"obligation:{base.region_id}:EXACT_CONTROL_RELATION"}
        )
        exact_relation = {
            **relation, "cause": "1'b1", "effect": effect,
        }
        proof, proof_reasons, vacuity, vacuity_reasons = _risk_scores(
            "CAUSALITY", exact_relation, structural, [], instances[base.module]
        )
        components = dict(base.score_components)
        components["obligation_value"] = 10.0
        components["exact_relation_expansion_adjustment"] = 1.0
        result.append(PortfolioCandidate(
            candidate_id, contract, base.module, base.region_id, base.region_kind,
            base.scope, "CAUSALITY", "PRIMITIVE_CAUSALITY", "EXACT_CONTROL_RELATION",
            f"{base.functional_meaning}; complete asserted/deasserted equality",
            "The parsed deterministic one-bit assignment is retained as one complete equality with a literal true antecedent.",
            deepcopy(base.rtl_evidence), exact_relation,
            list(base.dependency_ids), [], structural, components,
            round(sum(components.values()), 3), proof, proof_reasons,
            vacuity, vacuity_reasons, base.historical_gap_items,
        ))
    return result


def _semantic_path_candidates(
    direct: list[PortfolioCandidate], design: RTLDesign, instances: Counter[str]
) -> list[PortfolioCandidate]:
    """Compose only exact, acyclic paths of at most two assignment edges."""

    producers: dict[tuple[str, str], list[PortfolioCandidate]] = defaultdict(list)
    for item in direct:
        lhs = str(item.rtl_relation.get("lhs", ""))
        if lhs:
            producers[(item.module, lhs)].append(item)
    result: list[PortfolioCandidate] = []
    for tail in direct:
        relation = tail.rtl_relation
        mid_match = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_$]*)\s*", str(relation.get("rhs", "")))
        if not mid_match or not _truthy(str(relation.get("guard", "1'b1"))):
            continue
        heads = producers.get((tail.module, mid_match.group(1)), [])
        if len(heads) != 1:
            continue
        head = heads[0]
        if head.candidate_id == tail.candidate_id:
            continue
        head_relation = head.rtl_relation
        if not _truthy(str(head_relation.get("guard", "1'b1"))):
            continue
        kinds = (head_relation.get("kind"), relation.get("kind"))
        if kinds == ("nonblocking", "nonblocking") or relation.get("kind") == "nonblocking":
            continue
        delay = 1 if head_relation.get("kind") == "nonblocking" else 0
        source_expr = str(head_relation.get("rhs", ""))
        target = str(relation.get("lhs", ""))
        if not source_expr or target in expression_signals(source_expr):
            continue
        target_info = design.module_signals.get(tail.module, {}).get(target)
        source_names = expression_signals(source_expr)
        source_infos = [design.module_signals.get(tail.module, {}).get(name) for name in source_names]
        boolean_path = bool(target_info and not target_info.width and source_infos and all(item and not item.width for item in source_infos))
        primitive = "CAUSALITY" if boolean_path else "DATA_INTEGRITY"
        roles = (
            {"CAUSE": source_expr, "EFFECT": target, "DELAY": delay}
            if primitive == "CAUSALITY"
            else {"CONDITION": "1'b1", "SOURCE": source_expr, "TARGET": target, "DELAY": delay}
        )
        region_path = [head.region_id, tail.region_id]
        # A path must cross either verification-region or hierarchical boundary;
        # purely local duplicates remain represented by their direct relations.
        dependency_ids = sorted(set(head.dependency_ids) | set(tail.dependency_ids))
        if head.region_id == tail.region_id and not dependency_ids:
            continue
        candidate_id = f"path_{_safe_id(tail.module)}_{_safe_id(mid_match.group(1))}_{_safe_id(target)}_{delay}"
        evidence = deepcopy(head.rtl_evidence) + deepcopy(tail.rtl_evidence)
        contract = _make_contract(
            candidate_id, tail.module, tail.region_id, primitive, roles, "CROSS_REGION",
            f"[CROSS_REGION] bounded semantic path {source_expr} -> {mid_match.group(1)} -> {target}.",
            evidence, "DETERMINISTIC_SHORT_SEMANTIC_PATH",
        )
        contract = _clone_contract(contract, candidate_id)
        path_assignments = [
            {
                "assignment_id": head_relation.get("assignment_id"),
                "module": head.module,
                "lhs": head_relation.get("lhs"),
                "rhs": head_relation.get("rhs"),
                "guard": head_relation.get("guard") or "1'b1",
                "kind": head_relation.get("kind"),
                "file": head_relation.get("file"),
                "line": head_relation.get("line"),
            },
            {
                "assignment_id": relation.get("assignment_id"),
                "module": tail.module,
                "lhs": relation.get("lhs"),
                "rhs": relation.get("rhs"),
                "guard": relation.get("guard") or "1'b1",
                "kind": relation.get("kind"),
                "file": relation.get("file"),
                "line": relation.get("line"),
            },
        ]
        for field in ("causality", "data_integrity"):
            for rule in getattr(contract, field):
                rule["semantic_path_assignments"] = deepcopy(path_assignments)
                rule["semantic_path_max_edges"] = 2
        path = [
            {"candidate_id": head.candidate_id, "region_id": head.region_id, "signal": mid_match.group(1)},
            {"candidate_id": tail.candidate_id, "region_id": tail.region_id, "signal": target},
        ]
        structural = sorted(set(head.structural_scope) | set(tail.structural_scope) | {
            f"semantic_path:{head.region_id}->{tail.region_id}",
            f"obligation:{tail.region_id}:CROSS_REGION_DATAFLOW",
        })
        path_relation = {
            "source_expression": source_expr, "intermediate": mid_match.group(1), "lhs": target,
            "condition": "1'b1", "delay": delay, "region_path": region_path,
        }
        proof, proof_reasons, vacuity, vacuity_reasons = _risk_scores(
            primitive, path_relation, structural, path, instances[tail.module]
        )
        components = {
            "coverage_closure_static_value": round(min(30.0, (head.static_coverage_score + tail.static_coverage_score) / 4.0), 3),
            "hub_importance": round(min(20.0, (len(head.dependency_ids) + len(tail.dependency_ids)) * 1.5), 3),
            "proofability": round(22.0 * proof, 3),
            "vacuity_safety": round(12.0 * (1.0 - vacuity), 3),
            "historical_gap_potential": round(min(12.0, 1.5 * (head.historical_gap_items + tail.historical_gap_items)), 3),
            "obligation_value": 13.0,
            "semantic_path_value": 8.0,
            "instance_reuse_penalty": round(-min(14.0, 2.0 * log2(max(1, instances[tail.module]))), 3),
        }
        result.append(PortfolioCandidate(
            candidate_id, contract, tail.module, tail.region_id, tail.region_kind, "CROSS_REGION",
            primitive, f"PRIMITIVE_{primitive}", "CROSS_REGION_DATAFLOW",
            f"bounded control/data propagation through {mid_match.group(1)} into {target}",
            "Two exact parsed assignment edges form a bounded semantic path; no symbolic execution or inferred latency is used.",
            evidence, path_relation, dependency_ids, path, structural, components,
            round(sum(components.values()), 3), proof, proof_reasons, vacuity, vacuity_reasons,
            head.historical_gap_items + tail.historical_gap_items,
        ))
    unique: dict[str, PortfolioCandidate] = {}
    for item in result:
        unique.setdefault(item.candidate_id, item)
    return list(unique.values())


def _marginal_select(
    candidates: list[PortfolioCandidate], *, max_properties: int, min_utility: float,
    force_budget: bool,
) -> tuple[list[PortfolioCandidate], dict[str, dict[str, Any]], str]:
    selected: list[PortfolioCandidate] = []
    remaining = list(candidates)
    covered: set[str] = set()
    obligation_counts: Counter[tuple[str, str]] = Counter()
    global_obligation_counts: Counter[str] = Counter()
    region_counts: Counter[str] = Counter()
    module_counts: Counter[str] = Counter()
    family_counts: Counter[str] = Counter()
    scope_counts: Counter[str] = Counter()
    audit: dict[str, dict[str, Any]] = {}
    stop_reason = "MAX_PROPERTIES_REACHED"
    while remaining and len(selected) < max_properties:
        ranked: list[tuple[float, float, str, PortfolioCandidate, dict[str, Any]]] = []
        for item in remaining:
            scope = set(item.structural_scope)
            new_scope = scope - covered
            max_overlap = max(
                (len(scope & set(other.structural_scope)) / max(1, len(scope | set(other.structural_scope))) for other in selected),
                default=0.0,
            )
            obligation_novelty = 1.0 / (1 + obligation_counts[(item.region_id, item.obligation)])
            region_novelty = 1.0 / (1 + region_counts[item.region_id])
            family_novelty = 1.0 / (1 + family_counts[item.primitive])
            marginal = {
                "base_static_value": item.static_coverage_score,
                "new_structural_scope": min(28.0, 2.5 * len(new_scope)),
                "obligation_novelty": 18.0 * obligation_novelty,
                "obligation_diversity": 12.0 / (1 + global_obligation_counts[item.obligation]),
                "region_completion": 8.0 if region_counts[item.region_id] and obligation_counts[(item.region_id, item.obligation)] == 0 else 0.0,
                "region_novelty": 8.0 * region_novelty,
                "family_diversity": 12.0 * family_novelty,
                "scope_diversity": 8.0 / (1 + scope_counts[item.scope]),
                "cross_region_value": 6.0 if item.scope == "CROSS_REGION" else 0.0,
                "semantic_path_value": 5.0 if item.semantic_path else 0.0,
                "overlap_penalty": -22.0 * max_overlap,
                "region_saturation_penalty": -2.5 * region_counts[item.region_id],
                "module_saturation_penalty": -0.8 * module_counts[item.module],
            }
            utility = round(sum(marginal.values()), 3)
            ranked.append((utility, item.proofability_score, item.candidate_id, item, marginal))
        utility, _proof, _candidate_id, best, marginal = max(ranked)
        if not force_budget and utility < min_utility:
            stop_reason = "LOW_MARGINAL_GAIN"
            break
        rank = len(selected) + 1
        audit[best.candidate_id] = {
            "selected": True, "selection_rank": rank, "marginal_utility": utility,
            "marginal_components": {key: round(value, 3) for key, value in marginal.items()},
            "new_structural_scope_items": len(set(best.structural_scope) - covered),
            "selection_reason": "highest marginal portfolio utility at this selection step",
        }
        selected.append(best)
        covered.update(best.structural_scope)
        obligation_counts[(best.region_id, best.obligation)] += 1
        global_obligation_counts[best.obligation] += 1
        region_counts[best.region_id] += 1
        module_counts[best.module] += 1
        family_counts[best.primitive] += 1
        scope_counts[best.scope] += 1
        remaining.remove(best)
    for item in remaining:
        scope = set(item.structural_scope)
        overlap = max(
            (len(scope & set(other.structural_scope)) / max(1, len(scope | set(other.structural_scope))) for other in selected),
            default=0.0,
        )
        if overlap >= 0.80:
            code = "HIGH_OVERLAP"
        elif item.proofability_score < 0.45:
            code = "LOW_PROOFABILITY"
        elif item.vacuity_risk > 0.65:
            code = "HIGH_VACUITY_RISK"
        elif stop_reason == "LOW_MARGINAL_GAIN":
            code = "LOW_MARGINAL_GAIN"
        else:
            code = "BUDGET_FILTERED"
        audit[item.candidate_id] = {
            "selected": False, "selection_rank": None, "marginal_utility": None,
            "marginal_components": {}, "new_structural_scope_items": len(scope - covered),
            "selection_reason": code,
        }
    return selected, audit, stop_reason


def _inventory(
    candidates: list[PortfolioCandidate], audit: dict[str, dict[str, Any]], experiment: str,
) -> list[dict[str, Any]]:
    result = []
    for item in sorted(candidates, key=lambda value: value.candidate_id):
        payload = {key: value for key, value in asdict(item).items() if key != "contract"}
        payload.update(audit[item.candidate_id])
        payload.update({
            "experiment": experiment,
            "contract_id": item.contract.contract_id,
            "contract_region": item.contract.region,
        })
        result.append(payload)
    return result


def _statistics(
    candidates: list[PortfolioCandidate], selected: list[PortfolioCandidate], stop_reason: str,
) -> dict[str, Any]:
    return {
        "eligible_candidates": len(candidates),
        "selected_properties": len(selected),
        "selected_local_properties": sum(item.scope == "LOCAL" for item in selected),
        "selected_cross_region_properties": sum(item.scope == "CROSS_REGION" for item in selected),
        "selected_semantic_path_properties": sum(bool(item.semantic_path) for item in selected),
        "selected_modules": len({item.module for item in selected}),
        "selected_regions": len({item.region_id for item in selected}),
        "selected_obligations": len({(item.region_id, item.obligation) for item in selected}),
        "selected_families": dict(Counter(item.primitive for item in selected)),
        "selected_obligation_distribution": dict(Counter(item.obligation for item in selected)),
        "cross_dependency_edges_utilized": len({edge for item in selected for edge in item.dependency_ids}),
        "mean_proofability": round(sum(item.proofability_score for item in selected) / len(selected), 3) if selected else 0.0,
        "mean_vacuity_risk": round(sum(item.vacuity_risk for item in selected) / len(selected), 3) if selected else 0.0,
        "structural_scope_items": len({scope for item in selected for scope in item.structural_scope}),
        "stop_reason": stop_reason,
    }


def build_property_candidate_pool(
    design: RTLDesign,
    graph: dict[str, Any],
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    config: dict[str, Any] | None = None,
    historical_coverage_items: list[Any] | None = None,
) -> tuple[list[PortfolioCandidate], list[dict[str, Any]], dict[str, Any]]:
    """Build the statically eligible Req8.2 candidate pool.

    Requirement 8.3 deliberately reuses this function so its experiment changes
    portfolio selection only.  Candidate construction, deterministic grounding,
    and the pre-Formal static gate therefore remain byte-for-byte the Req8.2
    mechanisms rather than a relaxed parallel implementation.
    """

    cfg = config or {}
    reset = str(cfg.get("reset", "rst_n"))
    reset_active_low = bool(cfg.get("reset_active_low", True))
    planner = cfg.get("planner", cfg)
    direct_base, enumeration_rejections = _enumerate_direct(
        design, graph, design_map, regions_doc, reset, reset_active_low
    )
    instances = _instance_counts(design_map)
    historical_gap = _historical_gap_index(historical_coverage_items)
    direct = [
        _adapt(item, f"cand82_{index:05d}_{_safe_id(item.module)}_{_safe_id(str(item.rtl_relation.get('lhs', item.primitive)))}_{item.primitive.lower()}", instances, historical_gap)
        for index, item in enumerate(direct_base, start=1)
    ]
    complements = _complement_candidates(direct, design, instances)
    exact_boolean_relations = _exact_boolean_relation_candidates(
        direct, design, instances,
    )
    paths = _semantic_path_candidates(direct, design, instances)
    persistence = _persistence_candidates(
        direct, design, graph, instances, reset, reset_active_low
    )
    all_candidates = direct + complements + exact_boolean_relations + paths + persistence
    # Contract/role identity is the authoritative duplicate key.
    unique: list[PortfolioCandidate] = []
    seen: set[str] = set()
    for item in all_candidates:
        rule_payload = {
            field: getattr(item.contract, field)
            for field in ("invariants", "update_rules", "hold_rules", "ordering", "causality", "stability", "data_integrity", "mutual_exclusion", "reset_behavior")
        }
        key = json.dumps({"module": item.module, "rules": rule_payload}, sort_keys=True)
        if key in seen:
            enumeration_rejections.append({
                "candidate_id": item.candidate_id, "module": item.module,
                "disposition": "NOT_GENERATED", "reason_code": "DUPLICATE_OBLIGATION",
                "reason": "identical module and fixed-template semantic roles already exist",
            })
            continue
        seen.add(key)
        unique.append(item)
    all_candidates = unique

    # Candidate quality is evaluated before ranking.  Static failures and
    # ambiguities do not consume either experiment's Formal budget.
    grounded_all, pool_static, pool_grounding = ground_contracts(
        [item.contract for item in all_candidates], design, graph
    )
    grounded_by_region = {item.region: item for item in grounded_all}
    static_by_region = {item["object_id"]: item for item in pool_static["objects"]}
    statically_eligible: list[PortfolioCandidate] = []
    for item in all_candidates:
        static = static_by_region[item.contract.region]
        dispositions = [rule["disposition"] for rule in static.get("rules", [])]
        if dispositions and all(value in {"VALID", "REFINED_VALID"} for value in dispositions):
            item.contract = grounded_by_region[item.contract.region]
            statically_eligible.append(item)
            continue
        findings = [
            finding
            for rule in static.get("rules", [])
            for finding in rule.get("findings", [])
        ]
        result_name = next(
            (rule.get("final_result") for rule in static.get("rules", []) if rule.get("final_result") != "VALID"),
            "AMBIGUOUS",
        )
        enumeration_rejections.append({
            "candidate_id": item.candidate_id,
            "module": item.module,
            "disposition": "NOT_GENERATED",
            "reason_code": (
                "TYPE_CONFLICT" if result_name == "TYPE_CONFLICT" else
                "TIMING_CONFLICT" if result_name == "TIMING_CONFLICT" else
                "GROUNDING_FAILED" if result_name != "AMBIGUOUS" else
                "INSUFFICIENT_EVIDENCE"
            ),
            "reason": "; ".join(str(value.get("reason", "")) for value in findings)
                or f"pre-selection static result {result_name}",
            "static_result": result_name,
        })
    all_candidates = statically_eligible
    pool = {
        "direct_and_family_expansion": len(direct),
        "control_complements": len(complements),
        "exact_boolean_relations": len(exact_boolean_relations),
        "short_semantic_paths": len(paths),
        "complete_writeset_persistence": len(persistence),
        "eligible": len(all_candidates),
        "not_generated": len(enumeration_rejections),
        "preselection_static_check": pool_static["summary"],
        "preselection_grounding": pool_grounding,
    }
    return all_candidates, enumeration_rejections, pool


def plan_property_portfolios(
    design: RTLDesign,
    graph: dict[str, Any],
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    config: dict[str, Any] | None = None,
    historical_coverage_items: list[Any] | None = None,
) -> dict[str, Any]:
    """Enumerate once and produce equal-budget plus dynamic Req8.2 portfolios."""

    cfg = config or {}
    planner = cfg.get("planner", cfg)
    all_candidates, enumeration_rejections, candidate_pool = build_property_candidate_pool(
        design, graph, design_map, regions_doc, config, historical_coverage_items
    )

    fixed_budget = int(planner.get("fixed_budget", 83))
    fixed_selected, fixed_audit, fixed_stop = _marginal_select(
        all_candidates, max_properties=min(fixed_budget, len(all_candidates)),
        min_utility=float("-inf"), force_budget=True,
    )
    node_count = max(1, int(graph.get("node_count", len(graph.get("nodes", [])))))
    computed_dynamic_cap = ceil(
        sqrt(node_count) * float(planner.get("dynamic_scale_factor", 1.35))
    )
    dynamic_cap = min(int(planner.get("max_properties", 144)), max(fixed_budget + 1, computed_dynamic_cap), len(all_candidates))
    expanded_selected, expanded_audit, expanded_stop = _marginal_select(
        all_candidates, max_properties=dynamic_cap,
        min_utility=float(planner.get("min_marginal_utility", 34.0)), force_budget=False,
    )
    if len(expanded_selected) <= len(fixed_selected) and len(all_candidates) > len(fixed_selected):
        raise RuntimeError("dynamic portfolio did not expand beyond the equal-budget experiment")

    return {
        "schema": "region_flow.2-property-portfolio-plan.v1",
        "strategy": "hub-times-novelty-obligation-aware-marginal-portfolio",
        "strategy_parameters": {
            "fixed_budget": fixed_budget,
            "dynamic_scale_factor": float(planner.get("dynamic_scale_factor", 1.35)),
            "computed_dynamic_cap": computed_dynamic_cap,
            "dynamic_cap": dynamic_cap,
            "min_marginal_utility": float(planner.get("min_marginal_utility", 34.0)),
            "max_semantic_path_edges": 2,
            "cross_region_quota": None,
        },
        "candidate_pool": candidate_pool,
        "fixed_budget": {
            "contracts": [item.contract for item in fixed_selected],
            "selection_order": [item.candidate_id for item in fixed_selected],
            "statistics": _statistics(all_candidates, fixed_selected, fixed_stop),
            "candidates": _inventory(all_candidates, fixed_audit, "EQUAL_BUDGET"),
        },
        "expanded": {
            "contracts": [item.contract for item in expanded_selected],
            "selection_order": [item.candidate_id for item in expanded_selected],
            "statistics": _statistics(all_candidates, expanded_selected, expanded_stop),
            "candidates": _inventory(all_candidates, expanded_audit, "EXPANDED"),
        },
        "enumeration_rejections": enumeration_rejections,
        "future_strategy_interface": {
            "version": 2,
            "pluggable_inputs": [
                "static_coverage_score", "proofability_score", "vacuity_risk",
                "verification_obligation", "structural_scope", "historical_gap_items",
            ],
            "selection_policy": "set-dependent-greedy-marginal-utility",
        },
    }
