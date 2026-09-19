"""Generic local and cross-region Contract IR construction for Requirement 8."""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import ContractIR
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


RULE_FIELD = {
    "UPDATE": "update_rules",
    "HOLD": "hold_rules",
    "ORDERING": "ordering",
    "CAUSALITY": "causality",
    "STABILITY": "stability",
    "DATA_INTEGRITY": "data_integrity",
    "MUTUAL_EXCLUSION": "mutual_exclusion",
    "PERSISTENCE": "invariants",
    "CONTROL_ASSERT": "invariants",
    "CONTROL_DEASSERT": "invariants",
    "RESET": "reset_behavior",
}


def _safe_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_$]+", "_", value).strip("_").lower()


def _evidence(assignment: Any, scope: str) -> list[dict[str, Any]]:
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
    }]


def _safe_assignment(assignment: Any, design: RTLDesign) -> bool:
    known = set(design.module_signals.get(assignment.module, {}))
    if assignment.lhs not in known or not assignment.rhs or assignment.rhs == assignment.lhs:
        return False
    referenced = expression_signals(assignment.rhs)
    guard = expression_signals(assignment.guard)
    if not referenced or not referenced | guard <= known:
        return False
    if len(assignment.rhs) > 240 or len(assignment.guard) > 240:
        return False
    if "`" in assignment.rhs or "`" in assignment.guard:
        return False
    if re.search(r"\b(?:function|task|force|release)\b", assignment.rhs):
        return False
    return True


def _is_one_bit_alias(assignment: Any, design: RTLDesign) -> bool:
    rhs = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_$]*)\s*", assignment.rhs)
    if not rhs:
        return False
    signals = design.module_signals.get(assignment.module, {})
    left = signals.get(assignment.lhs)
    right = signals.get(rhs.group(1))
    return bool(left and right and not left.width and not right.width)


def _assignment_rule(
    assignment: Any, design: RTLDesign, scope: str, provenance: str
) -> dict[str, Any]:
    if assignment.kind == "nonblocking":
        primitive = "UPDATE"
        roles = {
            "CONDITION": assignment.guard or "1'b1",
            "TARGET": assignment.lhs,
            "VALUE": assignment.rhs,
            "DELAY": 1,
        }
    elif _is_one_bit_alias(assignment, design):
        primitive = "CAUSALITY"
        roles = {
            "CAUSE": assignment.rhs,
            "EFFECT": assignment.lhs,
            "DELAY": 0,
        }
    else:
        primitive = "DATA_INTEGRITY"
        roles = {
            "CONDITION": assignment.guard or "1'b1",
            "SOURCE": assignment.rhs,
            "TARGET": assignment.lhs,
            "DELAY": 0,
        }
    return {
        "primitive": primitive,
        "roles": roles,
        "semantics": (
            f"[{scope}] {assignment.module}.{assignment.lhs} follows its deterministic RTL "
            f"producer relation."
        ),
        "confidence": 1.0,
        "region_flow_scope": scope,
        "provenance": provenance,
    }


def _contract(region_id: str, module: str, rule: dict[str, Any], evidence: list[dict[str, Any]]) -> ContractIR:
    kwargs: dict[str, Any] = {name: [] for name in RULE_FIELD.values()}
    field = RULE_FIELD.get(rule["primitive"], "invariants")
    kwargs[field] = [rule]
    return ContractIR(
        contract_id=f"contract_req8_{_safe_id(region_id)}_{_safe_id(rule['primitive'])}",
        object_type="HIERARCHICAL_VERIFICATION_REGION",
        ontology_classification="NEW_OBJECT_CANDIDATE",
        region=region_id,
        module=module,
        evidence=evidence,
        reused_primitives=[rule["primitive"]],
        **kwargs,
    )


def deterministic_region_contracts(
    design: RTLDesign,
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    *,
    max_local: int = 8,
    max_cross: int = 6,
) -> list[ContractIR]:
    """Create exact contracts selected by graph-pattern regions.

    Signal spelling is deliberately absent from selection.  Functional motif
    score, core membership, typed cross-region edges, assignment timing and
    dependency count determine the portfolio.
    """

    module_region = {
        item["module"]: item["region_id"]
        for item in regions_doc["regions"] if item["kind"] == "MODULE"
    }
    boundary_by_module: dict[str, dict[str, set[str]]] = defaultdict(lambda: defaultdict(set))
    for edge in design_map.get("cross_module_dependencies", []):
        boundary_by_module[edge["source"]["module"]][edge["source"]["signal"]].add(
            edge["target"]["module"]
        )
        boundary_by_module[edge["target"]["module"]][edge["target"]["signal"]].add(
            edge["source"]["module"]
        )

    indexed = {f"assignment:{index}": item for index, item in enumerate(design.assignments, start=1)}
    safe_ids = {
        assignment_id for assignment_id, item in indexed.items()
        if item.module in module_region and _safe_assignment(item, design)
    }
    kind_priority = {
        "DECODE": 6, "FSM": 5, "HANDSHAKE": 4, "PIPELINE": 3,
        "DATAPATH": 2, "REGISTER_UPDATE": 1,
    }
    pattern_regions = [
        item for item in regions_doc.get("regions", [])
        if item.get("kind") in kind_priority and item.get("detection_status") in {"MATCH", "LLM_VALIDATED"}
    ]
    assignment_regions: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for region in pattern_regions:
        core = set(region.get("core_node_ids", []))
        for node in region.get("coi", {}).get("nodes", []):
            assignment_id = str(node.get("id", ""))
            if assignment_id in safe_ids:
                assignment_regions[assignment_id].append({
                    "region_id": region["region_id"],
                    "kind": region["kind"],
                    "pattern_score": float(region.get("score", 0.0)),
                    "core_assignment": assignment_id in core,
                })

    cross_assignment_ids: dict[str, tuple[str, str]] = {}
    for edge in regions_doc.get("cross_region_semantic_edges", []):
        for node_key in ("source_node", "target_node"):
            assignment_id = str(edge.get(node_key, ""))
            if assignment_id in safe_ids:
                cross_assignment_ids.setdefault(
                    assignment_id,
                    (str(edge.get("source_region", "")), str(edge.get("target_region", ""))),
                )

    # Cross-module boundary paths remain valid cross-region evidence, but no
    # interface-name tokens influence their ranking.
    for assignment_id in safe_ids:
        assignment = indexed[assignment_id]
        boundary = boundary_by_module[assignment.module]
        if assignment.lhs not in boundary:
            continue
        rhs_boundary = [item for item in assignment.dependencies if item in boundary]
        if any(boundary[assignment.lhs] != boundary[item] for item in rhs_boundary):
            cross_assignment_ids.setdefault(
                assignment_id,
                (module_region[assignment.module], module_region[assignment.module]),
            )

    for assignment_id in cross_assignment_ids:
        if assignment_id not in assignment_regions:
            assignment = indexed[assignment_id]
            assignment_regions[assignment_id].append({
                "region_id": module_region[assignment.module],
                "kind": "DATAPATH",
                "pattern_score": 0.45,
                "core_assignment": False,
            })

    def structural_score(assignment_id: str) -> tuple[Any, ...]:
        assignment = indexed[assignment_id]
        owners = assignment_regions.get(assignment_id, [])
        best = max(owners, key=lambda item: (
            item["core_assignment"], kind_priority[item["kind"]], item["pattern_score"]
        ), default={"core_assignment": False, "kind": "REGISTER_UPDATE", "pattern_score": 0.0})
        return (
            -int(best["core_assignment"]), -kind_priority[best["kind"]],
            -float(best["pattern_score"]), -int(bool(assignment.guard)),
            -len(assignment.dependencies), assignment.module, assignment.line,
        )

    cross_limit = min(max_cross, max(0, len(assignment_regions) - 1))
    selected_cross_ids = sorted(
        (item for item in cross_assignment_ids if item in assignment_regions),
        key=structural_score,
    )[:cross_limit]
    selected_keys = set(selected_cross_ids)
    selected_local_ids = sorted(
        (item for item in assignment_regions if item not in selected_keys),
        key=structural_score,
    )[:max_local]
    contracts = []
    for scope, assignment_ids in (("LOCAL", selected_local_ids), ("CROSS_REGION", selected_cross_ids)):
        for index, assignment_id in enumerate(assignment_ids, start=1):
            assignment = indexed[assignment_id]
            owners = sorted(
                assignment_regions[assignment_id],
                key=lambda item: (-int(item["core_assignment"]), -kind_priority[item["kind"]], -item["pattern_score"]),
            )
            owner = owners[0]["region_id"] if owners else module_region[assignment.module]
            if scope == "CROSS_REGION" and assignment_id in cross_assignment_ids:
                left, right = cross_assignment_ids[assignment_id]
                region = f"{left}__to__{right}_{index}"
            else:
                region = f"{owner}_{scope.lower()}_{index}"
            contracts.append(_contract(
                region,
                assignment.module,
                _assignment_rule(assignment, design, scope, "GRAPH_PATTERN_TYPED_DIRECTED_EDGE"),
                _evidence(assignment, scope),
            ))
    return contracts


def llm_response_contracts(
    responses: list[dict[str, Any]],
    region_by_id: dict[str, dict[str, Any]],
) -> list[ContractIR]:
    contracts = []
    counters: dict[str, int] = defaultdict(int)
    for response in responses:
        if response.get("status") != "COMPLETE":
            continue
        region = region_by_id[response["region_id"]]
        for proposal in response.get("contracts", []):
            primitive = str(proposal["primitive"]).upper()
            scope = proposal["scope"]
            counters[response["region_id"]] += 1
            rule = {
                "primitive": primitive,
                "roles": proposal["roles"],
                "semantics": f"[{scope}] {proposal.get('semantics', '')}",
                "confidence": float(proposal["confidence"]),
                "region_flow_scope": scope,
                "provenance": "DEEPSEEK_CONTEXT_FALLBACK",
                "evidence_signals": proposal["evidence_signals"],
            }
            evidence = [{
                "files": [item["file"] for item in region["coi"].get("rtl_context", [])],
                "line_start": int(region.get("evidence", {}).get("line_start", 1) or 1),
                "line_end": int(region.get("evidence", {}).get("line_end", 1) or 1),
                "snippet": response.get("object_summary", ""),
                "region_flow_scope": scope,
            }]
            contracts.append(_contract(
                f"{response['region_id']}_llm_{counters[response['region_id']]}",
                region["module"], rule, evidence,
            ))
    return contracts


def contract_scope(contract: ContractIR) -> str:
    for field in RULE_FIELD.values():
        rules = getattr(contract, field)
        if rules:
            return str(rules[0].get("region_flow_scope", "LOCAL"))
    return "LOCAL"
