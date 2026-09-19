"""Requirement-7 deterministic grounding and Contract Static Checker."""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from copy import deepcopy
from dataclasses import asdict
import json
import re
from typing import Any

from dateassertion.ir.schema import ContractIR
from dateassertion.ontology.contracts import PRIMITIVES
from dateassertion.ontology.primitives import _compile, expression_signals
from dateassertion.pipeline.contract_validation import RULE_FIELDS, unique_rules
from dateassertion.rtl_frontend.parser import RTLDesign
from dateassertion.rtl_frontend.semantic_graph import (
    assignment_timing,
    connected_signal_cones,
    expression_role,
    expression_width,
)


STATIC_RESULTS = {
    "VALID", "TYPE_CONFLICT", "TIMING_CONFLICT", "GUARD_TOO_WEAK",
    "BOUNDARY_INCOHERENT", "UNSUPPORTED_SEMANTICS", "AMBIGUOUS",
}
PREDICATE_ROLES = {
    "UPDATE": ["CONDITION"],
    "HOLD": ["CONDITION"],
    "CAUSALITY": ["CAUSE", "EFFECT"],
    "ORDERING": ["FIRST", "SECOND"],
    "STABILITY": ["CONDITION"],
    "DATA_INTEGRITY": ["CONDITION"],
    "PERSISTENCE": ["START", "END"],
    "RESET": ["RESET"],
    "PROGRESS": ["START", "END"],
    "CONSERVATION": ["CONDITION"],
    "CONTROL_ASSERT": ["CONDITION", "TARGET"],
    "CONTROL_DEASSERT": ["CONDITION", "TARGET"],
}
OBSERVED_ROLE = {
    "UPDATE": "TARGET", "DATA_INTEGRITY": "TARGET", "RESET": "TARGET",
    "CAUSALITY": "EFFECT", "ORDERING": "SECOND",
    "CONTROL_ASSERT": "TARGET", "CONTROL_DEASSERT": "TARGET",
}
ANTECEDENT_ROLE = {
    "UPDATE": "CONDITION", "DATA_INTEGRITY": "CONDITION", "RESET": "RESET",
    "CAUSALITY": "CAUSE", "ORDERING": "FIRST",
    "CONTROL_ASSERT": "CONDITION", "CONTROL_DEASSERT": "CONDITION",
}
VALUE_ROLE = {"UPDATE": "VALUE", "DATA_INTEGRITY": "SOURCE", "RESET": "VALUE"}


def contract_to_dict(contract: ContractIR) -> dict[str, Any]:
    return asdict(contract)


def _roles(rule: dict[str, Any]) -> dict[str, Any]:
    roles = rule.get("roles", {})
    return roles if isinstance(roles, dict) else {}


def _normalize(text: Any, design: RTLDesign) -> str:
    if not isinstance(text, str):
        return str(text)
    result = text
    for name, value in sorted(design.macros.items(), key=lambda item: -len(item[0])):
        result = re.sub(rf"`{re.escape(name)}\b", f"({value})", result)
    result = result.replace("==?", "==").replace("!=?", "!=")
    result = re.sub(r"\s+", "", result)
    while result.startswith("(") and result.endswith(")"):
        depth = 0
        balanced = True
        for index, character in enumerate(result):
            depth += character == "("
            depth -= character == ")"
            if depth == 0 and index != len(result) - 1:
                balanced = False
                break
        if not balanced:
            break
        result = result[1:-1]
    return result.lower()


def _boolean_constant(text: Any, design: RTLDesign) -> int | None:
    compact = _normalize(text, design)
    if compact in {"0", "1'b0", "1'd0", "1'h0", "'0"}:
        return 0
    if compact in {"1", "1'b1", "1'd1", "1'h1", "'1"}:
        return 1
    return None


def _base_signal(expression: Any) -> str | None:
    if not isinstance(expression, str):
        return None
    match = re.fullmatch(r"\s*([A-Za-z_][A-Za-z0-9_$]*)\s*", expression)
    return match.group(1) if match else None


def _target_signal(expression: Any) -> str | None:
    if not isinstance(expression, str):
        return None
    match = re.match(r"\s*([A-Za-z_][A-Za-z0-9_$]*)", expression)
    return match.group(1) if match else None


def _matching_assignments(
    rule: dict[str, Any], module: str, design: RTLDesign, graph: dict[str, Any]
) -> list[dict[str, Any]]:
    primitive = str(rule.get("primitive", "")).upper()
    roles = _roles(rule)
    target = _target_signal(roles.get(OBSERVED_ROLE.get(primitive, "")))
    if not target:
        return []
    path = rule.get("semantic_path_assignments")
    if isinstance(path, list) and 1 < len(path) <= 2:
        graph_assignments = graph.get("assignments", [])
        exact: list[dict[str, Any]] = []
        for edge in path:
            if not isinstance(edge, dict) or edge.get("module") != module:
                return []
            match = next((
                item for item in graph_assignments
                if item.get("module") == module
                and item.get("lhs") == edge.get("lhs")
                and _normalize(item.get("rhs", ""), design) == _normalize(edge.get("rhs", ""), design)
                and (not edge.get("assignment_id") or item.get("id") == edge.get("assignment_id"))
            ), None)
            if match is None:
                return []
            exact.append(match)
        if any(
            str(exact[index].get("lhs", "")) not in expression_signals(str(exact[index + 1].get("rhs", "")))
            for index in range(len(exact) - 1)
        ):
            return []
        source_name = "SOURCE" if primitive == "DATA_INTEGRITY" else (
            "CAUSE" if primitive == "CAUSALITY" else "FIRST"
        )
        observed_name = OBSERVED_ROLE.get(primitive, "")
        source = roles.get(source_name)
        observed = _target_signal(roles.get(observed_name))
        if (
            _normalize(source, design) != _normalize(exact[0].get("rhs", ""), design)
            or observed != exact[-1].get("lhs")
        ):
            return []
        sequential_edges = sum(item.get("timing") == "next_cycle" for item in exact)
        if sequential_edges > 1:
            return []
        return [{
            "id": "semantic_path:" + "->".join(str(item.get("id", "")) for item in exact),
            "module": module,
            "lhs": observed,
            "rhs": source,
            "guard": "1'b1",
            "assignment_kind": "semantic_path",
            "timing": "next_cycle" if sequential_edges else "same_cycle",
            "file": exact[-1].get("source", {}).get("file"),
            "line": exact[-1].get("source", {}).get("line"),
            "semantic_path_assignments": exact,
        }]
    candidates = [
        item for item in graph.get("assignments", [])
        if item.get("module") == module and item.get("lhs") == target
    ]
    value = roles.get(VALUE_ROLE.get(primitive, ""))
    if primitive == "CONTROL_ASSERT":
        value = "1'b1"
    elif primitive == "CONTROL_DEASSERT":
        value = "1'b0"
    if value is None and primitive in {"CAUSALITY", "ORDERING"}:
        observed = roles.get(OBSERVED_ROLE[primitive])
        if isinstance(observed, str):
            comparison = re.fullmatch(
                rf"\s*{re.escape(target)}\s*==\s*(.+?)\s*", observed
            )
            if comparison:
                value = comparison.group(1)
        antecedent = roles.get(ANTECEDENT_ROLE[primitive], "")
        antecedent_signals = expression_signals(str(antecedent))
        if (
            primitive == "CAUSALITY"
            and _boolean_constant(antecedent, design) == 1
            and value is not None
        ):
            return [
                item for item in candidates
                if _normalize(item.get("rhs", ""), design)
                == _normalize(value, design)
            ]
        scored: list[tuple[int, dict[str, Any]]] = []
        for item in candidates:
            path_signals = expression_signals(str(item.get("guard", ""))) | expression_signals(str(item.get("rhs", "")))
            overlap = len(antecedent_signals & path_signals)
            exact_value = int(value is not None and _normalize(item.get("rhs", ""), design) == _normalize(value, design))
            scored.append((10 * overlap + exact_value, item))
        best = max((score for score, _item in scored), default=0)
        # No direct syntactic overlap means the causal relation needs alias or
        # semantic reasoning (for example inst_i -> opcode -> branch).  Do not
        # invent an exact guard in that case.
        if best < 10:
            return []
        return [item for score, item in scored if score == best]
    if value is None:
        return candidates
    if primitive in {"CONTROL_ASSERT", "CONTROL_DEASSERT"}:
        wanted_boolean = 1 if primitive == "CONTROL_ASSERT" else 0
        return [
            item for item in candidates
            if _boolean_constant(item.get("rhs", ""), design) == wanted_boolean
        ]
    wanted = _normalize(value, design)
    exact = [item for item in candidates if _normalize(item.get("rhs", ""), design) == wanted]
    if exact:
        return exact
    # A source slice or a harmless parenthesized form may be embedded in a
    # larger cast/extension.  Keep these as ambiguous evidence, not proof.
    containing = [item for item in candidates if wanted and wanted in _normalize(item.get("rhs", ""), design)]
    return containing


def _required_guard(assignments: list[dict[str, Any]]) -> str | None:
    guards = list(dict.fromkeys(item.get("guard") or "1'b1" for item in assignments))
    if not guards:
        return None
    if len(guards) == 1:
        return guards[0]
    return " || ".join(f"({guard})" for guard in guards)


def _guard_covers(proposed: Any, required: str | None, design: RTLDesign) -> bool:
    if required is None:
        return False
    if _normalize(required, design) in {"1'b1", "1", "true"}:
        return True
    proposed_n = _normalize(proposed, design)
    required_n = _normalize(required, design)
    return bool(proposed_n) and (proposed_n == required_n or required_n in proposed_n)


def _expected_delay(timing: str) -> int | None:
    if timing == "same_cycle":
        return 0
    if timing == "next_cycle":
        return 1
    return None


def _graph_path(graph: dict[str, Any], module: str, sources: set[str], targets: set[str]) -> bool:
    if sources & targets:
        return True
    prefix = f"signal:{module}."
    adjacency: dict[str, set[str]] = defaultdict(set)
    for edge in graph.get("edges", []):
        if edge.get("type") not in {"DATA", "CONTROL", "SEQUENTIAL"}:
            continue
        left, right = edge.get("source", ""), edge.get("target", "")
        adjacency[left].add(right)
    queue = deque(prefix + item for item in sources)
    seen = set(queue)
    wanted = {prefix + item for item in targets}
    while queue:
        current = queue.popleft()
        if current in wanted:
            return True
        for neighbor in adjacency.get(current, set()):
            if neighbor not in seen:
                seen.add(neighbor)
                queue.append(neighbor)
    return False


def assess_boundary(contract: ContractIR, graph: dict[str, Any]) -> dict[str, Any]:
    records, _ = unique_rules(contract)
    referenced: set[str] = set()
    disconnected_relations: list[str] = []
    for record in records:
        rule = record["rule"]
        roles = _roles(rule)
        primitive = str(rule.get("primitive", "")).upper()
        values = [item for item in roles.values() if isinstance(item, str)]
        values += [entry for item in roles.values() if isinstance(item, list) for entry in item if isinstance(entry, str)]
        for value in values:
            referenced.update(expression_signals(value))
        if primitive in {"CAUSALITY", "ORDERING"}:
            first = roles.get("CAUSE" if primitive == "CAUSALITY" else "FIRST", "")
            second = roles.get("EFFECT" if primitive == "CAUSALITY" else "SECOND", "")
            first_signals = expression_signals(str(first))
            literal_true_cause = (
                primitive == "CAUSALITY"
                and not first_signals
                and re.sub(r"[\s()]", "", str(first)).lower() in {"1", "1'b1", "true"}
            )
            if not literal_true_cause and not _graph_path(
                graph, contract.module, first_signals,
                expression_signals(str(second)),
            ):
                disconnected_relations.append(record["rule_id"])
    cones = connected_signal_cones(graph, contract.module, referenced)
    if disconnected_relations:
        status = "BOUNDARY_INCOHERENT"
        reason = "a causal/ordering rule crosses disconnected RTL dependence cones"
    elif len(cones) <= 1:
        status = "BOUNDARY_COHERENT"
        reason = "all referenced signals occupy one deterministic control/data cone"
    else:
        status = "AMBIGUOUS"
        reason = "the object contains several independent rule-local cones; Req7 expands and gates them per rule"
    return {
        "status": status,
        "reason": reason,
        "referenced_signals": sorted(referenced),
        "control_data_cones": cones,
        "disconnected_relations": disconnected_relations,
        "expansion_mode": "REJECT" if status == "BOUNDARY_INCOHERENT" else "RULE_LEVEL",
    }


def _type_findings(rule: dict[str, Any], module: str, design: RTLDesign) -> list[dict[str, Any]]:
    primitive = str(rule.get("primitive", "")).upper()
    roles = _roles(rule)
    findings: list[dict[str, Any]] = []
    for role_name in PREDICATE_ROLES.get(primitive, []):
        value = roles.get(role_name)
        if value is None and primitive in {"DATA_INTEGRITY", "CONSERVATION"} and role_name == "CONDITION":
            continue
        inferred = expression_role(value, design, module)
        if inferred.get("role") not in {"predicate", "event", "control"} or inferred.get("width") not in {1, None}:
            findings.append({
                "category": "TYPE_CONFLICT",
                "field": role_name,
                "reason": f"{primitive}.{role_name} must be predicate/event/control, got {inferred.get('role')} width={inferred.get('width')}",
                "evidence": inferred,
            })
    if primitive == "MUTUAL_EXCLUSION":
        for operand in roles.get("SIGNALS", []) if isinstance(roles.get("SIGNALS"), list) else []:
            inferred = expression_role(operand, design, module)
            if inferred.get("width") != 1:
                findings.append({
                    "category": "TYPE_CONFLICT", "field": "SIGNALS",
                    "reason": f"MUTUAL_EXCLUSION operand {operand!r} is not a one-bit event/predicate",
                    "evidence": inferred,
                })
    if primitive in {"UPDATE", "DATA_INTEGRITY"}:
        left_name, right_name = (("TARGET", "VALUE") if primitive == "UPDATE" else ("TARGET", "SOURCE"))
        left_width = expression_width(roles.get(left_name), design, module)
        right_width = expression_width(roles.get(right_name), design, module)
        if left_width is not None and right_width is not None and left_width != right_width:
            findings.append({
                "category": "TYPE_CONFLICT", "field": f"{left_name}/{right_name}",
                "reason": f"width mismatch: {left_width} versus {right_width}",
                "evidence": {left_name: left_width, right_name: right_width},
            })
        for role_name in (left_name, right_name):
            inferred = expression_role(roles.get(role_name), design, module)
            if inferred.get("role") in {"predicate", "event", "control"} and inferred.get("width") == 1:
                findings.append({
                    "category": "TYPE_CONFLICT", "field": role_name,
                    "reason": f"{primitive}.{role_name} requires state/data/address/payload semantics",
                    "evidence": inferred,
                })
    return findings


def check_rule(
    rule: dict[str, Any], module: str, design: RTLDesign, graph: dict[str, Any],
    *, boundary: dict[str, Any] | None = None,
) -> dict[str, Any]:
    primitive = str(rule.get("primitive", "")).upper()
    roles = _roles(rule)
    findings: list[dict[str, Any]] = []
    deterministic: dict[str, Any] = {"role": {}, "timing": None, "guard": None, "primitive_applicability": None}
    if primitive not in PRIMITIVES:
        findings.append({"category": "UNSUPPORTED_SEMANTICS", "field": "primitive", "reason": f"unknown primitive {primitive!r}", "evidence": {}})
    elif _compile(primitive, rule) is None:
        findings.append({"category": "UNSUPPORTED_SEMANTICS", "field": "roles", "reason": "primitive roles do not satisfy the fixed compiler signature", "evidence": roles})
    findings.extend(_type_findings(rule, module, design))
    for name, value in roles.items():
        if name in {"DELAY", "MAX_DELAY"}:
            continue
        values = value if isinstance(value, list) else [value]
        deterministic["role"][name] = [expression_role(item, design, module) for item in values]

    assignments = _matching_assignments(rule, module, design, graph)
    observed_name = OBSERVED_ROLE.get(primitive)
    if observed_name:
        target = _target_signal(roles.get(observed_name))
        if target:
            if assignments:
                timings = {item.get("timing", "unknown") for item in assignments}
                inferred_timing = next(iter(timings)) if len(timings) == 1 else "variable_latency"
                deterministic["timing"] = {"value": inferred_timing, "status": "DETERMINISTIC" if len(timings) == 1 else "AMBIGUOUS", "evidence": assignments}
                expected = _expected_delay(inferred_timing)
                if primitive in {
                    "UPDATE", "DATA_INTEGRITY", "CAUSALITY", "ORDERING",
                    "CONTROL_ASSERT", "CONTROL_DEASSERT",
                } and expected is not None:
                    actual = roles.get("DELAY", 1 if primitive == "UPDATE" else 0)
                    if str(actual) != str(expected):
                        findings.append({
                            "category": "TIMING_CONFLICT", "field": "DELAY",
                            "reason": f"DELAY={actual} conflicts with deterministic {inferred_timing} assignment",
                            "evidence": assignments,
                            "deterministic_value": expected,
                        })
            elif primitive in {
                "UPDATE", "DATA_INTEGRITY", "RESET",
                "CONTROL_ASSERT", "CONTROL_DEASSERT",
            }:
                findings.append({
                    "category": "UNSUPPORTED_SEMANTICS", "field": observed_name,
                    "reason": "no RTL assignment matches the proposed target/value relation",
                    "evidence": {"target": target, "value": roles.get(VALUE_ROLE.get(primitive, ""))},
                })

    # CAUSALITY/ORDERING assignments reach this point only when the antecedent
    # directly overlaps one best-scoring RTL path.  This avoids matching an
    # unrelated branch merely because it writes the same literal value.
    if primitive in {
        "UPDATE", "DATA_INTEGRITY", "RESET", "CAUSALITY", "ORDERING",
        "CONTROL_ASSERT", "CONTROL_DEASSERT",
    } and assignments:
        required = _required_guard(assignments)
        proposed_name = ANTECEDENT_ROLE[primitive]
        proposed = roles.get(proposed_name, "1'b1")
        covered = _guard_covers(proposed, required, design)
        deterministic["guard"] = {
            "status": "DETERMINISTIC",
            "required_path_condition": required,
            "proposed_guard": proposed,
            "compatible": covered,
            "evidence": [{key: item.get(key) for key in ("file", "line", "lhs", "rhs", "guard")} for item in assignments],
        }
        if not covered:
            findings.append({
                "category": "GUARD_TOO_WEAK", "field": proposed_name,
                "reason": "contract antecedent does not include the assignment's complete if/case/priority path condition",
                "evidence": deterministic["guard"],
                "deterministic_value": required,
            })

    semantic_ambiguity: dict[str, Any] | None = None
    if primitive == "MUTUAL_EXCLUSION" and not findings:
        semantic_ambiguity = {
            "field": "SIGNALS",
            "reason": "all operands are type-compatible predicates, but syntactic RTL analysis alone cannot prove they are mutually exclusive",
            "evidence": roles.get("SIGNALS", []),
        }
    if primitive == "PROGRESS":
        findings.append({
            "category": "UNSUPPORTED_SEMANTICS", "field": "MAX_DELAY",
            "reason": "a bounded progress latency cannot be established from direct assignment structure",
            "evidence": {"classification": "variable_latency"},
        })
    if primitive in {"CAUSALITY", "ORDERING"}:
        first_name, second_name = (("CAUSE", "EFFECT") if primitive == "CAUSALITY" else ("FIRST", "SECOND"))
        first = roles.get(first_name, "")
        first_signals = expression_signals(str(first))
        literal_true_cause = (
            primitive == "CAUSALITY"
            and not first_signals
            and _boolean_constant(first, design) == 1
        )
        if not literal_true_cause and not _graph_path(
            graph, module, first_signals,
            expression_signals(str(roles.get(second_name, ""))),
        ):
            findings.append({
                "category": "BOUNDARY_INCOHERENT", "field": f"{first_name}/{second_name}",
                "reason": "no RTL DATA/SEQUENTIAL dependence path connects the proposed relation",
                "evidence": {first_name: roles.get(first_name), second_name: roles.get(second_name)},
            })

    priority = ["TYPE_CONFLICT", "TIMING_CONFLICT", "GUARD_TOO_WEAK", "BOUNDARY_INCOHERENT", "UNSUPPORTED_SEMANTICS"]
    result = next((name for name in priority if any(item["category"] == name for item in findings)), "AMBIGUOUS" if semantic_ambiguity else "VALID")
    deterministic["primitive_applicability"] = {
        "status": "DETERMINISTIC",
        "value": result if result != "GUARD_TOO_WEAK" and result != "TIMING_CONFLICT" else "VALID_AFTER_GROUNDING",
        "signature_checked": primitive in PRIMITIVES,
        "semantic_ambiguity": semantic_ambiguity,
    }
    return {
        "result": result,
        "primitive": primitive,
        "findings": findings,
        "deterministic_facts": deterministic,
    }


def apply_deterministic_refinement(rule: dict[str, Any], check: dict[str, Any]) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    grounded = deepcopy(rule)
    roles = grounded.setdefault("roles", {})
    changes: list[dict[str, Any]] = []
    for finding in check.get("findings", []):
        category = finding.get("category")
        field = finding.get("field")
        if category == "TIMING_CONFLICT" and field == "DELAY":
            before = roles.get("DELAY")
            after = finding.get("deterministic_value")
            roles["DELAY"] = after
            changes.append({"field": "DELAY", "before": before, "after": after, "reason": category})
        elif category == "GUARD_TOO_WEAK" and isinstance(field, str):
            required = finding.get("deterministic_value")
            before = roles.get(field, "1'b1")
            before_simple = re.sub(r"[\s()]", "", str(before)).lower()
            after = required if before_simple in {"1'b1", "1", "true"} else f"({before}) && ({required})"
            roles[field] = after
            changes.append({"field": field, "before": before, "after": after, "reason": category})
    return grounded, changes


def ground_contracts(
    contracts: list[ContractIR], design: RTLDesign, graph: dict[str, Any], *, auto_refine: bool = True,
) -> tuple[list[ContractIR], dict[str, Any], dict[str, Any]]:
    grounded_contracts: list[ContractIR] = []
    object_results: list[dict[str, Any]] = []
    metrics = {name: Counter() for name in ("boundary", "role", "timing", "guard", "primitive_applicability")}
    for contract in contracts:
        grounded = deepcopy(contract)
        boundary = assess_boundary(contract, graph)
        metrics["boundary"]["total"] += 1
        metrics["boundary"]["deterministic" if boundary["status"] != "AMBIGUOUS" else "llm_required"] += 1
        records, duplicates = unique_rules(contract)
        checks: list[dict[str, Any]] = []
        replacement_by_field: dict[str, list[dict[str, Any]]] = defaultdict(list)
        for record in records:
            original_check = check_rule(record["rule"], contract.module, design, graph, boundary=boundary)
            grounded_rule, changes = apply_deterministic_refinement(record["rule"], original_check) if auto_refine else (deepcopy(record["rule"]), [])
            final_check = check_rule(grounded_rule, contract.module, design, graph, boundary=boundary)
            if auto_refine and original_check["result"] in {"TIMING_CONFLICT", "GUARD_TOO_WEAK"} and final_check["result"] == "VALID":
                disposition = "REFINED_VALID"
                replacement_by_field[record["contract_field"]].append(grounded_rule)
            elif final_check["result"] == "VALID":
                disposition = "VALID"
                replacement_by_field[record["contract_field"]].append(grounded_rule)
            elif final_check["result"] == "AMBIGUOUS":
                disposition = "LLM_REQUIRED"
                replacement_by_field[record["contract_field"]].append(grounded_rule)
            else:
                disposition = "REJECTED_PRE_FORMAL"
            facts = final_check["deterministic_facts"]
            for values in facts["role"].values():
                for value in values:
                    metrics["role"]["total"] += 1
                    metrics["role"]["deterministic" if value.get("status") == "DETERMINISTIC" else "llm_required"] += 1
            for field_name in ("timing", "guard"):
                if facts.get(field_name) is not None:
                    metrics[field_name]["total"] += 1
                    metrics[field_name]["deterministic" if facts[field_name].get("status") == "DETERMINISTIC" else "llm_required"] += 1
            metrics["primitive_applicability"]["total"] += 1
            metrics["primitive_applicability"]["llm_required" if final_check["result"] == "AMBIGUOUS" else "deterministic"] += 1
            checks.append({
                "rule_id": record["rule_id"],
                "contract_field": record["contract_field"],
                "original_rule": record["rule"],
                "grounded_rule": grounded_rule,
                "initial_result": original_check["result"],
                "final_result": final_check["result"],
                "disposition": disposition,
                "deterministic_changes": changes,
                "findings": original_check["findings"],
                "grounded_facts": facts,
            })
        for field in RULE_FIELDS:
            setattr(grounded, field, replacement_by_field.get(field, []))
        grounded_contracts.append(grounded)
        object_results.append({
            "object_id": contract.region,
            "module": contract.module,
            "boundary": boundary,
            "rules": checks,
            "duplicates": duplicates,
        })

    totals = Counter()
    per_field: dict[str, Any] = {}
    for name, values in metrics.items():
        total = values["total"]
        deterministic = values["deterministic"]
        llm_required = values["llm_required"]
        totals.update({"total": total, "deterministic": deterministic, "llm_required": llm_required})
        per_field[name] = {
            "deterministic": deterministic,
            "total": total,
            "llm_required": llm_required,
            "rate": round(deterministic / total, 6) if total else None,
        }
    rate = round(totals["deterministic"] / totals["total"], 6) if totals["total"] else 0.0
    grounding_metrics = {
        "definition": "deterministically resolved grounding fields / all grounding fields",
        "deterministic": totals["deterministic"],
        "total": totals["total"],
        "llm_required_fields": totals["llm_required"],
        "rate": rate,
        "percent": round(rate * 100, 2),
        "by_field": per_field,
    }
    static_results = {
        "schema": "grounding_flow-static-check.v1",
        "objects": object_results,
        "summary": {
            "contracts_processed": len(contracts),
            "rules_processed": sum(len(item["rules"]) for item in object_results),
            "initial_results": dict(Counter(rule["initial_result"] for item in object_results for rule in item["rules"])),
            "final_results": dict(Counter(rule["final_result"] for item in object_results for rule in item["rules"])),
            "dispositions": dict(Counter(rule["disposition"] for item in object_results for rule in item["rules"])),
            "pre_formal_rejected": sum(rule["disposition"] == "REJECTED_PRE_FORMAL" for item in object_results for rule in item["rules"]),
            "deterministically_refined": sum(rule["disposition"] == "REFINED_VALID" for item in object_results for rule in item["rules"]),
        },
    }
    return grounded_contracts, static_results, grounding_metrics
