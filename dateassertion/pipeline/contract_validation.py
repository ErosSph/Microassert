"""Requirement-6.1 formal-guided validation for Extension Contracts.

This stage deliberately consumes the frozen Requirement-6 artifacts.  The LLM
may edit Contract data, but only the fixed primitive compiler can create SVA,
and an object cannot reach full expansion until its probes are proven,
non-vacuous, and structurally consistent with RTL evidence.
"""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import re
import sys
from typing import Any

import yaml

from dateassertion.formal.jaspergold import JasperGoldRunner, generate_tcl
from dateassertion.generators.sva_generator import generate_sva
from dateassertion.ir.schema import (
    ContractIR, ObjectType, PropertyIR, dump_json, load_json,
    microarchitecture_from_dict, properties_from_dict,
)
from dateassertion.ir.validation import validate_properties
from dateassertion.llm.client import DeepSeekClient, DeepSeekConfig
from dateassertion.ontology.contracts import PRIMITIVES
from dateassertion.ontology.primitives import _compile, bind_extension_primitives, expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


PROJECT_ROOT = Path(__file__).resolve().parents[1]
RULE_FIELDS = (
    "invariants", "update_rules", "hold_rules", "ordering", "causality",
    "stability", "data_integrity", "mutual_exclusion", "reset_behavior",
)
CEX_CATEGORIES = {
    "WRONG_OBJECT_BOUNDARY", "WRONG_SIGNAL_ROLE", "MISSING_GUARD",
    "WRONG_TEMPORAL_RELATION", "MISSING_ENV_ASSUMPTION", "RTL_BUG_CANDIDATE",
    "UNSUPPORTED_SEMANTICS", "NONE",
}
DISPOSITIONS = {
    "CONTRACT_ERROR", "LEGITIMATE_RTL_BEHAVIOR", "UNSUPPORTED_SEMANTICS",
    "POSSIBLE_RTL_BUG", "VALIDATED",
}
ACTIONS = {"KEEP", "PATCH", "REMOVE"}
FALSE_GUARDS = {
    "0", "1'b0", "1'd0", "1'h0", "false", "(0)", "(1'b0)",
}
PRIMITIVE_ROLES = {
    "UPDATE": {"CONDITION", "TARGET", "VALUE", "DELAY"},
    "HOLD": {"CONDITION", "TARGET"},
    "CAUSALITY": {"CAUSE", "EFFECT", "DELAY"},
    "ORDERING": {"FIRST", "SECOND", "DELAY"},
    "STABILITY": {"CONDITION", "SIGNALS"},
    "DATA_INTEGRITY": {"CONDITION", "SOURCE", "TARGET", "DELAY"},
    "MUTUAL_EXCLUSION": {"SIGNALS"},
    "PERSISTENCE": {"START", "END"},
    "CONSERVATION": {"CONDITION", "BEFORE", "AFTER"},
    "RESET": {"RESET", "TARGET", "VALUE"},
    "PROGRESS": {"START", "END", "MAX_DELAY"},
    "CONTROL_ASSERT": {"CONDITION", "TARGET", "DELAY"},
    "CONTROL_DEASSERT": {"CONDITION", "TARGET", "DELAY"},
}


class ContractValidationError(ValueError):
    """Raised when an LLM refinement cannot enter the trusted pipeline."""


def _config(path: Path) -> dict[str, Any]:
    return yaml.safe_load(path.read_text(encoding="utf-8"))


def _llm_config(raw: dict[str, Any]) -> DeepSeekConfig:
    allowed = set(DeepSeekConfig.__dataclass_fields__)
    return DeepSeekConfig(**{key: value for key, value in raw.items() if key in allowed})


def _formal_config(config: dict[str, Any]) -> dict[str, Any]:
    merged = dict(config.get("formal", {}))
    merged.update({
        "clock": config.get("clock", "clk"),
        "reset": config.get("reset", "resetn"),
        "reset_active_low": config.get("reset_active_low", True),
    })
    return merged


def contract_from_dict(raw: dict[str, Any]) -> ContractIR:
    allowed = set(ContractIR.__dataclass_fields__)
    return ContractIR(**{key: deepcopy(value) for key, value in raw.items() if key in allowed})


def _canonical_rule(rule: dict[str, Any]) -> str:
    primitive = str(rule.get("primitive", "")).upper()
    roles = deepcopy(rule.get("roles", {}))
    if isinstance(roles, dict) and "DELAY" not in roles:
        if primitive in {"UPDATE", "CONTROL_ASSERT", "CONTROL_DEASSERT"}:
            roles["DELAY"] = 1
        elif primitive in {"CAUSALITY", "ORDERING", "DATA_INTEGRITY"}:
            roles["DELAY"] = 0
    return json.dumps(
        {"primitive": primitive, "roles": roles},
        sort_keys=True,
        separators=(",", ":"),
    )


def unique_rules(contract: ContractIR) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Return stable rule records and explicitly trace semantic duplicates."""
    records: list[dict[str, Any]] = []
    duplicates: list[dict[str, Any]] = []
    seen: dict[str, str] = {}
    for field in RULE_FIELDS:
        for index, rule in enumerate(getattr(contract, field), start=1):
            rule_id = f"{contract.region}:{field}:{index}"
            canonical = _canonical_rule(rule)
            if canonical in seen:
                duplicates.append({
                    "rule_id": rule_id,
                    "duplicate_of": seen[canonical],
                    "contract_field": field,
                    "reason": "identical primitive and semantic roles",
                })
                continue
            seen[canonical] = rule_id
            records.append({
                "rule_id": rule_id,
                "contract_field": field,
                "rule": deepcopy(rule),
            })
    return records, duplicates


def _property_and_result(
    record: dict[str, Any],
    properties: list[PropertyIR],
    results: dict[str, dict[str, Any]],
) -> dict[str, Any] | None:
    rule = record["rule"]
    primitive = str(rule.get("primitive", "")).upper()
    canonical = _canonical_rule(rule)
    for prop in properties:
        if prop.template != primitive:
            continue
        if _canonical_rule({"primitive": prop.template, "roles": prop.bindings}) != canonical:
            continue
        formal = results.get(prop.property_id, {})
        return {
            "property_id": prop.property_id,
            "primitive": prop.template,
            "body": prop.body,
            "result": formal.get("result", "UNKNOWN"),
            "vacuity": formal.get("vacuity"),
            "runtime_seconds": formal.get("runtime_seconds"),
        }
    return None


def _signal_is_multibit(design: RTLDesign, module: str, expression: Any) -> bool:
    if not isinstance(expression, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", expression.strip()):
        return False
    signal = design.module_signals.get(module, {}).get(expression.strip())
    return bool(signal and signal.width)


def structural_findings(rule: dict[str, Any], module: str, design: RTLDesign) -> list[str]:
    """Reject category mistakes that formal proof alone cannot expose."""
    primitive = str(rule.get("primitive", "")).upper()
    roles = rule.get("roles", {})
    if not isinstance(roles, dict):
        return ["semantic roles are not an object"]
    findings: list[str] = []
    forbidden_operators = re.compile(r"\$(?:past|stable|onehot0?|rose|fell)\b")
    for role_name, role_value in roles.items():
        expressions = role_value if isinstance(role_value, list) else [role_value]
        if any(isinstance(item, str) and forbidden_operators.search(item) for item in expressions):
            findings.append(
                f"{role_name} embeds a temporal/system operator owned by the primitive compiler"
            )
    if primitive == "CAUSALITY":
        for role in ("CAUSE", "EFFECT"):
            if _signal_is_multibit(design, module, roles.get(role)):
                findings.append(f"{role} is a bare multi-bit data value, not a Boolean event/predicate")
    if primitive == "MUTUAL_EXCLUSION":
        signals = roles.get("SIGNALS", [])
        if isinstance(signals, list):
            for signal in signals:
                if _signal_is_multibit(design, module, signal):
                    findings.append(f"MUTUAL_EXCLUSION operand {signal!r} is a multi-bit bus")
    condition = roles.get("CONDITION")
    if isinstance(condition, str) and condition.strip().lower() in FALSE_GUARDS:
        findings.append("antecedent is a constant-false vacuity guard")
    target = roles.get("TARGET")
    delay = roles.get("DELAY")
    if primitive in {
        "UPDATE", "DATA_INTEGRITY", "CONTROL_ASSERT", "CONTROL_DEASSERT",
    } and isinstance(target, str) and delay in (0, 1, "0", "1"):
        kinds = {
            item.kind for item in design.assignments
            if item.module == module and item.lhs == target
        }
        normalized = int(delay)
        if normalized == 0 and kinds and not (kinds & {"blocking", "continuous"}):
            findings.append(f"DELAY=0 conflicts with assignment kinds {sorted(kinds)} for {target}")
        if normalized == 1 and kinds and "nonblocking" not in kinds:
            findings.append(f"DELAY=1 conflicts with assignment kinds {sorted(kinds)} for {target}")
    if primitive in {"CAUSALITY", "ORDERING"} and delay in (0, "0"):
        observed_role = "EFFECT" if primitive == "CAUSALITY" else "SECOND"
        observed = roles.get(observed_role)
        if isinstance(observed, str):
            observed_signals = expression_signals(observed)
            kinds = {
                item.kind for item in design.assignments
                if item.module == module and item.lhs in observed_signals
            }
            if kinds and kinds <= {"nonblocking"}:
                findings.append(
                    f"DELAY=0 samples {observed_role} before its nonblocking update; use next-cycle timing"
                )
    if primitive == "RESET":
        reset_expr = roles.get("RESET")
        reset_target = roles.get("TARGET")
        reset_value = roles.get("VALUE")
        if all(isinstance(item, str) for item in (reset_expr, reset_target, reset_value)):
            normalize = lambda value: re.sub(r"[\s()]", "", value)
            wanted_guard = normalize(reset_expr)
            value_assignments = [
                item for item in design.assignments
                if item.module == module and item.lhs == reset_target
                and normalize(item.rhs) == normalize(reset_value)
            ]
            if value_assignments and not any(
                wanted_guard in normalize(item.guard) for item in value_assignments
            ):
                findings.append(
                    f"RESET condition {reset_expr!r} is broader than every RTL guard assigning "
                    f"{reset_target}={reset_value}"
                )
    return findings


def _source_excerpt(path: str, line: int, radius: int = 3) -> dict[str, Any] | None:
    source = Path(path)
    if not source.is_file() or line < 1:
        return None
    lines = source.read_text(encoding="utf-8", errors="replace").splitlines()
    start = max(1, line - radius)
    end = min(len(lines), line + radius)
    return {
        "file": str(source.resolve()),
        "line_start": start,
        "line_end": end,
        "snippet": "\n".join(lines[start - 1:end]),
    }


def _rule_rtl_facts(record: dict[str, Any], contract: ContractIR, design: RTLDesign) -> dict[str, Any]:
    rule = record["rule"]
    roles = rule.get("roles", {}) if isinstance(rule.get("roles"), dict) else {}
    role_expressions: list[str] = []
    for value in roles.values():
        if isinstance(value, str):
            role_expressions.append(value)
        elif isinstance(value, list):
            role_expressions.extend(item for item in value if isinstance(item, str))
    signals = sorted(set().union(*(expression_signals(item) for item in role_expressions))) if role_expressions else []
    signal_facts = []
    module_signals = design.module_signals.get(contract.module, {})
    for name in signals:
        signal = module_signals.get(name)
        if signal:
            signal_facts.append({
                "name": name, "width": signal.width, "direction": signal.direction,
                "kind": signal.kind, "declaration_file": signal.file, "declaration_line": signal.line,
            })
    targets = {roles.get(key) for key in ("TARGET", "EFFECT") if isinstance(roles.get(key), str)}
    sources = set()
    for key in ("SOURCE", "VALUE"):
        if isinstance(roles.get(key), str):
            sources |= expression_signals(roles[key])
    assignments = [
        item for item in design.assignments
        if item.module == contract.module and item.lhs in targets
    ]
    assignments.sort(key=lambda item: (
        0 if item.rhs == roles.get("VALUE") or item.rhs == roles.get("SOURCE") else 1,
        0 if sources & set(item.dependencies) else 1,
        item.line,
    ))
    assignment_facts = []
    evidence_segments = []
    for item in assignments[:5]:
        assignment_facts.append({
            "lhs": item.lhs, "rhs": item.rhs, "kind": item.kind,
            "guard": item.guard, "file": item.file, "line": item.line,
            "dependencies": item.dependencies,
        })
        excerpt = _source_excerpt(item.file, item.line)
        if excerpt and excerpt not in evidence_segments:
            evidence_segments.append(excerpt)
    return {
        "signals": signal_facts,
        "target_assignments": assignment_facts,
        "evidence_segments": evidence_segments,
        "structural_findings": structural_findings(rule, contract.module, design),
    }


def build_llm_request(
    contract: ContractIR,
    records: list[dict[str, Any]],
    duplicates: list[dict[str, Any]],
    properties: list[PropertyIR],
    results: dict[str, dict[str, Any]],
    design: RTLDesign,
) -> dict[str, Any]:
    rule_payload = []
    for record in records:
        enriched = deepcopy(record)
        enriched["baseline_property"] = _property_and_result(record, properties, results)
        enriched["rtl_facts"] = _rule_rtl_facts(record, contract, design)
        rule_payload.append(enriched)
    serialized_rules = json.dumps(rule_payload, ensure_ascii=True)
    relevant_macros = {
        name: value for name, value in design.macros.items()
        if f"`{name}" in serialized_rules
    }
    return {
        "requirement": "Requirement 6.1 Extension Contract Validation",
        "object_id": contract.region,
        "contract": {
            "contract_id": contract.contract_id,
            "object_type": contract.object_type,
            "region": contract.region,
            "module": contract.module,
            "state": contract.state,
            "events": contract.events,
            "inputs": contract.inputs,
            "outputs": contract.outputs,
            "dependencies": contract.dependencies,
            "assumptions": contract.assumptions,
            "evidence": contract.evidence,
        },
        "unique_rules": rule_payload,
        "semantic_duplicates_removed_before_validation": duplicates,
        "module_macros": relevant_macros,
        "fixed_primitives": sorted(PRIMITIVES),
    }


def conservative_response(
    contract: ContractIR,
    records: list[dict[str, Any]],
    design: RTLDesign,
) -> dict[str, Any]:
    """Fail closed when repeated LLM patches do not satisfy the trusted schema."""
    source_evidence = contract.evidence[0] if contract.evidence else {}
    evidence_files = source_evidence.get("files", []) if isinstance(source_evidence, dict) else []
    if not evidence_files:
        raise ContractValidationError(f"Contract has no RTL evidence: {contract.region}")
    base_evidence = [{
        "file": evidence_files[0],
        "line_start": source_evidence.get("line_start"),
        "line_end": source_evidence.get("line_end"),
        "snippet": source_evidence.get("snippet", ""),
    }]
    decisions = []
    active_refs = []
    for record in records:
        formal = record.get("baseline_property") or {}
        findings = structural_findings(record["rule"], contract.module, design)
        keep = formal.get("result") == "PASS" and formal.get("vacuity") != "VACUOUS" and not findings
        if keep:
            action = "KEEP"
            category = "NONE"
            disposition = "VALIDATED"
            replacements = [{
                "contract_field": record["contract_field"],
                **deepcopy(record["rule"]),
            }]
            active_refs.append(f"{record['rule_id']}#0")
            reason = "Conservative fallback retains only a baseline-Proven, non-vacuous, structurally valid rule."
        else:
            action = "REMOVE"
            replacements = []
            if findings and any("multi-bit" in item for item in findings):
                category = "WRONG_SIGNAL_ROLE"
                disposition = "CONTRACT_ERROR"
            elif formal.get("vacuity") == "VACUOUS":
                category = "UNSUPPORTED_SEMANTICS"
                disposition = "UNSUPPORTED_SEMANTICS"
            else:
                category = "UNSUPPORTED_SEMANTICS"
                disposition = "UNSUPPORTED_SEMANTICS"
            reason = "Conservative fallback removes a CEX, vacuous, or structurally invalid hypothesis."
            if findings:
                reason += " " + "; ".join(findings)
        decisions.append({
            "source_rule_id": record["rule_id"],
            "action": action,
            "cex_category": category,
            "disposition": disposition,
            "reason": reason,
            "modified_fields": [],
            "evidence": base_evidence,
            "replacement_rules": replacements,
        })
    non_reset_refs = [
        ref for ref in active_refs
        if next(
            item for item in records if item["rule_id"] == ref.rsplit("#", 1)[0]
        )["rule"].get("primitive") != "RESET"
    ]
    probes = non_reset_refs[:2]
    return {
        "object_id": contract.region,
        "boundary_assessment": {
            "status": "TOO_BROAD",
            "reason": "LLM refinement repeatedly failed validation; only conservative rule-level scope is retained.",
            "evidence": base_evidence,
        },
        "decisions": decisions,
        "probe_rule_refs": probes,
        "summary": "Fail-closed conservative fallback after invalid LLM refinements.",
    }
def _actual_evidence(raw: Any, allowed_files: set[str]) -> list[dict[str, Any]]:
    if not isinstance(raw, list) or not raw:
        raise ContractValidationError("every decision and boundary assessment needs RTL evidence")
    result = []
    for item in raw:
        if not isinstance(item, dict):
            raise ContractValidationError("evidence entry must be an object")
        path = str(Path(str(item.get("file", ""))).resolve())
        if path not in allowed_files:
            raise ContractValidationError(f"evidence file is outside the analyzed RTL: {path}")
        try:
            start = int(item["line_start"])
            end = int(item["line_end"])
        except (KeyError, TypeError, ValueError) as exc:
            raise ContractValidationError("evidence line range is invalid") from exc
        source_lines = Path(path).read_text(encoding="utf-8", errors="replace").splitlines()
        if start < 1 or end < start or end > len(source_lines):
            raise ContractValidationError(f"evidence line range {start}:{end} is outside {path}")
        result.append({
            "file": path,
            "line_start": start,
            "line_end": end,
            "snippet": "\n".join(source_lines[start - 1:end]),
        })
    return result


def _validate_replacement(
    replacement: dict[str, Any],
    module: str,
    design: RTLDesign,
) -> dict[str, Any]:
    if not isinstance(replacement, dict):
        raise ContractValidationError("replacement rule must be an object")
    field = str(replacement.get("contract_field", ""))
    primitive = str(replacement.get("primitive", "")).upper()
    roles = replacement.get("roles")
    if field not in RULE_FIELDS:
        raise ContractValidationError(f"invalid contract field: {field}")
    if primitive not in PRIMITIVES:
        raise ContractValidationError(f"invalid primitive: {primitive}")
    if not isinstance(roles, dict):
        raise ContractValidationError("replacement roles must be an object")
    expected_roles = PRIMITIVE_ROLES[primitive]
    if set(roles) != expected_roles:
        raise ContractValidationError(
            f"{primitive} roles must be exactly {sorted(expected_roles)}, got {sorted(roles)}"
        )
    def expand_macros(value: Any) -> Any:
        if isinstance(value, str):
            expanded = value
            for name, macro_value in sorted(design.macros.items(), key=lambda item: -len(item[0])):
                expanded = re.sub(rf"`{re.escape(name)}\b", str(macro_value), expanded)
            if "`" in expanded:
                unknown = sorted(set(re.findall(r"`([A-Za-z_][A-Za-z0-9_$]*)", expanded)))
                raise ContractValidationError(f"replacement references unknown RTL macros: {unknown}")
            return expanded
        if isinstance(value, list):
            return [expand_macros(item) for item in value]
        return value

    normalized_roles = {name: expand_macros(value) for name, value in roles.items()}
    rule = {
        "primitive": primitive,
        "roles": normalized_roles,
        "semantics": str(replacement.get("semantics", "")).strip(),
        "confidence": float(replacement.get("confidence", 0.0)),
    }
    if not rule["semantics"]:
        raise ContractValidationError("replacement semantics are empty")
    compiled = _compile(primitive, rule)
    if not compiled:
        raise ContractValidationError(f"replacement does not satisfy {primitive} role schema")
    known = set(design.module_signals.get(module, {}))
    invalid = expression_signals(compiled[0]) - known
    if invalid:
        raise ContractValidationError(f"replacement invents module signals: {sorted(invalid)}")
    findings = structural_findings(rule, module, design)
    if findings:
        raise ContractValidationError("replacement fails structural validation: " + "; ".join(findings))
    return {"contract_field": field, "rule": rule, "compiled_body": compiled[0]}


def validate_and_apply_response(
    response: dict[str, Any],
    contract: ContractIR,
    records: list[dict[str, Any]],
    design: RTLDesign,
) -> tuple[ContractIR, list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
    """Schema-check, evidence-check, and structurally check an LLM patch."""
    if not isinstance(response, dict) or response.get("object_id") != contract.region:
        raise ContractValidationError("response object_id does not match the Contract")
    allowed_files = {str(Path(path).resolve()) for path in design.files}
    boundary = response.get("boundary_assessment")
    if not isinstance(boundary, dict) or boundary.get("status") not in {"VALID", "TOO_BROAD", "WRONG"}:
        raise ContractValidationError("invalid boundary assessment")
    normalized_boundary = {
        "status": boundary["status"],
        "reason": str(boundary.get("reason", "")).strip(),
        "evidence": _actual_evidence(boundary.get("evidence"), allowed_files),
    }
    input_by_id = {item["rule_id"]: item for item in records}
    decisions = response.get("decisions")
    if not isinstance(decisions, list):
        raise ContractValidationError("decisions must be a list")
    ids = [item.get("source_rule_id") for item in decisions if isinstance(item, dict)]
    if len(ids) != len(set(ids)) or set(ids) != set(input_by_id):
        raise ContractValidationError("response must contain exactly one decision for every unique source rule")

    normalized_decisions: list[dict[str, Any]] = []
    active: dict[str, dict[str, Any]] = {}
    for decision in decisions:
        source_id = decision["source_rule_id"]
        source = input_by_id[source_id]
        action = str(decision.get("action", ""))
        category = str(decision.get("cex_category", ""))
        disposition = str(decision.get("disposition", ""))
        if action not in ACTIONS or category not in CEX_CATEGORIES or disposition not in DISPOSITIONS:
            raise ContractValidationError(f"invalid decision enum for {source_id}")
        replacements = decision.get("replacement_rules", [])
        if not isinstance(replacements, list):
            raise ContractValidationError(f"replacement_rules must be a list for {source_id}")
        if action == "REMOVE" and replacements:
            raise ContractValidationError(f"REMOVE must have no replacement rules for {source_id}")
        if action != "REMOVE" and not replacements:
            raise ContractValidationError(f"{action} requires replacement rules for {source_id}")
        normalized_replacements = [
            _validate_replacement(item, contract.module, design) for item in replacements
        ]
        if action == "KEEP":
            if len(normalized_replacements) != 1:
                raise ContractValidationError(f"KEEP must contain exactly one rule for {source_id}")
            replacement = normalized_replacements[0]
            if replacement["contract_field"] != source["contract_field"] or _canonical_rule(replacement["rule"]) != _canonical_rule(source["rule"]):
                raise ContractValidationError(f"KEEP changed the source rule {source_id}")
            baseline_property = source.get("baseline_property") or {}
            if baseline_property.get("result") == "FAIL" or baseline_property.get("vacuity") == "VACUOUS":
                raise ContractValidationError(f"CEX/vacuous source rule cannot be KEEP: {source_id}")
        if action == "PATCH" and len(normalized_replacements) == 1:
            replacement = normalized_replacements[0]
            if replacement["contract_field"] == source["contract_field"] and _canonical_rule(replacement["rule"]) == _canonical_rule(source["rule"]):
                raise ContractValidationError(f"PATCH does not change compiled semantics for {source_id}")
        modified_fields = decision.get("modified_fields", [])
        if not isinstance(modified_fields, list) or any(not isinstance(item, str) for item in modified_fields):
            raise ContractValidationError(f"modified_fields is invalid for {source_id}")
        if action == "PATCH" and not modified_fields:
            raise ContractValidationError(f"PATCH must name modified fields for {source_id}")
        evidence = _actual_evidence(decision.get("evidence"), allowed_files)
        normalized = {
            "source_rule_id": source_id,
            "source_contract_field": source["contract_field"],
            "source_rule": source["rule"],
            "action": action,
            "cex_category": category,
            "disposition": disposition,
            "reason": str(decision.get("reason", "")).strip(),
            "modified_fields": modified_fields,
            "evidence": evidence,
            "replacement_rules": normalized_replacements,
        }
        normalized_decisions.append(normalized)
        for index, replacement in enumerate(normalized_replacements):
            active[f"{source_id}#{index}"] = replacement

    probes = response.get("probe_rule_refs")
    if not isinstance(probes, list) or len(probes) > 2 or len(probes) != len(set(probes)):
        raise ContractValidationError("probe_rule_refs must contain at most two unique probes")
    if not probes and active:
        raise ContractValidationError("an object with active rules must select one or two probes")
    if any(ref not in active for ref in probes):
        raise ContractValidationError("probe_rule_refs points to an inactive replacement")
    if any(active[ref]["rule"]["primitive"] == "RESET" for ref in probes):
        raise ContractValidationError("reset-only properties cannot be used as semantic probes")

    refined = replace(contract)
    for field in RULE_FIELDS:
        setattr(refined, field, [])
    for replacement in active.values():
        getattr(refined, replacement["contract_field"]).append(deepcopy(replacement["rule"]))
    refined.reused_primitives = list(dict.fromkeys(
        replacement["rule"]["primitive"] for replacement in active.values()
    ))
    probe_rules = [{"probe_ref": ref, **deepcopy(active[ref])} for ref in probes]
    return refined, normalized_decisions, probe_rules, normalized_boundary


def _probe_contract(contract: ContractIR, probes: list[dict[str, Any]]) -> ContractIR:
    selected = replace(contract)
    for field in RULE_FIELDS:
        setattr(selected, field, [])
    selected.reused_primitives = []
    for probe in probes:
        getattr(selected, probe["contract_field"]).append(deepcopy(probe["rule"]))
        selected.reused_primitives.append(probe["rule"]["primitive"])
    return selected


def _run_formal(
    properties: list[PropertyIR],
    design: RTLDesign,
    top: str,
    output: Path,
    config: dict[str, Any],
    sva_name: str,
) -> tuple[Any, Path]:
    output.mkdir(parents=True, exist_ok=True)
    sva_path = output.parent / sva_name
    generate_sva(
        properties, design.signals, top, sva_path,
        clock=config.get("clock", "clk"), reset=config.get("reset", "resetn"),
        module_signals=design.module_signals,
    )
    generate_tcl(design.files, str(sva_path), top, output, _formal_config(config))
    result = JasperGoldRunner().run(
        design.files, str(sva_path), top, properties, output, _formal_config(config)
    )
    return result, sva_path


def _summary_counts(results: list[Any], properties: list[PropertyIR], extension_only: bool = False) -> dict[str, Any]:
    property_by_id = {prop.property_id: prop for prop in properties}
    selected = []
    for result in results:
        prop = property_by_id.get(result.property_id)
        if not prop or (extension_only and prop.object_type != ObjectType.EXTENSION):
            continue
        selected.append(result)
    proven = sum(item.result == "PASS" for item in selected)
    cex = sum(item.result == "FAIL" for item in selected)
    unknown = len(selected) - proven - cex
    non_vacuous = sum(item.vacuity == "NON_VACUOUS" for item in selected)
    vacuous = sum(item.vacuity == "VACUOUS" for item in selected)
    return {
        "total": len(selected), "proven": proven, "cex": cex, "unknown": unknown,
        "proven_rate": round(100.0 * proven / len(selected), 2) if selected else 0.0,
        "non_vacuous": non_vacuous, "vacuous": vacuous,
    }


def _cex_clusters(
    contracts: list[ContractIR],
    records_by_region: dict[str, list[dict[str, Any]]],
    decisions_by_region: dict[str, list[dict[str, Any]]],
    properties: list[PropertyIR],
    baseline_results: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    clusters = []
    contract_by_region = {item.region: item for item in contracts}
    decision_lookup = {
        (region, decision["source_rule_id"]): decision
        for region, decisions in decisions_by_region.items() for decision in decisions
    }
    for prop in properties:
        result = baseline_results.get(prop.property_id, {})
        if prop.object_type != ObjectType.EXTENSION or result.get("result") != "FAIL":
            continue
        records = records_by_region.get(prop.region_id, [])
        source = next((
            item for item in records
            if _canonical_rule(item["rule"]) == _canonical_rule({"primitive": prop.template, "roles": prop.bindings})
        ), None)
        if not source:
            raise ContractValidationError(f"cannot map CEX property to Contract field: {prop.property_id}")
        decision = decision_lookup[(prop.region_id, source["rule_id"])]
        contract = contract_by_region[prop.region_id]
        clusters.append({
            "object_id": contract.region,
            "object_type": contract.object_type,
            "property_id": prop.property_id,
            "contract_id": contract.contract_id,
            "contract_field": source["contract_field"],
            "source_rule_id": source["rule_id"],
            "failing_primitive": prop.template,
            "sva_body": prop.body,
            "rtl_evidence": decision["evidence"],
            "cex_category": decision["cex_category"],
            "disposition": decision["disposition"],
            "diagnosis": decision["reason"],
            "refinement_suggestion": {
                "action": decision["action"],
                "modified_fields": decision["modified_fields"],
                "replacement_rules": decision["replacement_rules"],
            },
        })
    return clusters


def reject_failed_expansion_rules(
    contracts: list[ContractIR],
    properties: list[PropertyIR],
    formal_results: list[Any],
    require_non_vacuous: bool = False,
    stage: str = "FULL_EXPANSION",
) -> tuple[list[ContractIR], list[dict[str, Any]]]:
    """Fail closed on CEX/Unknown/vacuous rules found after a passed object probe."""
    property_by_id = {item.property_id: item for item in properties}
    rejected_signatures: dict[str, set[str]] = {}
    rejections = []
    contract_by_region = {item.region: item for item in contracts}
    for result in formal_results:
        prop = property_by_id.get(result.property_id)
        if not prop or prop.object_type != ObjectType.EXTENSION:
            continue
        accepted_vacuity = result.vacuity == "NON_VACUOUS" if require_non_vacuous else result.vacuity != "VACUOUS"
        if result.result == "PASS" and accepted_vacuity:
            continue
        signature = _canonical_rule({"primitive": prop.template, "roles": prop.bindings})
        rejected_signatures.setdefault(prop.region_id, set()).add(signature)
        contract = contract_by_region[prop.region_id]
        field = ""
        source_rule: dict[str, Any] | None = None
        for candidate_field in RULE_FIELDS:
            for rule in getattr(contract, candidate_field):
                if _canonical_rule(rule) == signature:
                    field = candidate_field
                    source_rule = rule
                    break
            if source_rule is not None:
                break
        if source_rule is None:
            raise ContractValidationError(
                f"cannot map post-expansion result to refined Contract: {prop.property_id}"
            )
        if result.result == "PASS" and require_non_vacuous and result.vacuity != "NON_VACUOUS":
            category = "UNSUPPORTED_SEMANTICS"
            reason = "Probe was Proven but JasperGold did not establish a non-vacuous antecedent."
        elif result.vacuity == "VACUOUS":
            category = "UNSUPPORTED_SEMANTICS"
            reason = "Full-expansion property is vacuous; Requirement 6.1 forbids accepting it."
        elif result.result == "UNKNOWN":
            category = "UNSUPPORTED_SEMANTICS"
            reason = "Full-expansion property is not proven within the configured formal run."
        else:
            category = "MISSING_GUARD" if prop.template in {"UPDATE", "DATA_INTEGRITY", "CAUSALITY", "ORDERING"} else "UNSUPPORTED_SEMANTICS"
            reason = (
                "Full-expansion CEX after successful object probes shows that this field-level "
                "hypothesis still lacks an exact RTL path condition or faithful primitive semantics."
            )
        rejections.append({
            "object_id": contract.region,
            "object_type": contract.object_type,
            "property_id": prop.property_id,
            "contract_id": contract.contract_id,
            "contract_field": field,
            "failing_primitive": prop.template,
            "sva_body": prop.body,
            "formal_result": result.result,
            "vacuity": result.vacuity,
            "validation_stage": stage,
            "cex_category": category,
            "disposition": "CONTRACT_ERROR" if result.result == "FAIL" else "UNSUPPORTED_SEMANTICS",
            "diagnosis": reason,
            "rtl_evidence": contract.evidence,
            "refinement_suggestion": {
                "action": "REMOVE_FROM_TRUSTED_CONTRACT",
                "reason": "Do not guess another guard; require a new evidence-backed field patch and Probe in a later iteration.",
            },
        })
    if not rejected_signatures:
        return contracts, rejections
    refined = []
    for contract in contracts:
        copied = replace(contract)
        rejected = rejected_signatures.get(contract.region, set())
        for field in RULE_FIELDS:
            setattr(copied, field, [
                deepcopy(rule) for rule in getattr(contract, field)
                if _canonical_rule(rule) not in rejected
            ])
        copied.reused_primitives = list(dict.fromkeys(
            str(rule.get("primitive", "")).upper()
            for field in RULE_FIELDS for rule in getattr(copied, field)
        ))
        refined.append(copied)
    return refined, rejections


def select_followup_probes(contract: ContractIR, round_number: int) -> list[dict[str, Any]]:
    """Choose new foundational probes after removing failed probe hypotheses."""
    records, _duplicates = unique_rules(contract)
    priority = {
        "PERSISTENCE": 0, "STABILITY": 1, "DATA_INTEGRITY": 2,
        "UPDATE": 3, "CAUSALITY": 4, "ORDERING": 5,
        "HOLD": 6, "MUTUAL_EXCLUSION": 7, "PROGRESS": 8,
        "CONSERVATION": 9, "RESET": 10,
    }
    candidates = [item for item in records if item["rule"].get("primitive") != "RESET"]
    candidates.sort(key=lambda item: (priority.get(str(item["rule"].get("primitive", "")), 99), item["rule_id"]))
    return [
        {
            "probe_ref": f"round{round_number}:{item['rule_id']}#0",
            "contract_field": item["contract_field"],
            "rule": deepcopy(item["rule"]),
            "compiled_body": _compile(str(item["rule"].get("primitive", "")).upper(), item["rule"])[0],
        }
        for item in candidates[:2]
    ]


def run(args: argparse.Namespace) -> dict[str, Any]:
    baseline = Path(args.baseline).resolve()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = _config(Path(args.config).resolve())
    baseline_summary = load_json(baseline / "run_summary.json")
    baseline_top = baseline_summary.get("top")
    if baseline_top and args.top != baseline_top:
        raise ContractValidationError(
            f"Req6.1 must use the Requirement-6 top {baseline_top!r}, got {args.top!r}"
        )
    design = RTLDesign.load(baseline / "rtl_structure.json")
    microarchitecture = microarchitecture_from_dict(load_json(baseline / "microarchitecture.json"))
    baseline_contracts = [
        contract_from_dict(item) for item in load_json(baseline / "normalized_contracts.json")
        if item.get("ontology_classification") == "NEW_OBJECT_CANDIDATE"
    ]
    if not baseline_contracts:
        raise ContractValidationError("baseline contains no Extension Contracts")
    baseline_properties = properties_from_dict(load_json(baseline / "properties.json"))
    baseline_formal = load_json(baseline / "formal_results.json")
    baseline_results = {item["property_id"]: item for item in baseline_formal["results"]}
    extension_properties = [item for item in baseline_properties if item.object_type == ObjectType.EXTENSION]
    core_properties = [item for item in baseline_properties if item.object_type != ObjectType.EXTENSION]
    dump_json(output / "contracts_original.json", baseline_contracts)

    client = DeepSeekClient(_llm_config(config["llm"]))
    system_prompt = (PROJECT_ROOT / "llm" / "prompts" / "contract_refinement.txt").read_text(encoding="utf-8")
    refined_contracts: list[ContractIR] = []
    probes_by_region: dict[str, list[dict[str, Any]]] = {}
    decisions_by_region: dict[str, list[dict[str, Any]]] = {}
    records_by_region: dict[str, list[dict[str, Any]]] = {}
    boundary_by_region: dict[str, dict[str, Any]] = {}
    all_duplicates: list[dict[str, Any]] = []
    llm_usage = Counter()
    llm_calls = 0
    response_models = set()

    for contract in baseline_contracts:
        records, duplicates = unique_rules(contract)
        object_properties = [item for item in extension_properties if item.region_id == contract.region]
        for record in records:
            record["baseline_property"] = _property_and_result(
                record, object_properties, baseline_results
            )
        records_by_region[contract.region] = records
        all_duplicates.extend({"object_id": contract.region, **item} for item in duplicates)
        request = build_llm_request(contract, records, duplicates, object_properties, baseline_results, design)
        object_dir = output / "llm"
        object_dir.mkdir(parents=True, exist_ok=True)
        # A repeated run may accept an earlier attempt than the previous run.
        # Remove only this object's generated response cache so stale attempts
        # cannot be mistaken for evidence used by the current summary.
        for stale in object_dir.glob(f"{contract.region}.attempt*.json"):
            stale.unlink()
        for suffix in ("json", "fallback.json"):
            (object_dir / f"{contract.region}.{suffix}").unlink(missing_ok=True)
        validation_error = ""
        previous_response: dict[str, Any] | None = None
        for attempt in range(1, 4):
            if attempt == 1:
                user_payload: dict[str, Any] = request
            else:
                user_payload = {
                    "original_request": request,
                    "rejected_response": previous_response,
                    "validator_error": validation_error,
                    "instruction": (
                        "Return a complete corrected response. Do not repeat the validator error. "
                        "Treat baseline formal FAIL as authoritative: do not defend or reproduce the "
                        "same compiled rule. Re-read whether allegedly exclusive events can co-occur. "
                        "If the fixed primitive cannot express the evidence-backed guard/grouping, REMOVE."
                    ),
                }
            response, metadata = client.complete_json(
                system_prompt, json.dumps(user_payload, ensure_ascii=False)
            )
            llm_calls += 1
            safe_metadata = {key: value for key, value in metadata.items() if key != "raw_content"}
            dump_json(object_dir / f"{contract.region}.attempt{attempt}.json", {
                "request": user_payload, "response": response, "metadata": safe_metadata,
            })
            usage = metadata.get("usage", {})
            for key in ("prompt_tokens", "completion_tokens", "total_tokens"):
                llm_usage[key] += int(usage.get(key, 0) or 0)
            if metadata.get("response_model"):
                response_models.add(metadata["response_model"])
            try:
                refined, decisions, probes, boundary = validate_and_apply_response(
                    response, contract, records, design
                )
                dump_json(object_dir / f"{contract.region}.json", {
                    "request": user_payload, "response": response, "metadata": safe_metadata,
                    "accepted_attempt": attempt,
                })
                break
            except ContractValidationError as exc:
                validation_error = str(exc)
                previous_response = response
        else:
            response = conservative_response(contract, records, design)
            refined, decisions, probes, boundary = validate_and_apply_response(
                response, contract, records, design
            )
            dump_json(object_dir / f"{contract.region}.fallback.json", {
                "trigger": validation_error,
                "response": response,
                "mode": "CONSERVATIVE_FAIL_CLOSED",
            })
        refined_contracts.append(refined)
        decisions_by_region[contract.region] = decisions
        probes_by_region[contract.region] = probes
        boundary_by_region[contract.region] = boundary

    dump_json(output / "contracts_refined.json", refined_contracts)
    dump_json(output / "contract_refinements.json", {
        "objects": [
            {
                "object_id": contract.region,
                "object_type": contract.object_type,
                "boundary_assessment": boundary_by_region[contract.region],
                "decisions": decisions_by_region[contract.region],
                "probe_rules": probes_by_region[contract.region],
            }
            for contract in refined_contracts
        ],
        "semantic_duplicates_removed": all_duplicates,
    })
    clusters = _cex_clusters(
        baseline_contracts, records_by_region, decisions_by_region,
        extension_properties, baseline_results,
    )
    dump_json(output / "cex_clusters.json", clusters)

    module_signals = {module: set(signals) for module, signals in design.module_signals.items()}
    reset_asserted = f"!{config.get('reset', 'resetn')}" if config.get("reset_active_low", True) else config.get("reset", "resetn")
    probe_contracts = [_probe_contract(contract, probes_by_region[contract.region]) for contract in refined_contracts]
    probe_properties, probe_bindings = bind_extension_primitives(probe_contracts, module_signals, reset_asserted)
    rejected_probe_bindings = [item for item in probe_bindings if item.status != "BOUND"]
    if rejected_probe_bindings:
        raise ContractValidationError(f"probe binding rejected: {rejected_probe_bindings[0].reason}")
    validate_properties(probe_properties, microarchitecture, set(design.signals))
    probe_result, _probe_sva = _run_formal(
        probe_properties, design, args.top, output / "formal_probe", config,
        "generated_probe_assertions.sv",
    )
    probe_result_by_id = {item.property_id: item for item in probe_result.results}
    probe_gate: dict[str, dict[str, Any]] = {}
    probe_records = []
    for contract, probes in zip(probe_contracts, (probes_by_region[item.region] for item in refined_contracts)):
        object_props = [item for item in probe_properties if item.region_id == contract.region]
        property_by_signature = {
            _canonical_rule({"primitive": item.template, "roles": item.bindings}): item
            for item in object_props
        }
        object_records = []
        for probe in probes:
            prop = property_by_signature[_canonical_rule(probe["rule"])]
            result = probe_result_by_id[prop.property_id]
            consistent = not structural_findings(probe["rule"], contract.module, design)
            accepted = result.result == "PASS" and result.vacuity == "NON_VACUOUS" and consistent
            record = {
                "object_id": contract.region,
                "probe_round": 1,
                "probe_ref": probe["probe_ref"],
                "property_id": prop.property_id,
                "contract_field": probe["contract_field"],
                "primitive": probe["rule"]["primitive"],
                "result": result.result,
                "vacuity": result.vacuity,
                "rtl_evidence_consistent": consistent,
                "accepted": accepted,
            }
            object_records.append(record)
            probe_records.append(record)
        passed = bool(object_records) and all(item["accepted"] for item in object_records)
        probe_gate[contract.region] = {
            "passed": passed,
            "full_expansion_allowed": passed,
            "reason": "all probes proven, non-vacuous, and evidence-consistent" if passed else "probe gate failed; full expansion stopped",
        }
    probe_round_summaries = [{"round": 1, "formal_summary": probe_result.summary}]
    failed_regions = {region for region, gate in probe_gate.items() if not gate["passed"]}
    refined_contracts, probe_rejections = reject_failed_expansion_rules(
        refined_contracts,
        [item for item in probe_properties if item.region_id in failed_regions],
        probe_result.results,
        require_non_vacuous=True,
        stage="PROBE_ROUND_1",
    )
    if probe_rejections:
        clusters.extend(probe_rejections)
        dump_json(output / "cex_clusters.json", clusters)
    followup_probes = {
        contract.region: select_followup_probes(contract, 2)
        for contract in refined_contracts if contract.region in failed_regions
    }
    followup_contracts = [
        _probe_contract(contract, followup_probes[contract.region])
        for contract in refined_contracts
        if contract.region in failed_regions and followup_probes[contract.region]
    ]
    if followup_contracts:
        followup_properties, followup_bindings = bind_extension_primitives(
            followup_contracts, module_signals, reset_asserted
        )
        rejected_followup = [item for item in followup_bindings if item.status != "BOUND"]
        if rejected_followup:
            raise ContractValidationError(f"follow-up probe binding rejected: {rejected_followup[0].reason}")
        validate_properties(followup_properties, microarchitecture, set(design.signals))
        followup_result, _followup_sva = _run_formal(
            followup_properties, design, args.top, output / "formal_probe_round2", config,
            "generated_probe_assertions_round2.sv",
        )
        probe_round_summaries.append({"round": 2, "formal_summary": followup_result.summary})
        followup_result_by_id = {item.property_id: item for item in followup_result.results}
        for contract in followup_contracts:
            probes = followup_probes[contract.region]
            object_props = [item for item in followup_properties if item.region_id == contract.region]
            property_by_signature = {
                _canonical_rule({"primitive": item.template, "roles": item.bindings}): item
                for item in object_props
            }
            object_records = []
            for probe in probes:
                prop = property_by_signature[_canonical_rule(probe["rule"])]
                result = followup_result_by_id[prop.property_id]
                consistent = not structural_findings(probe["rule"], contract.module, design)
                accepted = result.result == "PASS" and result.vacuity == "NON_VACUOUS" and consistent
                record = {
                    "object_id": contract.region,
                    "probe_round": 2,
                    "probe_ref": probe["probe_ref"],
                    "property_id": prop.property_id,
                    "contract_field": probe["contract_field"],
                    "primitive": probe["rule"]["primitive"],
                    "result": result.result,
                    "vacuity": result.vacuity,
                    "rtl_evidence_consistent": consistent,
                    "accepted": accepted,
                }
                object_records.append(record)
                probe_records.append(record)
            passed = bool(object_records) and all(item["accepted"] for item in object_records)
            probe_gate[contract.region] = {
                "passed": passed,
                "full_expansion_allowed": passed,
                "reason": (
                    "failed probe fields were removed; all round-2 probes are proven, non-vacuous, and evidence-consistent"
                    if passed else "round-2 probe gate failed; full expansion stopped"
                ),
            }
        still_failed = {region for region, gate in probe_gate.items() if not gate["passed"]}
        refined_contracts, round2_rejections = reject_failed_expansion_rules(
            refined_contracts,
            [item for item in followup_properties if item.region_id in still_failed],
            followup_result.results,
            require_non_vacuous=True,
            stage="PROBE_ROUND_2",
        )
        probe_rejections.extend(round2_rejections)
        if round2_rejections:
            clusters.extend(round2_rejections)
            dump_json(output / "cex_clusters.json", clusters)
    dump_json(output / "probe_refinements.json", probe_rejections)
    dump_json(output / "contracts_refined.json", refined_contracts)
    dump_json(output / "probe_results.json", {
        "objects": probe_gate,
        "probes": probe_records,
        "rounds": probe_round_summaries,
    })

    gated_contracts = [item for item in refined_contracts if probe_gate[item.region]["passed"]]
    refined_extension_properties, final_bindings = bind_extension_primitives(gated_contracts, module_signals, reset_asserted)
    rejected_final = [item for item in final_bindings if item.status != "BOUND"]
    if rejected_final:
        raise ContractValidationError(f"refined full binding rejected: {rejected_final[0].reason}")
    initial_full_properties = core_properties + refined_extension_properties
    validate_properties(initial_full_properties, microarchitecture, set(design.signals))
    initial_full_result, _initial_sva = _run_formal(
        initial_full_properties, design, args.top, output / "formal_full_initial", config,
        "generated_assertions_initial.sv",
    )
    gated_contracts, post_rejections = reject_failed_expansion_rules(
        gated_contracts, refined_extension_properties, initial_full_result.results
    )
    dump_json(output / "post_expansion_rejections.json", post_rejections)
    if post_rejections:
        clusters.extend(post_rejections)
        dump_json(output / "cex_clusters.json", clusters)
        gated_regions = {item.region for item in gated_contracts}
        refined_contracts = [
            next((candidate for candidate in gated_contracts if candidate.region == item.region), item)
            if item.region in gated_regions else item
            for item in refined_contracts
        ]
        dump_json(output / "contracts_refined.json", refined_contracts)
    refined_extension_properties, final_bindings = bind_extension_primitives(
        gated_contracts, module_signals, reset_asserted
    )
    final_properties = core_properties + refined_extension_properties
    validate_properties(final_properties, microarchitecture, set(design.signals))
    final_result, final_sva = _run_formal(
        final_properties, design, args.top, output / "formal", config,
        "generated_assertions.sv",
    )
    dump_json(output / "generated_properties.json", final_properties)
    dump_json(output / "template_bindings.json", final_bindings)
    dump_json(output / "formal_results.json", final_result)

    final_ext = _summary_counts(final_result.results, final_properties, extension_only=True)
    final_core = _summary_counts(final_result.results, final_properties, extension_only=False)
    # The non-extension subset is reported independently from the overall run.
    extension_ids = {item.property_id for item in refined_extension_properties}
    core_results = [item for item in final_result.results if item.property_id not in extension_ids]
    final_core = _summary_counts(core_results, core_properties)
    baseline_ext = _summary_counts(
        [type("BaselineResult", (), item)() for item in baseline_formal["results"]],
        baseline_properties,
        extension_only=True,
    )
    category_counts = Counter(item["cex_category"] for item in clusters)
    disposition_counts = Counter(item["disposition"] for item in clusters)
    modified_fields = sum(len(item["modified_fields"]) for values in decisions_by_region.values() for item in values)
    removed = (
        sum(item["action"] == "REMOVE" for values in decisions_by_region.values() for item in values)
        + len(all_duplicates) + len(probe_rejections) + len(post_rejections)
    )
    summary = {
        "schema": "requirement6.1-summary.v1",
        "design": args.design,
        "top": args.top,
        "baseline_extension": baseline_ext,
        "final_extension": final_ext,
        "final_core": final_core,
        "overall": final_result.summary,
        "proof_core_coverage": final_result.coverage,
        "probe": {
            "objects_passed": sum(item["passed"] for item in probe_gate.values()),
            "objects_failed": sum(not item["passed"] for item in probe_gate.values()),
            "properties_passed": sum(item["accepted"] for item in probe_records),
            "properties_failed": sum(not item["accepted"] for item in probe_records),
        },
        "contract_refinement": {
            "objects": len(refined_contracts),
            "modified_contract_fields": modified_fields,
            "removed_unsupported_hypotheses": removed,
            "probe_cex_refinements": len(probe_rejections),
            "post_expansion_rejections": len(post_rejections),
            "boundary_statuses": dict(Counter(item["status"] for item in boundary_by_region.values())),
        },
        "cex_categories": dict(category_counts),
        "cex_dispositions": dict(disposition_counts),
        "llm": {
            "provider": "deepseek",
            "requested_model": config["llm"].get("model"),
            "response_models": sorted(response_models),
            "usage": dict(llm_usage),
            "calls": llm_calls,
        },
        "artifacts": {
            "contracts_original": str(output / "contracts_original.json"),
            "contracts_refined": str(output / "contracts_refined.json"),
            "probe_results": str(output / "probe_results.json"),
            "cex_clusters": str(output / "cex_clusters.json"),
            "generated_assertions": str(final_sva),
            "formal_results": str(output / "formal_results.json"),
        },
    }
    dump_json(output / "summary.json", summary)
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Requirement-6.1 Extension Contract validator")
    parser.add_argument("--design", required=True)
    parser.add_argument("--top", required=True)
    parser.add_argument("--baseline", required=True, help="Requirement-6 output directory")
    parser.add_argument("--output", required=True)
    parser.add_argument("--config", required=True)
    return parser


def main() -> int:
    try:
        summary = run(build_parser().parse_args())
    except Exception as exc:
        print(json.dumps({"status": "ERROR", "error": str(exc)}, ensure_ascii=False, indent=2), file=sys.stderr)
        return 2
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
