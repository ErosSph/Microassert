"""Fixed verification primitives for safely compiling Extension Contracts."""

from __future__ import annotations

import re
import json
from typing import Any

from dateassertion.ir.schema import ContractIR, ObjectType, PropertyIR, PropertySource, TemplateBindingIR
from dateassertion.ontology.contracts import PRIMITIVES


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")
LITERAL = re.compile(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+")


def _role(rule: dict[str, Any], name: str) -> Any:
    roles = rule.get("roles", {})
    return roles.get(name) if isinstance(roles, dict) else None


def _expr(value: Any) -> str | None:
    return value.strip() if isinstance(value, str) and value.strip() else None


def _string_list(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [item for item in value if isinstance(item, str) and item]
    return []


def expression_signals(expression: str) -> set[str]:
    clean = LITERAL.sub(" ", expression)
    clean = re.sub(r"`[A-Za-z_][A-Za-z0-9_$]*", " ", clean)
    ignored = {"past", "stable", "onehot", "onehot0", "rose", "fell", "inside", "true", "false"}
    return {name for name in IDENT.findall(clean) if name not in ignored}


def _compile(primitive: str, rule: dict[str, Any]) -> tuple[str, dict[str, Any]] | None:
    if primitive == "ONEHOT_STEP":
        target, seed = (_expr(_role(rule, k)) for k in ("TARGET", "SEED"))
        if target and seed:
            return f"(({seed}) || $onehot0({target})) |=> $onehot0({target})", {"TARGET":target,"SEED":seed}
        return None
    if primitive in {"INDEXED_READ", "INDEXED_WRITE"}:
        condition, bank, index = (_expr(_role(rule, k)) for k in ("CONDITION", "BANK", "INDEX"))
        value_role = "TARGET" if primitive == "INDEXED_READ" else "VALUE"
        value = _expr(_role(rule, value_role))
        if condition and bank and index and value and re.fullmatch(r"[A-Za-z_][\w$]*", bank):
            roles = {"CONDITION":condition,"BANK":bank,"INDEX":index,value_role:value}
            if primitive == "INDEXED_READ":
                return f"({condition}) |-> ({value}) == {bank}[{index}]", roles
            return f"({condition}) |=> {bank}[$past({index})] == $past({value})", roles
        return None
    if primitive == "STATE_LEGAL":
        target = _expr(_role(rule, "TARGET"))
        values = _role(rule, "VALUES")
        if target and isinstance(values, list) and values and all(
            isinstance(v, str) and re.fullmatch(
                r"[1-9][0-9]*'(?:[bB][01][01_]*|[dD][0-9][0-9_]*|[hH][0-9a-fA-F][0-9a-fA-F_]*)", v
            ) for v in values
        ):
            values = list(dict.fromkeys(values))
            return f"(1'b1) |-> {target} inside {{{', '.join(values)}}}", {"TARGET": target, "VALUES": values}
        return None
    if primitive == "ONEHOT_STATE":
        target = _expr(_role(rule, "TARGET"))
        if target:
            return f"(1'b1) |-> $onehot0({target})", {"TARGET": target}
        return None
    if primitive == "UPDATE":
        condition, target, value = (_expr(_role(rule, key)) for key in ("CONDITION", "TARGET", "VALUE"))
        delay = _role(rule, "DELAY")
        if condition and target and value and delay in (0, 1, "0", "1", None):
            normalized_delay = int(delay if delay is not None else 1)
            roles = {"CONDITION": condition, "TARGET": target, "VALUE": value, "DELAY": normalized_delay}
            if normalized_delay == 0:
                return f"({condition}) |-> {target} == ({value})", roles
            return f"({condition}) |=> {target} == $past({value})", roles
    elif primitive == "HOLD":
        condition, target = (_expr(_role(rule, key)) for key in ("CONDITION", "TARGET"))
        if condition and target:
            return f"({condition}) |=> $stable({target})", {"CONDITION": condition, "TARGET": target}
    elif primitive in {"CONTROL_ASSERT", "CONTROL_DEASSERT"}:
        condition, target = (_expr(_role(rule, key)) for key in ("CONDITION", "TARGET"))
        delay = _role(rule, "DELAY")
        if condition and target and delay in (0, 1, "0", "1", None):
            normalized_delay = int(delay if delay is not None else 1)
            operator = "|->" if normalized_delay == 0 else "|=>"
            effect = target if primitive == "CONTROL_ASSERT" else f"!({target})"
            return f"({condition}) {operator} ({effect})", {
                "CONDITION": condition, "TARGET": target, "DELAY": normalized_delay,
            }
    elif primitive in {"CAUSALITY", "ORDERING"}:
        first_name, second_name = (("CAUSE", "EFFECT") if primitive == "CAUSALITY" else ("FIRST", "SECOND"))
        first, second = (_expr(_role(rule, key)) for key in (first_name, second_name))
        delay = _role(rule, "DELAY")
        if first and second and delay in (0, 1, "0", "1", None):
            operator = "|->" if str(delay or 0) == "0" else "|=>"
            return f"({first}) {operator} ({second})", {first_name: first, second_name: second, "DELAY": int(delay or 0)}
    elif primitive == "STABILITY":
        condition = _expr(_role(rule, "CONDITION"))
        signals = _string_list(_role(rule, "SIGNALS"))
        if condition and signals:
            payload = signals[0] if len(signals) == 1 else "{" + ", ".join(signals) + "}"
            return f"({condition}) |=> $stable({payload})", {"CONDITION": condition, "SIGNALS": signals}
    elif primitive == "DATA_INTEGRITY":
        condition = _expr(_role(rule, "CONDITION")) or "1'b1"
        source, target = (_expr(_role(rule, key)) for key in ("SOURCE", "TARGET"))
        delay = _role(rule, "DELAY")
        if source and target and delay in (0, 1, "0", "1", None):
            if str(delay or 0) == "0":
                return f"({condition}) |-> {target} == ({source})", {"CONDITION": condition, "SOURCE": source, "TARGET": target, "DELAY": 0}
            return f"({condition}) |=> {target} == $past({source})", {"CONDITION": condition, "SOURCE": source, "TARGET": target, "DELAY": 1}
    elif primitive == "MUTUAL_EXCLUSION":
        signals = _string_list(_role(rule, "SIGNALS"))
        if len(signals) >= 2:
            return "$onehot0({" + ", ".join(signals) + "})", {"SIGNALS": signals}
    elif primitive == "PERSISTENCE":
        start, end = (_expr(_role(rule, key)) for key in ("START", "END"))
        if start and end:
            return f"({start}) && !({end}) |=> ({start})", {"START": start, "END": end}
    elif primitive == "RESET":
        reset, target, value = (_expr(_role(rule, key)) for key in ("RESET", "TARGET", "VALUE"))
        if reset and target and value:
            return f"({reset}) |=> {target} == ({value})", {"RESET": reset, "TARGET": target, "VALUE": value}
    elif primitive == "PROGRESS":
        start, end = (_expr(_role(rule, key)) for key in ("START", "END"))
        bound = _role(rule, "MAX_DELAY")
        # Bounded iterative units (for example dividers) routinely need more
        # than sixteen cycles.  Keep the primitive finite and compiler-owned,
        # but permit the bounded microarchitecture paths required by Req8.5.
        if start and end and isinstance(bound, int) and 1 <= bound <= 64:
            return f"({start}) |-> ##[1:{bound}] ({end})", {"START": start, "END": end, "MAX_DELAY": bound}
    elif primitive == "BOUNDED_DOMINANCE":
        first, second = (_expr(_role(rule, key)) for key in ("FIRST", "SECOND"))
        bound = _role(rule, "MAX_DELAY")
        if first and second and isinstance(bound, int) and 1 <= bound <= 64:
            history = " || ".join(
                [f"({first})"] + [f"$past(({first}), {delay})" for delay in range(1, bound + 1)]
            )
            return f"({second}) |-> ({history})", {
                "FIRST": first, "SECOND": second, "MAX_DELAY": bound,
            }
    elif primitive == "CONSERVATION":
        before, after = (_expr(_role(rule, key)) for key in ("BEFORE", "AFTER"))
        condition = _expr(_role(rule, "CONDITION")) or "1'b1"
        if before and after:
            return f"({condition}) |=> ({after}) == $past({before})", {"CONDITION": condition, "BEFORE": before, "AFTER": after}
    return None


def _rules(contract: ContractIR) -> list[dict[str, Any]]:
    result = list(contract.invariants)
    named = {
        "UPDATE": contract.update_rules, "HOLD": contract.hold_rules,
        "ORDERING": contract.ordering, "CAUSALITY": contract.causality,
        "STABILITY": contract.stability, "DATA_INTEGRITY": contract.data_integrity,
        "MUTUAL_EXCLUSION": contract.mutual_exclusion, "RESET": contract.reset_behavior,
    }
    for primitive, rules in named.items():
        for rule in rules:
            copied = dict(rule)
            copied.setdefault("primitive", primitive)
            result.append(copied)
    deduplicated = []
    seen: set[str] = set()
    for rule in result:
        primitive = str(rule.get("primitive", "")).upper()
        key = json.dumps(
            {"primitive": primitive, "roles": rule.get("roles", {})},
            sort_keys=True,
            ensure_ascii=True,
        )
        if key in seen:
            continue
        seen.add(key)
        deduplicated.append(rule)
    return deduplicated


def bind_extension_primitives(
    contracts: list[ContractIR],
    module_signals: dict[str, set[str]],
    reset_asserted: str,
) -> tuple[list[PropertyIR], list[TemplateBindingIR]]:
    properties: list[PropertyIR] = []
    bindings: list[TemplateBindingIR] = []
    for contract in contracts:
        if contract.ontology_classification != "NEW_OBJECT_CANDIDATE":
            continue
        known = module_signals.get(contract.module, set())
        for index, rule in enumerate(_rules(contract), start=1):
            primitive = str(rule.get("primitive", "")).upper()
            binding_id = f"binding_{contract.region}_{index}"
            if primitive not in PRIMITIVES:
                bindings.append(TemplateBindingIR(binding_id, contract.contract_id, contract.region, contract.object_type, contract.ontology_classification, 3, primitive or "UNSPECIFIED", "", {}, "REJECTED", "unknown primitive; use NEW_PROPERTY_FAMILY_CANDIDATE instead"))
                continue
            compiled = _compile(primitive, rule)
            if not compiled:
                bindings.append(TemplateBindingIR(binding_id, contract.contract_id, contract.region, contract.object_type, contract.ontology_classification, 2, primitive, f"PRIMITIVE_{primitive}", {}, "REJECTED", "missing or invalid semantic roles"))
                continue
            body, roles = compiled
            referenced = expression_signals(body)
            invalid = referenced - known
            if invalid:
                bindings.append(TemplateBindingIR(binding_id, contract.contract_id, contract.region, contract.object_type, contract.ontology_classification, 2, primitive, f"PRIMITIVE_{primitive}", roles, "REJECTED", f"roles reference signals outside module evidence: {sorted(invalid)}"))
                continue
            property_id = re.sub(r"[^a-z0-9_]+", "_", f"{contract.region}_primitive_{primitive.lower()}_{index}".lower())
            disable_iff = None if primitive == "RESET" else reset_asserted
            prop = PropertyIR(
                property_id=property_id,
                region_id=contract.region,
                object_type=ObjectType.EXTENSION,
                family=f"PRIMITIVE_{primitive}",
                template=primitive,
                bindings=roles,
                signals=sorted(referenced),
                source="llm-contract+primitive-template",
                llm_confidence=float(rule.get("confidence", 0.0)),
                body=body,
                disable_iff=disable_iff,
                description=str(rule.get("semantics", f"Extension contract expressed with {primitive}.")),
                source_classification=PropertySource.LLM_HYPOTHESIS.value,
                evidence=contract.evidence,
                target_module=contract.module,
            )
            properties.append(prop)
            bindings.append(TemplateBindingIR(binding_id, contract.contract_id, contract.region, contract.object_type, contract.ontology_classification, 2, primitive, prop.family, roles, "BOUND", property_id=property_id))
    return properties, bindings


def core_template_bindings(contracts: list[ContractIR], properties: list[PropertyIR]) -> list[TemplateBindingIR]:
    by_region: dict[str, list[PropertyIR]] = {}
    for prop in properties:
        if prop.object_type != ObjectType.EXTENSION:
            by_region.setdefault(prop.region_id, []).append(prop)
    result = []
    for contract in contracts:
        if contract.ontology_classification != "CORE_OBJECT":
            continue
        props = by_region.get(contract.region, [])
        if not props:
            result.append(TemplateBindingIR(f"binding_{contract.region}_none", contract.contract_id, contract.region, contract.object_type, contract.ontology_classification, 1, "OBJECT_TEMPLATE", "", {}, "NO_SAFE_BINDING", "validated object has no sufficiently evidenced deterministic template binding"))
        for index, prop in enumerate(props, start=1):
            result.append(TemplateBindingIR(f"binding_{contract.region}_{index}", contract.contract_id, contract.region, contract.object_type, contract.ontology_classification, 1, "OBJECT_TEMPLATE", prop.family, prop.bindings, "BOUND", property_id=prop.property_id))
    return result
