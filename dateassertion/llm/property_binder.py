"""Bind fixed property templates to validated semantic roles."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from dateassertion.ir.schema import MicroarchitectureIR, ObjectType, PropertyIR, PropertySource
from dateassertion.ontology.property_families import PropertyFamily


def _signal(value: Any) -> str | None:
    return value if isinstance(value, str) and re.match(r"^[A-Za-z_][\w$]*$", value) else None


def _signals(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value] if _signal(value) else []
    if isinstance(value, list):
        return [item for item in value if _signal(item)]
    return []


def _expression_signals(value: str) -> list[str]:
    without_literals = re.sub(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+", " ", value)
    without_literals = re.sub(r"`[A-Za-z_][A-Za-z0-9_$]*", " ", without_literals)
    ignored = {"past", "stable", "inside", "true", "false"}
    return [name for name in re.findall(r"[A-Za-z_][\w$]*", without_literals) if name not in ignored]


def _expand_macros(value: str, macros: dict[str, str]) -> str:
    result = value
    for _ in range(8):
        expanded = re.sub(
            r"`([A-Za-z_][A-Za-z0-9_$]*)",
            lambda match: f"({macros[match.group(1)]})" if match.group(1) in macros else match.group(0),
            result,
        )
        if expanded == result:
            break
        result = expanded
    return result


def _id(region_id: str, family: PropertyFamily, index: int = 1) -> str:
    stem = family.value.lower()
    return re.sub(r"[^a-z0-9_]+", "_", f"{region_id}_{stem}_{index}")


def _spec_text(region) -> str:
    chunks = []
    for value in region.evidence.correctness_sources:
        try:
            chunks.append(Path(value).read_text(encoding="utf-8", errors="replace"))
        except OSError:
            continue
    return "\n".join(chunks)


def _source(region, role_signal: str | None = None) -> str:
    text = _spec_text(region)
    supported = bool(text and (not role_signal or re.search(rf"\b{re.escape(role_signal)}\b", text)))
    if supported and role_signal and region.type == ObjectType.REGISTER_UPDATE:
        supported = any(
            re.search(rf"\b{re.escape(role_signal)}\b", line)
            and re.search(r"\b(record|update|reset|register)", line, re.I)
            for line in text.splitlines()
        )
    if supported and role_signal and region.type == ObjectType.DATAPATH:
        supported = any(
            re.search(rf"\b{re.escape(role_signal)}\b", line)
            and re.search(r"\b(is|equals?|result|compute)", line, re.I)
            for line in text.splitlines()
        )
    if supported:
        return "spec+template"
    return "rtl-evidence+template"


def _state_values(states: Any, macros: dict[str, str] | None = None) -> list[str]:
    if not isinstance(states, dict):
        return []
    literal = re.compile(r"^(?:`[A-Za-z_][A-Za-z0-9_$]*|\d+|(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+)$")
    definitions = macros or {}
    def state_literal(value: Any) -> str:
        expanded = _expand_macros(str(value).strip(), definitions)
        while expanded.startswith("(") and expanded.endswith(")") and expanded.count("(") == expanded.count(")") == 1:
            expanded = expanded[1:-1].strip()
        return expanded

    values = [state_literal(value) for value in states.values()]
    if values and all(literal.fullmatch(value) for value in values):
        return values
    keys = [state_literal(key) for key in states]
    if keys and all(literal.fullmatch(key) for key in keys):
        return keys
    return []


def _make(region, family: PropertyFamily, template: str, bindings: dict[str, Any], signals: list[str], body: str, description: str, index: int = 1, disable_iff: str | None = "!resetn", role_signal: str | None = None) -> PropertyIR:
    source = _source(region, role_signal)
    return PropertyIR(
        property_id=_id(region.region_id, family, index),
        region_id=region.region_id,
        object_type=region.type,
        family=family.value,
        template=template,
        bindings=bindings,
        signals=sorted(set(signals)),
        source=source,
        llm_confidence=region.confidence,
        body=body,
        disable_iff=disable_iff,
        description=description,
        source_classification=(
            PropertySource.SPEC_BACKED.value if source == "spec+template"
            else PropertySource.RTL_STRUCTURAL.value
        ),
        evidence=[{
            "files": region.evidence.rtl_files,
            "line_start": region.evidence.line_start,
            "line_end": region.evidence.line_end,
            "region_id": region.region_id,
        }],
        target_module=region.module,
    )


def bind_properties(
    ir: MicroarchitectureIR,
    reset: str = "resetn",
    reset_active_low: bool = True,
    macro_definitions: dict[str, str] | None = None,
) -> list[PropertyIR]:
    reset_asserted = f"!{reset}" if reset_active_low else reset
    macros = macro_definitions or {}
    properties: list[PropertyIR] = []
    for region in ir.regions:
        if region.type == ObjectType.FSM:
            state = _signal(region.signals.get("state")) or _signal(region.details.get("state_variable"))
            states = region.details.get("states", {})
            values = _state_values(states, macros)
            if state and values:
                literal_set = ", ".join(dict.fromkeys(str(value) for value in values))
                properties.append(_make(
                    region, PropertyFamily.FSM_LEGAL_STATE, "STATE inside {LEGAL_STATES}",
                    {"STATE": state, "LEGAL_STATES": values}, [state],
                    f"{state} inside {{{literal_set}}}", "State remains in the enumerated legal set.",
                    disable_iff=reset_asserted, role_signal=state,
                ))
                reset_state = region.details.get("reset_state")
                if isinstance(reset_state, str) and reset_state in states:
                    reset_state = states[reset_state]
                if not reset_state:
                    reset_state = next((value for name, value in states.items() if "reset" in name.lower() or "idle" in name.lower() or "fetch" in name.lower()), None)
                if reset_state:
                    reset_state = _expand_macros(str(reset_state), macros)
                    properties.append(_make(
                        region, PropertyFamily.FSM_RESET_STATE, "RESET |=> STATE == RESET_STATE",
                        {"RESET": reset_asserted, "STATE": state, "RESET_STATE": reset_state}, [state],
                        f"({reset_asserted}) |=> {state} == {reset_state}", "Reset drives the documented initial state.",
                        disable_iff=None, role_signal=state,
                    ))

        elif region.type in {ObjectType.HANDSHAKE, ObjectType.REQUEST_RESPONSE}:
            request = _signal(region.signals.get("request")) or _signal(region.details.get("request"))
            response = _signal(region.signals.get("response")) or _signal(region.details.get("response"))
            payload = _signals(region.signals.get("payload")) or _signals(region.details.get("payload"))
            spec = _spec_text(region)
            if spec:
                # A response payload (for example read data) must not be
                # constrained by a request-payload stability contract.
                payload = [item for item in payload if re.search(rf"\b{re.escape(item)}\b", spec)]
            if request and response:
                persistence_family = (
                    PropertyFamily.REQUEST_RESPONSE_PERSISTENCE
                    if region.type == ObjectType.REQUEST_RESPONSE
                    else PropertyFamily.HANDSHAKE_PERSISTENCE
                )
                properties.append(_make(
                    region, persistence_family,
                    "REQUEST && !COMPLETION |=> REQUEST",
                    {"REQUEST": request, "COMPLETION": response}, [request, response],
                    f"{request} && !{response} |=> {request}", "An unaccepted request persists.",
                    disable_iff=reset_asserted, role_signal=request,
                ))
                if payload:
                    concat = "{" + ", ".join(payload) + "}"
                    properties.append(_make(
                        region, PropertyFamily.HANDSHAKE_PAYLOAD_STABILITY,
                        "REQUEST && !COMPLETION |=> stable(PAYLOAD)",
                        {"REQUEST": request, "COMPLETION": response, "PAYLOAD": payload},
                        [request, response, *payload],
                        f"{request} && !{response} |=> $stable({concat})", "Payload is stable while stalled.",
                        disable_iff=reset_asserted, role_signal=request,
                    ))

        elif region.type == ObjectType.RESOURCE:
            grants = _signals(region.signals.get("grants")) or _signals(region.details.get("grants"))
            owner = _signal(region.signals.get("owner")) or _signal(region.details.get("owner"))
            labels = _state_values(
                {str(index): value for index, value in enumerate(region.details.get("case_labels", []))},
                macros,
            )
            if len(grants) >= 2:
                payload = "{" + ", ".join(grants) + "}"
                properties.append(_make(
                    region, PropertyFamily.RESOURCE_MUTUAL_EXCLUSION,
                    "onehot0(GRANTS)", {"GRANTS": grants}, grants,
                    f"$onehot0({payload})", "At most one resource grant is active.",
                    disable_iff=reset_asserted, role_signal=grants[0],
                ))
            elif owner and labels:
                legal = ", ".join(dict.fromkeys(labels))
                properties.append(_make(
                    region, PropertyFamily.RESOURCE_OWNERSHIP,
                    "OWNER inside {LEGAL_OWNERS}", {"OWNER": owner, "LEGAL_OWNERS": labels}, [owner],
                    f"{owner} inside {{{legal}}}", "Encoded resource owner remains legal.",
                    disable_iff=reset_asserted, role_signal=owner,
                ))

        elif region.type == ObjectType.REGISTER_UPDATE:
            register = _signal(region.signals.get("register")) or _signal(region.details.get("register"))
            enable_value = region.details.get("enable")
            if enable_value is None and isinstance(region.details.get("assignments"), list):
                update_expression = region.details.get("update_expression")
                enable_value = next(
                    (
                        item.get("guard")
                        for item in region.details["assignments"]
                        if isinstance(item, dict) and item.get("rhs") == update_expression and item.get("guard")
                    ),
                    None,
                )
            enable = _expand_macros(str(enable_value or "1'b1"), macros)
            expression = region.details.get("update_expression")
            reset_value = region.details.get("reset_value")
            if isinstance(expression, str):
                expression = _expand_macros(expression, macros)
            if reset_value is not None:
                reset_value = _expand_macros(str(reset_value), macros)
            dependencies = _signals(region.details.get("operands"))
            if not dependencies and isinstance(expression, str):
                dependencies = [name for name in _expression_signals(expression) if name != register]
            dependencies.extend(_expression_signals(enable))
            assignment_records = [
                item for item in region.details.get("assignments", []) if isinstance(item, dict)
            ]
            same_guard_updates = {
                str(item.get("rhs")) for item in assignment_records
                if str(item.get("guard", "")) == str(enable_value or "1'b1")
            }
            ambiguous_guard = len(same_guard_updates) > 1
            if register and isinstance(expression, str) and expression not in {"'bx", "'x"} and not ambiguous_guard:
                properties.append(_make(
                    region, PropertyFamily.REGISTER_ENABLE_UPDATE,
                    "ENABLE |=> REGISTER == past(UPDATE_EXPRESSION)",
                    {"ENABLE": enable, "REGISTER": register, "UPDATE_EXPRESSION": expression},
                    [register, *dependencies],
                    f"({enable}) |=> {register} == $past({expression})", "Enabled register update follows the local contract.",
                    disable_iff=reset_asserted, role_signal=register,
                ))
            hold_assignment = next(
                (
                    item for item in assignment_records
                    if item.get("rhs") == register and item.get("guard")
                ),
                None,
            )
            if register and hold_assignment:
                hold = _expand_macros(str(hold_assignment["guard"]), macros)
                properties.append(_make(
                    region, PropertyFamily.REGISTER_DISABLE_HOLD,
                    "HOLD |=> stable(REGISTER)", {"HOLD": hold, "REGISTER": register},
                    [register, *_expression_signals(hold)],
                    f"({hold}) |=> $stable({register})", "An explicit RTL self-hold branch preserves the register.",
                    disable_iff=reset_asserted, role_signal=register,
                ))
            if register and reset_value is not None:
                properties.append(_make(
                    region, PropertyFamily.REGISTER_RESET_VALUE,
                    "RESET |=> REGISTER == RESET_VALUE",
                    {"RESET": reset_asserted, "REGISTER": register, "RESET_VALUE": reset_value}, [register],
                    f"({reset_asserted}) |=> {register} == {reset_value}", "Reset establishes the documented value.",
                    disable_iff=None, role_signal=register,
                ))

        elif region.type == ObjectType.DATAPATH:
            result = _signal(region.signals.get("result")) or _signal(region.details.get("result"))
            expression = region.details.get("expression")
            if isinstance(expression, str):
                expression = _expand_macros(expression, macros)
            operands = _signals(region.signals.get("operands")) or _signals(region.details.get("operands"))
            operation_select = _signal(region.signals.get("operation_select")) or _signal(region.details.get("operation_select"))
            # Datapath equivalence needs intent beyond the RTL itself.
            if result and isinstance(expression, str) and _source(region, result) == "spec+template":
                properties.append(_make(
                    region, PropertyFamily.DATAPATH_EXPRESSION,
                    "RESULT == EXPECTED_EXPRESSION",
                    {"RESULT": result, "EXPECTED_EXPRESSION": expression}, [result, *operands, *([operation_select] if operation_select else [])],
                    f"{result} == ({expression})", "Datapath result matches the external local contract.",
                    disable_iff=reset_asserted, role_signal=result,
                ))
        elif region.type == ObjectType.PIPELINE:
            transfers = region.details.get("transfers", [])
            stall = _signal(region.signals.get("stall")) or _signal(region.details.get("stall"))
            valid_in = _signal(region.signals.get("valid_in")) or _signal(region.details.get("valid_in"))
            valid_out = _signal(region.signals.get("valid_out")) or _signal(region.details.get("valid_out"))
            for index, transfer in enumerate(transfers, start=1):
                if not isinstance(transfer, dict):
                    continue
                input_signal = _signal(transfer.get("input"))
                output_signal = _signal(transfer.get("output"))
                if not input_signal or not output_signal:
                    continue
                antecedent = f"!({stall})" if stall else "1'b1"
                signals = [input_signal, output_signal, *([stall] if stall else [])]
                properties.append(_make(
                    region, PropertyFamily.PIPELINE_STAGE_TRANSFER,
                    "TRANSFER_ENABLE |=> OUTPUT == past(INPUT)",
                    {"TRANSFER_ENABLE": antecedent, "INPUT": input_signal, "OUTPUT": output_signal},
                    signals,
                    f"({antecedent}) |=> {output_signal} == $past({input_signal})",
                    "Enabled pipeline transfer preserves stage data/control consistency.",
                    index=index, disable_iff=reset_asserted, role_signal=output_signal,
                ))
            if valid_in and valid_out:
                transfer_enable = f"!({stall})" if stall else "1'b1"
                properties.append(_make(
                    region, PropertyFamily.PIPELINE_VALID_PROPAGATION,
                    "TRANSFER_ENABLE && VALID_IN |=> VALID_OUT",
                    {"TRANSFER_ENABLE": transfer_enable, "VALID_IN": valid_in, "VALID_OUT": valid_out},
                    [valid_in, valid_out, *([stall] if stall else [])],
                    f"({transfer_enable}) && {valid_in} |=> {valid_out}",
                    "Stage validity propagates when the pipeline advances.",
                    disable_iff=reset_asserted, role_signal=valid_out,
                ))
    return properties
