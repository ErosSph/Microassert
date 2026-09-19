"""Normalize core and discovered objects into the Requirement-6 Contract IR."""

from __future__ import annotations

from collections import defaultdict
from typing import Any

from dateassertion.ir.schema import ContractIR, MicroarchitectureIR, ObjectType, RegionIR


PRIMITIVES = {
    "UPDATE", "HOLD", "CAUSALITY", "ORDERING", "STABILITY",
    "DATA_INTEGRITY", "MUTUAL_EXCLUSION", "PERSISTENCE",
    "CONSERVATION", "RESET", "PROGRESS", "BOUNDED_DOMINANCE",
    "CONTROL_ASSERT", "CONTROL_DEASSERT",
    "STATE_LEGAL", "ONEHOT_STATE",
    "INDEXED_READ", "INDEXED_WRITE",
    "ONEHOT_STEP",
}

CORE_PRIMITIVES = {
    ObjectType.FSM: ["RESET", "HOLD", "PROGRESS"],
    ObjectType.REGISTER_UPDATE: ["UPDATE", "HOLD", "RESET"],
    ObjectType.DATAPATH: ["DATA_INTEGRITY", "STABILITY"],
    ObjectType.PIPELINE: ["DATA_INTEGRITY", "HOLD", "STABILITY"],
    ObjectType.DECODE: ["DATA_INTEGRITY", "MUTUAL_EXCLUSION"],
    ObjectType.HANDSHAKE: ["PERSISTENCE", "STABILITY", "CAUSALITY", "PROGRESS"],
    ObjectType.REQUEST_RESPONSE: ["PERSISTENCE", "CAUSALITY", "PROGRESS"],
    ObjectType.RESOURCE: ["MUTUAL_EXCLUSION", "CONSERVATION"],
}


def _strings(value: Any) -> list[str]:
    if isinstance(value, str):
        return [value]
    if isinstance(value, list):
        return [str(item) for item in value if isinstance(item, str)]
    if isinstance(value, dict):
        return [str(item) for item in value.values() if isinstance(item, str)]
    return []


def _rules(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        return [value]
    if isinstance(value, list):
        return [item for item in value if isinstance(item, dict)]
    return []


def _extension_payload(region: RegionIR) -> dict[str, Any]:
    payload = region.details.get("extension_candidate", {})
    return payload if isinstance(payload, dict) else {}


def _core_contract(region: RegionIR) -> ContractIR:
    details = region.details
    inputs = _strings(region.signals.get("inputs"))
    outputs = _strings(region.signals.get("outputs"))
    if not inputs and region.type == ObjectType.DATAPATH:
        inputs = _strings(region.signals.get("operands"))
    if not outputs and region.type == ObjectType.DATAPATH:
        outputs = _strings(region.signals.get("result"))
    if region.type == ObjectType.HANDSHAKE:
        inputs = list(dict.fromkeys(inputs + _strings(region.signals.get("request")) + _strings(region.signals.get("payload"))))
        outputs = list(dict.fromkeys(outputs + _strings(region.signals.get("response"))))
    if region.type == ObjectType.REQUEST_RESPONSE:
        inputs = list(dict.fromkeys(inputs + _strings(region.signals.get("request"))))
        outputs = list(dict.fromkeys(outputs + _strings(region.signals.get("response"))))
    return ContractIR(
        contract_id=f"contract_{region.region_id}",
        object_type=region.type.value,
        ontology_classification="CORE_OBJECT",
        region=region.region_id,
        module=region.module,
        state=_strings(region.signals.get("state")) or _strings(details.get("state_variable")),
        events=dict(region.events),
        inputs=inputs,
        outputs=outputs,
        dependencies={str(k): _strings(v) for k, v in details.get("dependencies", {}).items()} if isinstance(details.get("dependencies"), dict) else {},
        invariants=_rules(details.get("invariants")),
        update_rules=_rules(details.get("update_rules")),
        hold_rules=_rules(details.get("hold_rules")),
        ordering=_rules(details.get("ordering")),
        causality=_rules(details.get("causality")),
        stability=_rules(details.get("stability")),
        data_integrity=_rules(details.get("data_integrity")),
        mutual_exclusion=_rules(details.get("mutual_exclusion")),
        reset_behavior=_rules(details.get("reset_behavior")),
        assumptions=_rules(details.get("assumptions")),
        evidence=[{
            "files": region.evidence.rtl_files,
            "line_start": region.evidence.line_start,
            "line_end": region.evidence.line_end,
            "snippet": region.evidence.snippet,
        }],
        reused_primitives=CORE_PRIMITIVES.get(region.type, []),
    )


def _extension_contract(region: RegionIR) -> ContractIR:
    payload = _extension_payload(region)
    invariants = _rules(payload.get("invariants"))
    reused = []
    for invariant in invariants:
        primitive = str(invariant.get("primitive", "")).upper()
        if primitive in PRIMITIVES and primitive not in reused:
            reused.append(primitive)
    for name in ("update_rules", "hold_rules", "ordering", "causality", "stability", "data_integrity", "mutual_exclusion", "reset_behavior"):
        if _rules(payload.get(name)):
            primitive = {
                "update_rules": "UPDATE", "hold_rules": "HOLD", "ordering": "ORDERING",
                "causality": "CAUSALITY", "stability": "STABILITY",
                "data_integrity": "DATA_INTEGRITY", "mutual_exclusion": "MUTUAL_EXCLUSION",
                "reset_behavior": "RESET",
            }[name]
            if primitive not in reused:
                reused.append(primitive)
    return ContractIR(
        contract_id=f"contract_{region.region_id}",
        object_type=region.extension_type or str(payload.get("candidate_name") or "UNNAMED_EXTENSION"),
        ontology_classification="NEW_OBJECT_CANDIDATE",
        region=region.region_id,
        module=region.module,
        state=_strings(payload.get("state")),
        events={str(k): v for k, v in payload.get("events", {}).items()} if isinstance(payload.get("events"), dict) else {},
        inputs=_strings(payload.get("inputs")),
        outputs=_strings(payload.get("outputs")),
        dependencies={str(k): _strings(v) for k, v in payload.get("dependencies", {}).items()} if isinstance(payload.get("dependencies"), dict) else {},
        invariants=invariants,
        update_rules=_rules(payload.get("update_rules")),
        hold_rules=_rules(payload.get("hold_rules")),
        ordering=_rules(payload.get("ordering")),
        causality=_rules(payload.get("causality")),
        stability=_rules(payload.get("stability")),
        data_integrity=_rules(payload.get("data_integrity")),
        mutual_exclusion=_rules(payload.get("mutual_exclusion")),
        reset_behavior=_rules(payload.get("reset_behavior")),
        assumptions=_rules(payload.get("assumptions")),
        evidence=[{
            "files": region.evidence.rtl_files,
            "line_start": region.evidence.line_start,
            "line_end": region.evidence.line_end,
            "snippet": region.evidence.snippet,
            "reason": payload.get("reason", ""),
        }],
        reused_primitives=reused,
        new_property_family_candidates=_rules(payload.get("new_property_family_candidates")),
    )


def normalize_contracts(ir: MicroarchitectureIR) -> list[ContractIR]:
    contracts = []
    for region in ir.regions:
        if region.type == ObjectType.UNKNOWN:
            continue
        contracts.append(_extension_contract(region) if region.type == ObjectType.EXTENSION else _core_contract(region))
    return contracts


def ontology_matches(ir: MicroarchitectureIR) -> list[dict[str, Any]]:
    return [
        {
            "region_id": region.region_id,
            "module": region.module,
            "classification": region.ontology_classification,
            "object_type": region.extension_type if region.type == ObjectType.EXTENSION else region.type.value,
            "confidence": region.confidence,
            "evidence": {
                "files": region.evidence.rtl_files,
                "line_start": region.evidence.line_start,
                "line_end": region.evidence.line_end,
            },
            "analysis_source": region.analysis_source,
        }
        for region in ir.regions
    ]
