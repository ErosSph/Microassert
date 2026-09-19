"""Instantiate validated coverage-gap contracts as deterministic PropertyIR records."""

from __future__ import annotations

import re
from typing import Any

from dateassertion.ir.schema import ObjectType, PropertyIR


HYPOTHESIS_FAMILIES = {
    "DECODE_MUTUAL_EXCLUSION",
    "FSM_FORBIDDEN_TRANSITION",
    "FSM_MUTUAL_EXCLUSION",
    "HANDSHAKE_CAUSALITY",
    "CROSS_REGION_CAUSALITY",
}


def _next_cycle_consequent(contract: dict[str, Any], consequent: str) -> str:
    """Translate sequential assignment RHS sampling into explicit SVA $past semantics."""
    assigned: set[str] = set()
    for evidence in contract.get("evidence", []):
        source = str(evidence.get("source", ""))
        match = re.match(r"\s*([A-Za-z_][A-Za-z0-9_$]*)\s*(?:<=|=)", source)
        if match:
            assigned.add(match.group(1))
    if not assigned:
        return consequent
    result = consequent
    for signal in sorted(set(contract.get("signals", [])) - assigned, key=len, reverse=True):
        indexed = re.compile(rf"(?<!\$past\()\b{re.escape(signal)}\b(\s*\[[^]]+\])")
        result = indexed.sub(lambda match: f"$past({signal}{match.group(1)})", result)
        result = re.sub(
            rf"(?<!\$past\()\b{re.escape(signal)}\b(?!\s*\[)",
            f"$past({signal})",
            result,
        )
    return result


def _object_type(region: str) -> ObjectType:
    if region in {"CPU_CONTROL_FSM", "IRQ_TRAP"}:
        return ObjectType.FSM
    if region in {"MEMORY_CONTROLLER", "PCPI"}:
        return ObjectType.HANDSHAKE
    if region in {"ALU_SHIFTER"}:
        return ObjectType.DATAPATH
    return ObjectType.REGISTER_UPDATE


def bind_gap_contracts(
    contracts: list[dict[str, Any]],
    existing: list[PropertyIR],
    iteration: int,
    reset: str = "resetn",
    reset_active_low: bool = True,
) -> tuple[list[PropertyIR], list[dict[str, Any]]]:
    canonical = {re.sub(r"\s+", "", prop.body) for prop in existing}
    identifiers = {prop.property_id for prop in existing}
    accepted: list[PropertyIR] = []
    rejected: list[dict[str, Any]] = []
    for contract in contracts:
        antecedent = contract["antecedent"]
        consequent = contract["consequent"]
        if contract["temporal_relation"] == "NEXT_CYCLE":
            consequent = _next_cycle_consequent(contract, consequent)
        operator = "|->" if contract["temporal_relation"] == "SAME_CYCLE" else "|=>"
        body = f"({antecedent}) {operator} ({consequent})"
        key = re.sub(r"\s+", "", body)
        if key in canonical:
            rejected.append({"contract": contract, "reason": "duplicate normalized property body"})
            continue
        base = re.sub(r"[^a-z0-9_]+", "_", f"iter{iteration}_{contract['coverage_region_id']}_{contract['family']}".lower()).strip("_")
        property_id = base
        index = 2
        while property_id in identifiers:
            property_id = f"{base}_{index}"
            index += 1
        identifiers.add(property_id)
        canonical.add(key)
        source_classification = contract["source_classification"]
        if contract["family"] in HYPOTHESIS_FAMILIES and source_classification != "SPEC_BACKED":
            source_classification = "LLM_HYPOTHESIS"
        accepted.append(PropertyIR(
            property_id=property_id,
            region_id=contract["anchor_region_id"],
            object_type=_object_type(contract["region"]),
            family=contract["family"],
            template=f"ANTECEDENT {operator} CONSEQUENT",
            bindings={"ANTECEDENT": antecedent, "CONSEQUENT": consequent, "TEMPORAL_RELATION": contract["temporal_relation"]},
            signals=contract["signals"],
            source="coverage-guided-deepseek+validated-evidence",
            llm_confidence=float(contract["confidence"]),
            body=body,
            disable_iff=f"!{reset}" if reset_active_low else reset,
            description=contract["reason"],
            source_classification=source_classification,
            iteration_added=iteration,
            evidence=[{"coverage_region_id": contract["coverage_region_id"], **item} for item in contract["evidence"]],
            target_module=str(contract.get("target_module", "")),
            hard_gap_cluster_id=contract.get("hard_gap_cluster_id"),
            observation_helper_ids=[
                str(item["helper_id"]) for item in contract.get("observation_helpers", [])
            ],
        ))
    return accepted, rejected
