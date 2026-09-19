"""Rank validated LLM contracts before spending a JasperGold iteration."""

from __future__ import annotations

from typing import Any

from dateassertion.ir.schema import PropertyIR
from dateassertion.rtl_frontend.parser import RTLDesign


def rank_property_candidates(
    contracts: list[dict[str, Any]],
    target_region: dict[str, Any],
    all_regions: list[dict[str, Any]],
    existing: list[PropertyIR],
    design: RTLDesign,
) -> list[dict[str, Any]]:
    uncovered = set(target_region.get("uncovered_signals", []))
    existing_families = {prop.family for prop in existing}
    region_signals = {
        region["region_id"]: set(region.get("uncovered_signals", [])) for region in all_regions
    }
    ranked: list[dict[str, Any]] = []
    for contract in contracts:
        signals = set(contract.get("signals", []))
        uncovered_overlap = len(signals & uncovered)
        new_family = contract.get("family") not in existing_families
        cross_regions = set(contract.get("cross_regions", []))
        inferred_cross = {
            region_id for region_id, other_signals in region_signals.items()
            if region_id != target_region["region_id"] and signals & other_signals
        }
        cross_region = bool(cross_regions | inferred_cross) or contract.get("family") == "CROSS_REGION_CAUSALITY"
        cone = sum(
            assignment.lhs in signals or bool(set(assignment.dependencies) & signals)
            for assignment in design.assignments
        )
        evidence_score = min(2.0, 0.5 * len(contract.get("evidence", [])))
        source_score = {
            "SPEC_BACKED": 2.0,
            "RTL_STRUCTURAL": 1.5,
            "LLM_HYPOTHESIS": 0.0,
        }.get(contract.get("source_classification"), 0.0)
        score = (
            uncovered_overlap * 4.0
            + (3.0 if new_family else 0.0)
            + (4.0 if cross_region else 0.0)
            + min(4.0, cone / 8.0)
            + evidence_score
            + source_score
            + float(contract.get("confidence", 0.0))
        )
        ranked.append(
            {
                **contract,
                "ranking": {
                    "score": round(score, 4),
                    "uncovered_signal_overlap": uncovered_overlap,
                    "new_property_family": new_family,
                    "cross_region": cross_region,
                    "estimated_dependency_cone": cone,
                    "evidence_score": evidence_score,
                    "source_score": source_score,
                },
            }
        )
    return sorted(
        ranked,
        key=lambda contract: (-contract["ranking"]["score"], contract.get("contract_id", "")),
    )
