"""Deterministic region coverage map, prioritization, and saturation state."""

from __future__ import annotations

from typing import Any


IMPACT_WEIGHT = {
    "CPU_CONTROL_FSM": 1.45,
    "INSTRUCTION_DECODE": 1.35,
    "PC_BRANCH_CONTROL": 1.40,
    "REGISTER_WRITEBACK": 1.25,
    "ALU_SHIFTER": 1.15,
    "IRQ_TRAP": 1.20,
    "MEMORY_CONTROLLER": 1.10,
    "PCPI": 1.00,
    "OTHER_CONTROL": 0.90,
}


def _state(states: dict[str, dict[str, Any]], region_id: str) -> dict[str, Any]:
    return states.setdefault(
        region_id,
        {
            "selection_count": 0,
            "attempt_count": 0,
            "low_gain_streak": 0,
            "failure_streak": 0,
            "cex_count": 0,
            "vacuous_count": 0,
            "duplicate_count": 0,
            "no_gap_count": 0,
            "last_global_gain": None,
            "last_region_gain": None,
            "status": "ACTIVE",
            "history": [],
        },
    )


def build_region_coverage(
    gap: dict[str, Any], states: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for region in gap.get("regions", []):
        state = _state(states, region["region_id"])
        total_reachable = int(region.get("total_reachable_items", 0))
        covered = int(region.get("covered_elements", 0))
        uncovered = int(region.get("reachable_uncovered_elements", 0))
        result.append(
            {
                "region_id": region["region_id"],
                "region": region["region"],
                "module": region["module"],
                "total_reachable_items": total_reachable,
                "covered_items": covered,
                "uncovered_items": uncovered,
                "reachable_coverage_percent": (
                    round(100.0 * covered / total_reachable, 2) if total_reachable else 0.0
                ),
                "effective_denominator": int(region.get("effective_denominator", 0)),
                "effective_coverage_percent": float(region.get("effective_coverage_percent", 0.0)),
                "existing_properties": len(region.get("existing_properties", [])),
                "existing_property_ids": list(region.get("existing_properties", [])),
                "existing_property_families": list(region.get("existing_property_families", [])),
                "available_property_families": list(region.get("missing_property_families", [])),
                "last_global_marginal_gain": state["last_global_gain"],
                "last_region_marginal_gain": state["last_region_gain"],
                "selection_count": state["selection_count"],
                "failure_streak": state["failure_streak"],
                "low_gain_streak": state["low_gain_streak"],
                "status": state["status"],
                "classification_counts": dict(region.get("classification_counts", {})),
            }
        )
    return sorted(result, key=lambda item: (item["module"], item["region_id"]))


def rank_regions(
    region_coverage: list[dict[str, Any]],
    states: dict[str, dict[str, Any]],
    selected_regions: set[str],
    top_module: str,
    config: dict[str, Any],
) -> dict[str, Any]:
    minimum_distinct = int(config.get("min_distinct_regions", 3))
    diversity_gate = len(selected_regions) < minimum_distinct
    candidates: list[dict[str, Any]] = []
    for region in region_coverage:
        state = _state(states, region["region_id"])
        uncovered = region["uncovered_items"]
        total = max(1, region["total_reachable_items"])
        ratio = uncovered / total
        novelty = 1.6 / (1.0 + 0.65 * state["selection_count"])
        saturation = {"ACTIVE": 1.0, "DEPRIORITIZED": 0.22, "SATURATED": 0.05}.get(
            state["status"], 1.0
        )
        family_factor = 1.0 + min(0.5, 0.08 * len(region["available_property_families"]))
        impact = IMPACT_WEIGHT.get(region["region"], 0.8)
        score = ratio * uncovered * novelty * saturation * family_factor * impact
        eligible = (
            region["module"] == top_module
            and uncovered > 0
            and bool(region["available_property_families"])
            and state["status"] != "SATURATED"
        )
        reasons: list[str] = []
        if region["module"] != top_module:
            reasons.append("outside bind target module")
        if not uncovered:
            reasons.append("no proven-reachable uncovered items")
        if not region["available_property_families"]:
            reasons.append("no unused property family")
        if state["status"] == "SATURATED":
            reasons.append("region saturated")
        if diversity_gate and region["region_id"] in selected_regions:
            eligible = False
            reasons.append("distinct-region diversity gate")
        candidates.append(
            {
                **region,
                "priority_score": round(score, 6),
                "score_factors": {
                    "uncovered_ratio": round(ratio, 6),
                    "uncovered_items": uncovered,
                    "impact": impact,
                    "novelty": round(novelty, 6),
                    "saturation": saturation,
                    "family": round(family_factor, 6),
                },
                "eligible": eligible,
                "ineligible_reasons": reasons,
            }
        )
    if diversity_gate and not any(item["eligible"] for item in candidates):
        for item in candidates:
            only_diversity = item["ineligible_reasons"] == ["distinct-region diversity gate"]
            if only_diversity:
                item["eligible"] = True
                item["ineligible_reasons"] = ["diversity fallback: no unselected region was eligible"]
    candidates.sort(key=lambda item: (-item["priority_score"], item["region_id"]))
    return {
        "schema": "region-priority.v1",
        "minimum_distinct_regions": minimum_distinct,
        "selected_distinct_regions": sorted(selected_regions),
        "diversity_gate_active": diversity_gate,
        "ranking": candidates,
    }


def record_selection(
    states: dict[str, dict[str, Any]], region_id: str, iteration: int, repeated: bool
) -> None:
    state = _state(states, region_id)
    state["selection_count"] += 1
    state["attempt_count"] += 1
    state["history"].append({"iteration": iteration, "event": "SELECTED", "repeated": repeated})
    if repeated:
        state["status"] = "DEPRIORITIZED"


def record_candidate_failure(
    states: dict[str, dict[str, Any]], region_id: str, iteration: int, reason: str,
    config: dict[str, Any]
) -> None:
    state = _state(states, region_id)
    state["attempt_count"] += 1
    if reason == "duplicate":
        state["duplicate_count"] += 1
    else:
        state["no_gap_count"] += 1
    state["failure_streak"] += 1
    state["history"].append({"iteration": iteration, "event": reason.upper()})
    if state["failure_streak"] >= int(config.get("saturation_failure_threshold", 1)):
        state["status"] = "DEPRIORITIZED"
    if state["no_gap_count"] >= int(config.get("saturation_no_gap_threshold", 2)):
        state["status"] = "SATURATED"


def record_formal_outcome(
    states: dict[str, dict[str, Any]], region_id: str, iteration: int,
    global_gain: int, region_gain: int, classification: str, config: dict[str, Any]
) -> None:
    state = _state(states, region_id)
    state["last_global_gain"] = global_gain
    state["last_region_gain"] = region_gain
    low_threshold = int(config.get("region_low_gain_items", 3))
    if region_gain < low_threshold:
        state["low_gain_streak"] += 1
    else:
        state["low_gain_streak"] = 0
    failed = classification in {"CEX", "PROVEN_VACUOUS", "UNKNOWN", "ERROR"}
    if failed:
        state["failure_streak"] += 1
        if classification == "CEX":
            state["cex_count"] += 1
        if classification == "PROVEN_VACUOUS":
            state["vacuous_count"] += 1
    else:
        state["failure_streak"] = 0
    state["history"].append(
        {
            "iteration": iteration,
            "event": "FORMAL_RESULT",
            "classification": classification,
            "global_gain": global_gain,
            "region_gain": region_gain,
        }
    )
    if state["low_gain_streak"] >= int(config.get("saturation_low_gain_rounds", 2)):
        state["status"] = "SATURATED"
    elif state["failure_streak"] >= int(config.get("saturation_failure_threshold", 1)):
        state["status"] = "DEPRIORITIZED"
    else:
        state["status"] = "ACTIVE"


def all_high_priority_saturated(region_coverage: list[dict[str, Any]]) -> bool:
    eligible = [
        region for region in region_coverage
        if region["uncovered_items"] > 0 and region["available_property_families"]
    ]
    return bool(eligible) and all(region["status"] == "SATURATED" for region in eligible)
