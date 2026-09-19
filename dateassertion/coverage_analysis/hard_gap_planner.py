"""Select between ordinary reachable regions and recoverable hard-gap clusters."""

from __future__ import annotations

from typing import Any


def rank_coverage_targets(
    region_priority: dict[str, Any],
    hard_gap_clusters: list[dict[str, Any]],
    target_history: list[dict[str, Any]],
    config: dict[str, Any],
) -> dict[str, Any]:
    regions = [
        {
            "target_type": "REGION",
            "target_id": item["region_id"],
            "priority_score": float(item["priority_score"]),
            "eligible": bool(item["eligible"]),
            "payload": item,
            "ineligible_reasons": list(item.get("ineligible_reasons", [])),
        }
        for item in region_priority.get("ranking", [])
    ]
    hard = [
        {
            "target_type": "HARD_GAP",
            "target_id": item["cluster_id"],
            "priority_score": float(item["priority_score"]),
            "eligible": bool(item["recoverable"] and item["status"] != "SATURATED"),
            "payload": item,
            "ineligible_reasons": [] if item["recoverable"] else ["cluster is not recoverable"],
        }
        for item in hard_gap_clusters
    ]
    # Region scores and hard-gap scores use different raw scales. Normalize within
    # each population, retaining each planner's internal ordering.
    for population in (regions, hard):
        maximum = max((item["priority_score"] for item in population if item["eligible"]), default=1.0)
        for item in population:
            item["normalized_score"] = item["priority_score"] / maximum if maximum else 0.0
    min_hard = int(config.get("min_hard_gap_iterations", 1))
    min_region = int(config.get("min_region_iterations", 1))
    hard_done = sum(item.get("target_type") == "HARD_GAP" for item in target_history)
    region_done = sum(item.get("target_type") == "REGION" for item in target_history)
    forced_type = None
    if hard_done < min_hard and any(item["eligible"] for item in hard):
        forced_type = "HARD_GAP"
    elif region_done < min_region and any(item["eligible"] for item in regions):
        forced_type = "REGION"
    max_same = int(config.get("max_consecutive_same_target_type", 2))
    if len(target_history) >= max_same:
        tail = [item.get("target_type") for item in target_history[-max_same:]]
        if len(set(tail)) == 1:
            alternative = "REGION" if tail[0] == "HARD_GAP" else "HARD_GAP"
            pool = regions if alternative == "REGION" else hard
            if any(item["eligible"] for item in pool):
                forced_type = alternative
    ranking = regions + hard
    for item in ranking:
        item["eligible_before_type_gate"] = item["eligible"]
        if forced_type and item["target_type"] != forced_type:
            item["eligible"] = False
            item["ineligible_reasons"].append(f"target-type diversity gate requires {forced_type}")
    ranking.sort(
        key=lambda item: (
            not item["eligible"],
            -item["normalized_score"],
            0 if item["target_type"] == "HARD_GAP" else 1,
            item["target_id"],
        )
    )
    return {
        "schema": "hard-gap-aware-priority.v1",
        "forced_target_type": forced_type,
        "completed_hard_gap_targets": hard_done,
        "completed_region_targets": region_done,
        "ranking": ranking,
    }


def update_hard_gap_state(
    states: dict[str, dict[str, Any]], cluster_id: str, gain: int, outcome: str, config: dict[str, Any]
) -> None:
    state = states.setdefault(cluster_id, {"selection_count": 0, "low_gain_streak": 0, "last_gain": 0, "status": "ACTIVE", "history": []})
    state["selection_count"] += 1
    state["last_gain"] = gain
    state["low_gain_streak"] = state["low_gain_streak"] + 1 if gain < int(config.get("plateau_gain_items", 5)) else 0
    state["history"].append({"gain": gain, "formal_outcome": outcome})
    if outcome in {"CEX", "PROVEN_VACUOUS", "UNKNOWN"}:
        state["status"] = "DEPRIORITIZED"
    if state["low_gain_streak"] >= int(config.get("hard_gap_plateau_rounds", 3)):
        state["status"] = "SATURATED"
