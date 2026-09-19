"""Requirement 8.3 obligation-gap-aware initial property portfolio planner."""

from __future__ import annotations

from collections import Counter
from math import ceil, sqrt
from typing import Any

from dateassertion.pipeline.property_portfolio_planner import (
    PortfolioCandidate,
    _inventory,
    _statistics,
    build_property_candidate_pool,
)
from dateassertion.pipeline.verification_obligations import build_applicability_matrix


def _select(
    candidates: list[PortfolioCandidate],
    *,
    max_properties: int,
    min_utility: float,
    force_budget: bool,
    applicable_pairs: set[tuple[str, str]],
    prior_trusted_pairs: set[tuple[str, str]],
    obligation_gap_bonus: float = 16.0,
    obligation_saturation_penalty: float = 4.0,
    prior_trusted_saturation_penalty: float = 2.0,
) -> tuple[list[PortfolioCandidate], dict[str, dict[str, Any]], str, list[dict[str, Any]]]:
    """Req8.2 greedy selection plus explicit obligation gap/saturation terms."""

    selected: list[PortfolioCandidate] = []
    remaining = list(candidates)
    covered: set[str] = set()
    obligation_counts: Counter[tuple[str, str]] = Counter()
    global_obligation_counts: Counter[str] = Counter()
    region_counts: Counter[str] = Counter()
    module_counts: Counter[str] = Counter()
    family_counts: Counter[str] = Counter()
    scope_counts: Counter[str] = Counter()
    audit: dict[str, dict[str, Any]] = {}
    curve: list[dict[str, Any]] = []
    stop_reason = "MAX_PROPERTIES_REACHED"
    while remaining and len(selected) < max_properties:
        ranked = []
        for item in remaining:
            pair = (item.region_id, item.obligation)
            scope = set(item.structural_scope)
            new_scope = scope - covered
            max_overlap = max(
                (len(scope & set(other.structural_scope)) / max(1, len(scope | set(other.structural_scope))) for other in selected),
                default=0.0,
            )
            pair_count = obligation_counts[pair]
            gap_open = pair in applicable_pairs and pair not in prior_trusted_pairs and pair_count == 0
            # Every Req8.2 term remains present.  The final two named terms are
            # the only ranking additions made by Requirement 8.3.
            components = {
                "base_static_value": item.static_coverage_score,
                "new_structural_scope": min(28.0, 2.5 * len(new_scope)),
                "obligation_novelty": 18.0 / (1 + pair_count),
                "obligation_diversity": 12.0 / (1 + global_obligation_counts[item.obligation]),
                "region_completion": 8.0 if region_counts[item.region_id] and pair_count == 0 else 0.0,
                "region_novelty": 8.0 / (1 + region_counts[item.region_id]),
                "family_diversity": 12.0 / (1 + family_counts[item.primitive]),
                "scope_diversity": 8.0 / (1 + scope_counts[item.scope]),
                "cross_region_value": 6.0 if item.scope == "CROSS_REGION" else 0.0,
                "semantic_path_value": 5.0 if item.semantic_path else 0.0,
                "overlap_penalty": -22.0 * max_overlap,
                "region_saturation_penalty": -2.5 * region_counts[item.region_id],
                "module_saturation_penalty": -0.8 * module_counts[item.module],
                "obligation_gap_bonus": obligation_gap_bonus if gap_open else 0.0,
                "obligation_saturation_penalty": (
                    -obligation_saturation_penalty * pair_count
                    - (prior_trusted_saturation_penalty if pair in prior_trusted_pairs else 0.0)
                ),
            }
            utility = round(sum(components.values()), 3)
            ranked.append((utility, item.proofability_score, item.candidate_id, item, components, max_overlap, gap_open))
        utility, _proof, _candidate_id, best, components, max_overlap, gap_open = max(ranked)
        if not force_budget and utility < min_utility:
            stop_reason = "LOW_MARGINAL_GAIN"
            break
        rank = len(selected) + 1
        new_scope_items = len(set(best.structural_scope) - covered)
        audit[best.candidate_id] = {
            "selected": True,
            "selection_rank": rank,
            "marginal_utility": utility,
            "marginal_components": {key: round(value, 3) for key, value in components.items()},
            "new_structural_scope_items": new_scope_items,
            "selection_reason": "highest Req8.2 utility plus obligation gap minus obligation saturation",
            "fills_prior_trusted_obligation_gap": gap_open,
        }
        curve.append({
            "property_rank": rank,
            "candidate_id": best.candidate_id,
            "region_id": best.region_id,
            "family": best.primitive,
            "obligation": best.obligation,
            "marginal_utility": utility,
            "estimated_structural_gain": new_scope_items,
            "obligation_gap_contribution": components["obligation_gap_bonus"],
            "obligation_saturation_penalty": components["obligation_saturation_penalty"],
            "proofability": best.proofability_score,
            "overlap_penalty": round(components["overlap_penalty"], 3),
            "max_overlap": round(max_overlap, 6),
        })
        selected.append(best)
        covered.update(best.structural_scope)
        pair = (best.region_id, best.obligation)
        obligation_counts[pair] += 1
        global_obligation_counts[best.obligation] += 1
        region_counts[best.region_id] += 1
        module_counts[best.module] += 1
        family_counts[best.primitive] += 1
        scope_counts[best.scope] += 1
        remaining.remove(best)
    for item in remaining:
        scope = set(item.structural_scope)
        overlap = max(
            (len(scope & set(other.structural_scope)) / max(1, len(scope | set(other.structural_scope))) for other in selected),
            default=0.0,
        )
        if overlap >= 0.80:
            reason = "OVERLAP_FILTERED"
        elif item.proofability_score < 0.45:
            reason = "LOW_SCORE"
        elif item.vacuity_risk > 0.65:
            reason = "LOW_SCORE"
        elif stop_reason == "LOW_MARGINAL_GAIN":
            reason = "LOW_SCORE"
        else:
            reason = "BUDGET_FILTERED"
        audit[item.candidate_id] = {
            "selected": False,
            "selection_rank": None,
            "marginal_utility": None,
            "marginal_components": {},
            "new_structural_scope_items": len(scope - covered),
            "selection_reason": reason,
            "fills_prior_trusted_obligation_gap": False,
        }
    if not remaining:
        stop_reason = "CANDIDATE_POOL_EXHAUSTED"
    return selected, audit, stop_reason, curve


def plan_obligation_aware_portfolios(
    design: Any,
    graph: dict[str, Any],
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    config: dict[str, Any] | None = None,
    historical_coverage_items: list[Any] | None = None,
    prior_trusted_pairs: set[tuple[str, str]] | None = None,
) -> dict[str, Any]:
    cfg = config or {}
    planner = cfg.get("planner", cfg)
    candidates, rejected, pool = build_property_candidate_pool(
        design, graph, design_map, regions_doc, config, historical_coverage_items
    )
    applicability = build_applicability_matrix(regions_doc, candidates)
    applicable_pairs = {tuple(item) for item in applicability["applicable_region_obligation_pairs"]}
    prior_trusted_pairs = set(prior_trusted_pairs or ()) & applicable_pairs
    gap_bonus = float(planner.get("obligation_gap_bonus", 16.0))
    saturation_penalty = float(planner.get("obligation_saturation_penalty", 4.0))
    prior_saturation_penalty = float(planner.get("prior_trusted_saturation_penalty", 2.0))
    select_kwargs = {
        "applicable_pairs": applicable_pairs,
        "prior_trusted_pairs": prior_trusted_pairs,
        "obligation_gap_bonus": gap_bonus,
        "obligation_saturation_penalty": saturation_penalty,
        "prior_trusted_saturation_penalty": prior_saturation_penalty,
    }
    fixed_budget = min(int(planner.get("fixed_budget", 83)), len(candidates))
    fixed, fixed_audit, fixed_stop, fixed_curve = _select(
        candidates, max_properties=fixed_budget, min_utility=float("-inf"), force_budget=True,
        **select_kwargs,
    )
    node_count = max(1, int(graph.get("node_count", len(graph.get("nodes", [])))))
    computed_cap = ceil(sqrt(node_count) * float(planner.get("dynamic_scale_factor", 1.55)))
    dynamic_cap = min(
        int(planner.get("max_properties", 160)), max(fixed_budget + 1, computed_cap), len(candidates)
    )
    expanded, expanded_audit, expanded_stop, expanded_curve = _select(
        candidates, max_properties=dynamic_cap,
        min_utility=float(planner.get("min_marginal_utility", 34.0)), force_budget=False,
        **select_kwargs,
    )
    analysis_cap = min(int(planner.get("analysis_cap", 260)), len(candidates))
    _analysis, _analysis_audit, analysis_stop, analysis_curve = _select(
        candidates, max_properties=analysis_cap,
        min_utility=float(planner.get("analysis_min_marginal_utility", 34.0)), force_budget=False,
        **select_kwargs,
    )
    if len(expanded) <= len(fixed) and len(candidates) > len(fixed):
        raise RuntimeError("Requirement 8.3 dynamic portfolio did not expand beyond equal budget")
    relative_stop_fraction = float(planner.get("analysis_relative_stop_fraction", 0.55))
    relative_stop_point = next(
        (
            row["property_rank"] for row in analysis_curve
            if analysis_curve and row["marginal_utility"] <= analysis_curve[0]["marginal_utility"] * relative_stop_fraction
        ),
        None,
    )
    threshold_stop_point = len(analysis_curve) + 1 if analysis_stop == "LOW_MARGINAL_GAIN" else None
    recommended_stop = threshold_stop_point or relative_stop_point
    parameters = {
        "fixed_budget": fixed_budget,
        "dynamic_scale_factor": float(planner.get("dynamic_scale_factor", 1.55)),
        "computed_dynamic_cap": computed_cap,
        "dynamic_cap": dynamic_cap,
        "min_marginal_utility": float(planner.get("min_marginal_utility", 34.0)),
        "analysis_cap": analysis_cap,
        "analysis_min_marginal_utility": float(planner.get("analysis_min_marginal_utility", 34.0)),
        "obligation_gap_bonus": gap_bonus,
        "obligation_saturation_penalty_per_existing_selection": saturation_penalty,
        "prior_trusted_saturation_penalty": prior_saturation_penalty,
        "property_family_quotas": None,
        "cross_region_quota": None,
    }
    return {
        "schema": "region_flow.3-obligation-aware-property-plan.v1",
        "strategy": "candidate_planning-hub-novelty-proofability-plus-obligation-gap-saturation",
        "strategy_parameters": parameters,
        "candidate_pool": pool,
        "obligation_applicability": applicability,
        "prior_trusted_region_obligation_pairs": [list(item) for item in sorted(prior_trusted_pairs)],
        "fixed_budget": {
            "contracts": [item.contract for item in fixed],
            "selection_order": [item.candidate_id for item in fixed],
            "statistics": {**_statistics(candidates, fixed, fixed_stop), "obligation_gaps_selected": sum(row["obligation_gap_contribution"] > 0 for row in fixed_curve)},
            "candidates": _inventory(candidates, fixed_audit, "REQ8_3_EQUAL_BUDGET"),
            "marginal_utility_curve": fixed_curve,
        },
        "expanded": {
            "contracts": [item.contract for item in expanded],
            "selection_order": [item.candidate_id for item in expanded],
            "statistics": {**_statistics(candidates, expanded, expanded_stop), "obligation_gaps_selected": sum(row["obligation_gap_contribution"] > 0 for row in expanded_curve)},
            "candidates": _inventory(candidates, expanded_audit, "REQ8_3_EXPANDED"),
            "marginal_utility_curve": expanded_curve,
        },
        "selection_analysis": {
            "cap": analysis_cap,
            "selected_until_stop": len(analysis_curve),
            "stop_reason": analysis_stop,
            "threshold": float(planner.get("analysis_min_marginal_utility", 34.0)),
            "threshold_stop_point": threshold_stop_point,
            "relative_stop_fraction": relative_stop_fraction,
            "relative_stop_point": relative_stop_point,
            "marginal_utility_stop_point": recommended_stop,
            "marginal_utility_stop_method": (
                "ABSOLUTE_THRESHOLD" if threshold_stop_point else
                "RELATIVE_TO_RANK_1" if relative_stop_point else
                "NOT_OBSERVED_WITHIN_ANALYSIS_CAP"
            ),
            "curve": analysis_curve,
        },
        "enumeration_rejections": rejected,
    }
