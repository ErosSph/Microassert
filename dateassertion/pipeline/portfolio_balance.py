"""Deterministic bounded selection for Req12 Local candidate bindings.

This module is intentionally independent from the historical Local selector.
It does not use planner scores, LLM output, prior Formal outcomes, or a
predicted coverage gain.  Its only purpose is to limit a large *already
grounded* :class:`LocalCandidateBinding` pool while retaining structural
diversity that can later expose legitimate Contract interfaces.

No property is generated here.  In particular, a deferred binding is neither
an invalid candidate nor an assertion that was generated and rejected.
"""

from __future__ import annotations

from math import ceil
from typing import Any

from dateassertion.pipeline.local_region_assertions import LocalCandidateBinding


SCHEMA = "feedback-balanced-local-bindings.v1"


def _candidate_id(binding: LocalCandidateBinding) -> str:
    return str(binding.candidate.candidate_id)


def _candidate_fields(binding: LocalCandidateBinding) -> dict[str, str]:
    candidate = binding.candidate
    return {
        "candidate_id": _candidate_id(binding),
        "module": str(getattr(candidate, "module", "")),
        "region_kind": str(getattr(candidate, "region_kind", "")),
        "obligation": str(getattr(candidate, "obligation", "") or getattr(candidate, "primitive", "")),
        "candidate_region_id": str(getattr(candidate, "region_id", "")),
        "primitive": str(getattr(candidate, "primitive", "")),
    }


def _structural_producers(binding: LocalCandidateBinding) -> tuple[str, ...]:
    """Return only graph-structural producer anchors, never name heuristics."""

    producer_nodes: set[str] = set(str(item) for item in getattr(binding.candidate, "structural_scope", []) if item)
    for evidence in binding.binding_evidence_by_region.values():
        for edge in evidence.get("typed_edges", []) or []:
            # The evidence originates from typed graph binding.  Its source is
            # a producer endpoint, not a signal-name keyword classification.
            source = str(edge.get("source", ""))
            if source:
                producer_nodes.add(source)
    return tuple(sorted(producer_nodes))


def _frontier_regions(binding: LocalCandidateBinding) -> tuple[str, ...]:
    """Regions with explicit typed *boundary* evidence.

    ``TYPED_COI_PATH`` is useful grounding, but it is not claimed to be a
    cross-region frontier.  This distinction prevents the audit from
    overstating that a Local property will improve composition or coverage.
    """

    return tuple(sorted(
        region_id for region_id, evidence in binding.binding_evidence_by_region.items()
        if str(evidence.get("binding_level", "")) == "TYPED_BOUNDARY"
    ))


def _primary_region(binding: LocalCandidateBinding) -> tuple[str, str]:
    """Choose one actual compatible Region without collapsing compatibility."""

    compatible = tuple(sorted(set(map(str, binding.compatible_region_ids))))
    if not compatible:
        raise ValueError(f"{_candidate_id(binding)} has no compatible Region binding")
    preferred = str(getattr(binding.candidate, "region_id", ""))
    if preferred in compatible:
        return preferred, "CANDIDATE_DECLARED_COMPATIBLE_REGION"

    # If a candidate's declared Region is not compatible, use the strongest
    # *recorded* binding evidence, then shortest typed path, then stable ID.
    # This is deterministic evidence selection, not an inferred equivalence.
    def evidence_order(region_id: str) -> tuple[int, int, str]:
        evidence = binding.binding_evidence_by_region.get(region_id, {})
        return (-int(evidence.get("binding_rank", 0)), int(evidence.get("path_edge_count", 1 << 30)), region_id)

    return min(compatible, key=evidence_order), "STRONGEST_RECORDED_BINDING_EVIDENCE"


def _stable_binding_order(binding: LocalCandidateBinding) -> tuple[str, str, str, str, str]:
    fields = _candidate_fields(binding)
    primary, _ = _primary_region(binding)
    # Candidate ID is the final deterministic tie breaker.  Planner/formal
    # scores intentionally do not occur in this ordering.
    return (fields["module"], fields["region_kind"], fields["obligation"], primary, fields["candidate_id"])


def _validate_inputs(bindings: list[LocalCandidateBinding], budget: int, fraction: float, minimum: int) -> None:
    if budget < 0 or minimum < 0:
        raise ValueError("budget and minimum must be non-negative")
    if not 0.0 <= fraction <= 1.0:
        raise ValueError("fraction must be in [0, 1]")
    for binding in bindings:
        if not isinstance(binding, LocalCandidateBinding):
            raise TypeError("select_balanced_local_bindings requires LocalCandidateBinding instances")
        _primary_region(binding)


def select_balanced_local_bindings(
    bindings: list[LocalCandidateBinding], *, budget: int = 128,
    fraction: float = 0.5, minimum: int = 20,
) -> tuple[list[LocalCandidateBinding], dict[str, Any]]:
    """Select a bounded, structurally diverse grounded Local binding set.

    Target count is ``min(available, budget, max(minimum, ceil(available ×
    fraction)))``.  Selection is greedy but lexicographic, rather than a
    weighted score: it prioritizes new module, region kind, obligation,
    primary Region, typed-boundary frontier, producer anchor, and structural
    scope.  All fields are obtained from the pre-existing graph binding.

    Identical candidate IDs are kept in the audit, but only the first stable
    occurrence is eligible.  Distinct candidate IDs are never semantically
    merged merely because they look similar.
    """

    _validate_inputs(bindings, budget, fraction, minimum)
    ordered = sorted(bindings, key=_stable_binding_order)
    by_id: dict[str, LocalCandidateBinding] = {}
    duplicates: list[LocalCandidateBinding] = []
    for binding in ordered:
        identifier = _candidate_id(binding)
        if identifier in by_id:
            duplicates.append(binding)
        else:
            by_id[identifier] = binding
    eligible = list(by_id.values())
    target = min(len(eligible), int(budget), max(int(minimum), int(ceil(len(eligible) * fraction))))

    # Existing state from a previous selector must not leak into this policy.
    for binding in bindings:
        binding.selected = False
        binding.selection_rank = None
        binding.selection_score = None
        binding.selection_reason = ""

    selected: list[LocalCandidateBinding] = []
    remaining = list(eligible)
    covered_modules: set[str] = set()
    covered_kinds: set[str] = set()
    covered_obligations: set[str] = set()
    covered_regions: set[str] = set()
    covered_frontiers: set[str] = set()
    covered_producers: set[str] = set()
    covered_scope: set[str] = set()
    selection_features: dict[str, dict[str, Any]] = {}

    while remaining and len(selected) < target:
        choices: list[tuple[tuple[Any, ...], LocalCandidateBinding, str, str, tuple[str, ...], tuple[str, ...]]] = []
        for binding in remaining:
            fields = _candidate_fields(binding)
            primary, primary_reason = _primary_region(binding)
            producers = _structural_producers(binding)
            frontier = _frontier_regions(binding)
            scope = set(map(str, getattr(binding.candidate, "structural_scope", [])))
            # Lexicographic structural diversity.  The leading values are
            # booleans/counts, never old heuristic/proof/coverage scores.
            priority = (
                int(fields["module"] not in covered_modules),
                int(fields["region_kind"] not in covered_kinds),
                int(fields["obligation"] not in covered_obligations),
                int(primary not in covered_regions),
                int(bool(set(frontier) - covered_frontiers)),
                len(set(producers) - covered_producers),
                len(scope - covered_scope),
            )
            # The later stable ordering resolves only exact diversity ties.
            choices.append((priority, binding, primary, primary_reason, producers, frontier))
        best_priority = max(item[0] for item in choices)
        tied = [item for item in choices if item[0] == best_priority]
        _ignored, binding, primary, primary_reason, producers, frontier = min(
            tied, key=lambda item: _stable_binding_order(item[1])
        )
        fields = _candidate_fields(binding)
        scope = set(map(str, getattr(binding.candidate, "structural_scope", [])))
        selection_features[_candidate_id(binding)] = {
            "lexicographic_priority": list(best_priority),
            "new_module": fields["module"] not in covered_modules,
            "new_region_kind": fields["region_kind"] not in covered_kinds,
            "new_obligation": fields["obligation"] not in covered_obligations,
            "new_primary_region": primary not in covered_regions,
            "new_typed_boundary_frontier": sorted(set(frontier) - covered_frontiers),
            "new_producers": sorted(set(producers) - covered_producers),
            "new_structural_scope": sorted(scope - covered_scope),
            "primary_region_reason": primary_reason,
        }
        binding.selected = True
        binding.selection_rank = len(selected) + 1
        binding.selection_score = None
        binding.primary_region_id = primary
        binding.selection_reason = "REQ12_BALANCED_LEXICOGRAPHIC_STRUCTURAL_DIVERSITY"
        selected.append(binding)
        covered_modules.add(fields["module"])
        covered_kinds.add(fields["region_kind"])
        covered_obligations.add(fields["obligation"])
        covered_regions.add(primary)
        covered_frontiers.update(frontier)
        covered_producers.update(producers)
        covered_scope.update(scope)
        remaining.remove(binding)

    selected_ids = {_candidate_id(item) for item in selected}
    duplicate_ids = {_candidate_id(item) for item in duplicates}
    duplicate_object_ids = {id(item) for item in duplicates}
    records: list[dict[str, Any]] = []
    for binding in ordered:
        fields = _candidate_fields(binding)
        primary, primary_reason = _primary_region(binding)
        is_duplicate = id(binding) in duplicate_object_ids
        is_selected = _candidate_id(binding) in selected_ids and not is_duplicate
        records.append({
            **fields,
            "compatible_region_ids": list(binding.compatible_region_ids),
            "binding_evidence_by_region": binding.binding_evidence_by_region,
            "primary_region_id": binding.primary_region_id if is_selected else primary,
            "primary_region_reason": selection_features.get(_candidate_id(binding), {}).get(
                "primary_region_reason", primary_reason
            ),
            "structural_producers": list(_structural_producers(binding)),
            "typed_boundary_regions": list(_frontier_regions(binding)),
            "structural_scope": list(getattr(binding.candidate, "structural_scope", [])),
            "selected": is_selected,
            "selection_rank": binding.selection_rank if is_selected else None,
            "selection_score": None,
            "selection_features": selection_features.get(_candidate_id(binding), {}) if is_selected else {},
            "disposition": "SELECTED" if is_selected else "DEFERRED",
            "reason": (
                binding.selection_reason if is_selected else
                "IDENTICAL_CANDIDATE_ID_DEFERRED" if _candidate_id(binding) in duplicate_ids else
                "BALANCED_LOCAL_BUDGET_DEFERRED"
            ),
            "generated_sva": False,
        })
    audit = {
        "schema": SCHEMA,
        "policy": "deterministic_lexicographic_structural_diversity",
        "input_bindings": len(bindings),
        "unique_candidate_ids": len(eligible),
        "duplicate_candidate_ids": len(duplicates),
        "budget": int(budget), "fraction": fraction, "minimum": int(minimum),
        "target_selected": target, "selected": len(selected), "deferred": len(bindings) - len(selected),
        "selection_dimensions": [
            "module", "region_kind", "obligation", "primary_region",
            "typed_boundary_frontier", "structural_producer", "structural_scope",
        ],
        "frontier_definition": (
            "only binding_evidence_by_region entries tagged TYPED_BOUNDARY; this is a structural proxy, "
            "not a prediction of proof-core coverage or a promise of a Composite assertion"
        ),
        "no_semantic_equivalence_merge": "only identical candidate_id is deduplicated; distinct candidates remain audited",
        "records": records,
        "selected_counts": {
            "modules": len(covered_modules), "region_kinds": len(covered_kinds),
            "obligations": len(covered_obligations), "primary_regions": len(covered_regions),
            "typed_boundary_regions": len(covered_frontiers), "structural_producers": len(covered_producers),
        },
    }
    return selected, audit
