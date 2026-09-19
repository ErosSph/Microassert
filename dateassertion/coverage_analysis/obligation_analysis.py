"""Post-Formal obligation coverage, missing-reason, and contribution analysis."""

from __future__ import annotations

from collections import Counter, defaultdict
from typing import Any


def finalize_obligation_matrix(
    applicability: dict[str, Any],
    inventory: list[dict[str, Any]],
    metadata: dict[str, dict[str, Any]],
    formal_results: list[Any],
    trusted_property_ids: set[str],
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    selected_candidates = {item["candidate_id"] for item in inventory if item.get("selected")}
    property_by_candidate = {item["candidate_id"]: property_id for property_id, item in metadata.items()}
    formal_by_id = {item.property_id: item for item in formal_results}
    candidate_rows = {item["candidate_id"]: item for item in inventory}
    matrix_rows = []
    matrix_counts: Counter[str] = Counter()
    missing_rows = []
    reason_counts: Counter[str] = Counter()
    generated_pairs = 0
    trusted_pairs = 0
    applicable_pairs = 0
    for region in applicability["regions"]:
        cells = []
        for source_cell in region["obligations"]:
            cell = dict(source_cell)
            if not cell["applicable"]:
                status = "NOT_APPLICABLE"
                cell["missing_reason"] = cell["reason"]
            else:
                applicable_pairs += 1
                candidate_ids = set(cell["candidate_ids"])
                selected = sorted(candidate_ids & selected_candidates)
                property_ids = [property_by_candidate[candidate_id] for candidate_id in selected if candidate_id in property_by_candidate]
                trusted = sorted(property_id for property_id in property_ids if property_id in trusted_property_ids)
                if selected:
                    generated_pairs += 1
                if trusted:
                    trusted_pairs += 1
                    status = "TRUSTED"
                    reason = None
                elif selected:
                    status = "GENERATED"
                    results = [formal_by_id[property_id] for property_id in property_ids if property_id in formal_by_id]
                    if any(item.vacuity == "VACUOUS" for item in results):
                        reason = "VACUOUS"
                    elif any(item.result in {"UNKNOWN", "ERROR"} for item in results) or not results:
                        reason = "FORMAL_UNKNOWN"
                    elif any(item.result == "FAIL" for item in results):
                        reason = "FORMAL_COUNTEREXAMPLE"
                    else:
                        reason = "GROUNDING_FAILED"
                else:
                    status = "MISSING"
                    selection_reasons = [candidate_rows[candidate_id].get("selection_reason") for candidate_id in candidate_ids if candidate_id in candidate_rows]
                    if not candidate_ids:
                        reason = "NO_CANDIDATE"
                    elif selection_reasons and all(value == "OVERLAP_FILTERED" for value in selection_reasons):
                        reason = "OVERLAP_FILTERED"
                    elif "BUDGET_FILTERED" in selection_reasons:
                        reason = "BUDGET_FILTERED"
                    else:
                        reason = "LOW_SCORE"
                cell.update({
                    "selected_candidate_ids": selected,
                    "property_ids": property_ids,
                    "trusted_property_ids": trusted,
                    "missing_reason": reason,
                })
                if status != "TRUSTED":
                    missing_rows.append({
                        "region_id": region["region_id"],
                        "region_kind": region["region_kind"],
                        "module": region["module"],
                        "obligation": cell["obligation"],
                        "matrix_status": status,
                        "reason": reason,
                        "candidate_ids": cell["candidate_ids"],
                        "selected_candidate_ids": selected,
                        "property_ids": property_ids,
                    })
                    reason_counts[str(reason)] += 1
            cell["status"] = status
            matrix_counts[status] += 1
            cells.append(cell)
        matrix_rows.append({**{key: region[key] for key in ("region_id", "region_kind", "module")}, "obligations": cells})
    matrix = {
        "schema": "region_flow.3-region-obligation-matrix.v1",
        "status_definitions": {
            "NOT_APPLICABLE": "ontology cell lacks the required explicit RTL evidence",
            "MISSING": "Applicable but no candidate entered the initial Formal portfolio",
            "GENERATED": "at least one candidate entered Formal but none passed the strict Trust Gate",
            "TRUSTED": "at least one property passed grounding, static validation, all-target Formal, and non-vacuity gates",
        },
        "regions": matrix_rows,
        "counts": dict(matrix_counts),
    }
    coverage = {
        "schema": "region_flow.3-verification-obligation-coverage.v1",
        "definition": "Trusted region-obligation pairs / Applicable evidence-backed region-obligation pairs",
        "applicable": applicable_pairs,
        "generated": generated_pairs,
        "trusted": trusted_pairs,
        "missing_unselected": matrix_counts["MISSING"],
        "generated_not_trusted": matrix_counts["GENERATED"],
        "trust_gaps": applicable_pairs - trusted_pairs,
        "generated_coverage_percent": round(100 * generated_pairs / applicable_pairs, 2) if applicable_pairs else 0.0,
        "trusted_coverage_percent": round(100 * trusted_pairs / applicable_pairs, 2) if applicable_pairs else 0.0,
    }
    missing = {
        "schema": "region_flow.3-missing-obligation-analysis.v1",
        "definition": "Every Applicable obligation without a Trusted property, including unselected and generated-but-untrusted cells.",
        "total": len(missing_rows),
        "reason_counts": dict(reason_counts),
        "obligations": missing_rows,
    }
    return matrix, coverage, missing


def contribution_by(
    field: str,
    metadata: dict[str, dict[str, Any]],
    trusted_property_ids: set[str],
    attribution: dict[str, Any],
) -> dict[str, Any]:
    rows_by_id = {item["property_id"]: item for item in attribution["properties"]}
    group_properties: dict[str, set[str]] = defaultdict(set)
    group_items: dict[str, set[str]] = defaultdict(set)
    for property_id, meta in metadata.items():
        group = str(meta.get(field) or "UNSPECIFIED")
        group_properties[group].add(property_id)
        group_items[group].update(rows_by_id.get(property_id, {}).get("observed_rtl_item_ids", []))
    item_groups: dict[str, set[str]] = defaultdict(set)
    for group, items in group_items.items():
        for item_id in items:
            item_groups[item_id].add(group)
    result = []
    for group in sorted(group_properties):
        properties = group_properties[group]
        items = group_items[group]
        unique_items = {item_id for item_id in items if len(item_groups[item_id]) == 1}
        result.append({
            field: group,
            "selected_properties": len(properties),
            "trusted_properties": len(properties & trusted_property_ids),
            "observed_proof_core_items": len(items),
            "unique_proof_core_items": len(unique_items),
            "shared_proof_core_items": len(items - unique_items),
            "properties_with_unique_contribution": sum(
                rows_by_id.get(property_id, {}).get("unique_contribution_items", 0) > 0
                for property_id in properties
            ),
            "properties_with_observed_contribution": sum(
                rows_by_id.get(property_id, {}).get("observed_proof_core_items", 0) > 0
                for property_id in properties
            ),
        })
    return {
        "schema": f"region_flow.3-property-contribution-by-{field}.v1",
        "grouping": field,
        "unique_definition": "item appears in this group union and no other group union",
        "groups": result,
    }
