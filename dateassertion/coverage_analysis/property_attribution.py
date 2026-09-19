"""Parse and summarize per-Property Jasper proof-core measurements."""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import asdict
from hashlib import sha256
from pathlib import Path
from typing import Any

from dateassertion.coverage_analysis.proof_core import CoverItem, parse_coverage_items, split_tcl_list


def _record(payload: str) -> dict[str, str]:
    values = split_tcl_list(payload.strip())
    if len(values) % 2:
        raise ValueError(f"odd Jasper cover-item record ({len(values)} fields)")
    return dict(zip(values[0::2], values[1::2]))


def _parse_property_core_file(
    path: str | Path,
) -> tuple[dict[str, set[int]], dict[str, dict[str, str]]]:
    source = Path(path)
    if not source.is_file():
        return {}, {}
    result: dict[str, set[int]] = defaultdict(set)
    statuses: dict[str, dict[str, str]] = {}
    open_property: str | None = None
    for line_number, line in enumerate(
        source.read_text(encoding="utf-8", errors="replace").splitlines(), start=1
    ):
        if line.startswith("PROPERTY_BEGIN\t"):
            property_id = line.split("\t", 1)[1]
            if open_property is not None:
                raise ValueError(f"nested attribution block at {source}:{line_number}")
            open_property = property_id
            result.setdefault(property_id, set())
            continue
        if line.startswith("PROPERTY_END\t"):
            property_id = line.split("\t", 1)[1]
            if property_id != open_property:
                raise ValueError(f"mismatched attribution block at {source}:{line_number}")
            open_property = None
            continue
        if line.startswith("ATTRIBUTION_STATUS\t"):
            parts = line.split("\t", 3)
            if len(parts) < 3 or parts[1] != open_property:
                raise ValueError(f"invalid attribution status at {source}:{line_number}")
            statuses[parts[1]] = {
                "status": parts[2],
                "detail": parts[3] if len(parts) == 4 else "",
            }
            continue
        parts = line.split("\t", 2)
        if len(parts) != 3:
            continue
        property_id, status, payload = parts
        if property_id != open_property:
            raise ValueError(f"item outside its attribution block at {source}:{line_number}")
        if status == "checked":
            result[property_id].add(int(_record(payload)["cid"]))
    if open_property is not None:
        raise ValueError(f"unterminated attribution block for {open_property}")
    for property_id in result:
        statuses.setdefault(
            property_id,
            {"status": "MEASURED", "detail": "legacy attribution block"},
        )
    return dict(result), statuses


def parse_property_core_items(path: str | Path) -> dict[str, set[int]]:
    """Return observed item sets while preserving the original public API."""
    result, _ = _parse_property_core_file(path)
    return result


def _identity(item: CoverItem) -> tuple[Any, ...]:
    return (
        item.file, item.line_start, item.column_start, item.line_end, item.column_end,
        item.cover_item_type, item.description, item.expression, item.module, item.instance,
    )


def _stable_item_id(item: CoverItem) -> str:
    payload = "\x1f".join(str(value) for value in _identity(item)).encode("utf-8")
    return "rtl_item_" + sha256(payload).hexdigest()[:20]


def build_property_attribution(
    attribution_path: str | Path,
    coverage_items_path: str | Path,
    property_metadata: dict[str, dict[str, Any]],
    pending_property_ids: set[str] | None = None,
) -> dict[str, Any]:
    by_property_cid, attribution_statuses = _parse_property_core_file(attribution_path)
    pending_property_ids = set(pending_property_ids or ())
    missing_pending_ids = pending_property_ids - set(by_property_cid)
    if missing_pending_ids:
        raise ValueError(
            "formal results reference properties absent from attribution catalog: "
            f"{sorted(missing_pending_ids)[:10]}"
        )
    for property_id in pending_property_ids:
        raw_status = attribution_statuses[property_id]
        by_property_cid[property_id].clear()
        attribution_statuses[property_id] = {
            "status": "SKIPPED_PENDING_TARGETS",
            "detail": (
                raw_status["detail"]
                if raw_status["status"] == "SKIPPED_PENDING_TARGETS"
                else f"formal-target reconciliation; raw_status={raw_status['status']}"
            ),
        }
    cover_items = parse_coverage_items(coverage_items_path)
    by_cid = {item.cid: item for item in cover_items}
    missing_cids = sorted({cid for values in by_property_cid.values() for cid in values if cid not in by_cid})
    if missing_cids:
        raise ValueError(f"attribution references unknown coverage cids: {missing_cids[:10]}")
    by_property = {
        property_id: {_stable_item_id(by_cid[cid]) for cid in cids}
        for property_id, cids in by_property_cid.items()
    }
    item_users: dict[str, set[str]] = defaultdict(set)
    for property_id, item_ids in by_property.items():
        for item_id in item_ids:
            item_users[item_id].add(property_id)
    global_checked_items = {
        _stable_item_id(item): item
        for item in cover_items if item.status == "covered_and_checked"
    }
    observed_ids = set(item_users)
    global_ids = set(global_checked_items)
    overlap_ids = observed_ids & global_ids
    global_only_ids = global_ids - observed_ids
    property_only_ids = observed_ids - global_ids

    property_rows = []
    property_ids = sorted(by_property)
    for property_id in property_ids:
        item_ids = by_property[property_id]
        unique = {item_id for item_id in item_ids if len(item_users[item_id]) == 1}
        shared = item_ids - unique
        overlaps = []
        for other_id in property_ids:
            if other_id == property_id:
                continue
            other = by_property[other_id]
            union = item_ids | other
            overlaps.append((len(item_ids & other) / len(union) if union else 0.0, other_id))
        max_overlap, max_overlap_with = max(overlaps, default=(0.0, None))
        meta = property_metadata.get(property_id, {})
        attribution_status = attribution_statuses[property_id]
        property_rows.append({
            "property_id": property_id,
            "region_id": meta.get("region_id"),
            "module": meta.get("module"),
            "family": meta.get("family"),
            "obligation": meta.get("obligation"),
            "attribution_status": attribution_status["status"],
            "attribution_detail": attribution_status["detail"],
            "observed_proof_core_items": len(item_ids),
            "unique_contribution_items": len(unique),
            "shared_contribution_items": len(shared),
            "unique_fraction": round(len(unique) / len(item_ids), 6) if item_ids else 0.0,
            "max_pairwise_jaccard": round(max_overlap, 6),
            "max_overlap_with": max_overlap_with,
            "observed_rtl_item_ids": sorted(item_ids),
        })

    def group_rows(field: str) -> list[dict[str, Any]]:
        groups: dict[str, set[str]] = defaultdict(set)
        group_properties: dict[str, set[str]] = defaultdict(set)
        for row in property_rows:
            name = str(row.get(field) or "UNSPECIFIED")
            groups[name].update(row["observed_rtl_item_ids"])
            group_properties[name].add(row["property_id"])
        item_group_count = Counter(
            item_id for values in groups.values() for item_id in values
        )
        return [
            {
                field: name,
                "properties": len(group_properties[name]),
                "observed_proof_core_items": len(items),
                "unique_to_group_items": sum(item_group_count[item_id] == 1 for item_id in items),
            }
            for name, items in sorted(groups.items())
        ]

    used_items = {_stable_item_id(by_cid[cid]): by_cid[cid] for cids in by_property_cid.values() for cid in cids}
    pair_values = []
    for index, left_id in enumerate(property_ids):
        left = by_property[left_id]
        for right_id in property_ids[index + 1:]:
            right = by_property[right_id]
            union = left | right
            value = len(left & right) / len(union) if union else 0.0
            pair_values.append(value)
    return {
        "schema": "region_flow.2-property-proof-core-attribution.v2",
        "definition": (
            "Each source property without pending elaborated targets is independently selected by "
            "check_cov -measure -type proof -property; the checked set from that bounded measurement "
            "is its observed proof core. Properties with Unknown/Unprocessed/Error targets are "
            "catalogued as SKIPPED_PENDING_TARGETS and remain outside the attribution measurement."
        ),
        "properties_catalogued": len(by_property),
        "properties_measured": sum(
            item["status"] == "MEASURED" for item in attribution_statuses.values()
        ),
        "properties_skipped_pending_targets": sum(
            item["status"] == "SKIPPED_PENDING_TARGETS"
            for item in attribution_statuses.values()
        ),
        "observed_union_items": len(item_users),
        "global_checked_items": len(global_ids),
        "global_observed_overlap_items": len(overlap_ids),
        "globally_checked_unattributed_items": len(global_only_ids),
        "property_observed_not_global_items": len(property_only_ids),
        "global_attribution_reconciliation_percent": round(
            100 * len(overlap_ids) / len(global_ids), 6
        ) if global_ids else 100.0,
        "globally_unique_items": sum(len(users) == 1 for users in item_users.values()),
        "shared_items": sum(len(users) > 1 for users in item_users.values()),
        "mean_pairwise_jaccard": round(sum(pair_values) / len(pair_values), 6) if pair_values else 0.0,
        "properties_with_unique_contribution": sum(row["unique_contribution_items"] > 0 for row in property_rows),
        "properties": property_rows,
        "region_contribution": group_rows("region_id"),
        "family_contribution": group_rows("family"),
        "obligation_contribution": group_rows("obligation"),
        "rtl_items": [
            {"rtl_item_id": item_id, **asdict(item)}
            for item_id, item in sorted(used_items.items())
        ],
        "globally_checked_unattributed_rtl_items": [
            {"rtl_item_id": item_id, **asdict(global_checked_items[item_id])}
            for item_id in sorted(global_only_ids)
        ],
        "property_observed_not_global_rtl_item_ids": sorted(property_only_ids),
    }
