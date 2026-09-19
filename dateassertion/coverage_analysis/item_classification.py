"""Evidence-based coverage-item classification and dynamic denominator policy."""

from __future__ import annotations

from collections import Counter
from pathlib import Path
import re
from typing import Any

from dateassertion.rtl_frontend.parser import RTLDesign
from .proof_core import CoverItem


COVERED = "COVERED"
REACHABLE_UNCOVERED = "REACHABLE_UNCOVERED"
FORMALLY_UNREACHABLE = "FORMALLY_UNREACHABLE"
CONFIGURATION_DISABLED = "CONFIGURATION_DISABLED"
GENERATED_OR_SUBMODULE = "GENERATED_OR_SUBMODULE"
TOOL_UNDETECTABLE = "TOOL_UNDETECTABLE"
UNKNOWN = "UNKNOWN"

CATEGORIES = (
    COVERED,
    REACHABLE_UNCOVERED,
    FORMALLY_UNREACHABLE,
    CONFIGURATION_DISABLED,
    GENERATED_OR_SUBMODULE,
    TOOL_UNDETECTABLE,
    UNKNOWN,
)

PARAMETER = re.compile(
    r"\bparameter\b(?:\s+(?:integer|logic|reg|wire|signed|unsigned))*"
    r"\s*(?:\[[^]]+\])?\s*([A-Za-z_][A-Za-z0-9_$]*)\s*=\s*([^,\n)]+)"
)


def _literal_integer(value: str) -> int | None:
    compact = re.sub(r"[\s_]", "", value).strip("()")
    sized = re.fullmatch(r"(?:\d+)?'[sS]?([bBoOdDhH])([0-9a-fA-F]+)", compact)
    if sized:
        base = {"b": 2, "o": 8, "d": 10, "h": 16}[sized.group(1).lower()]
        try:
            return int(sized.group(2), base)
        except ValueError:
            return None
    if re.fullmatch(r"\d+", compact):
        return int(compact)
    return None


def _parameter_values(design: RTLDesign) -> dict[str, dict[str, int]]:
    values: dict[str, dict[str, int]] = {}
    file_lines = {
        file: Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
        for file in design.files
    }
    for module in design.modules:
        lines = file_lines.get(module.file, [])
        text = "\n".join(lines[max(0, module.line_start - 1):module.line_end])
        module_values: dict[str, int] = {}
        for name, raw_value in PARAMETER.findall(text):
            value = _literal_integer(raw_value)
            if value is not None:
                module_values[name] = value
        values[module.name] = module_values
    return values


def _source_window(item: CoverItem, radius: int = 8) -> str:
    try:
        lines = Path(item.file).read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return ""
    start = max(0, item.line_start - radius - 1)
    end = min(len(lines), item.line_end + radius)
    return "\n".join(lines[start:end])


def _provably_false_after_elaboration(expression: str) -> bool:
    compact = re.sub(r"\s+", "", expression)
    literal = _literal_integer(compact.lstrip("|"))
    if literal == 0:
        return True
    false_atom = r"\|(?:\d+)?'[sS]?[bBoOdDhH]0+"
    true_atom = r"\|(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-F]*[1-9a-fA-F][0-9a-fA-F]*"
    return bool(
        re.search(rf"(?:^|[(&]){false_atom}(?:$|[)&])", compact)
        or re.search(rf"~\({true_atom}\)", compact)
    )


def _configuration_reason(item: CoverItem, values: dict[str, int]) -> str | None:
    if not _provably_false_after_elaboration(item.expression):
        return None
    description_refs = sorted(
        name for name in values if re.search(rf"\b{re.escape(name)}\b", item.description)
    )
    referenced = description_refs or sorted(
        name for name in values if re.search(rf"\b{re.escape(name)}\b", _source_window(item))
    )
    if not referenced:
        return None
    rendered = ", ".join(f"{name}={values[name]}" for name in referenced[:8])
    return f"elaboration made the cover condition false under parameters: {rendered}"


def classify_coverage_items(
    items: list[CoverItem],
    exact_statuses: dict[int, set[str]],
    gap: dict[str, Any],
    design: RTLDesign,
    top_module: str,
    config: dict[str, Any] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    """Classify every official item; exclude only evidence-backed categories."""
    policy = config or {}
    if policy.get("require_exact_statuses", True) and not exact_statuses:
        raise RuntimeError("exact Jasper coverage statuses are required for denominator classification")
    include_submodules = bool(policy.get("include_submodules", True))
    out_of_scope_modules = set(policy.get("out_of_scope_modules", []))
    parameter_values = _parameter_values(design)
    region_by_cid = {
        int(cid): region["region_id"]
        for region in gap.get("regions", [])
        for cid in region.get("item_ids", [])
    }
    records: list[dict[str, Any]] = []
    for item in items:
        statuses = exact_statuses.get(item.cid, set())
        reason = ""
        in_scope = item.module not in out_of_scope_modules and (item.module == top_module or include_submodules)
        config_reason = _configuration_reason(item, parameter_values.get(item.module, {}))
        if config_reason and ("unreachable" in statuses or "deadcode" in statuses):
            category = CONFIGURATION_DISABLED
            reason = config_reason
        elif "unreachable" in statuses or "deadcode" in statuses:
            category = FORMALLY_UNREACHABLE
            reason = "Jasper stimuli/dead-code reachability proof classified this item unreachable"
        elif item.status == "covered_and_checked":
            category = COVERED
            reason = "stimuli-reachable and present in at least one selected proof core"
        elif item.module != top_module:
            category = GENERATED_OR_SUBMODULE
            reason = "item belongs to a generated/descendant module"
        elif item.status == "uncovered_or_unchecked" and "covered" in statuses:
            category = REACHABLE_UNCOVERED
            reason = "Jasper proved the item reachable, but it is not checked by the selected proof cores"
        elif "undetectable" in statuses:
            category = TOOL_UNDETECTABLE
            reason = "checker coverage reports the item outside the selected proof cones"
        else:
            category = UNKNOWN
            reason = "reachability is unprocessed or undetermined; conservatively retained"
        excluded = category in {FORMALLY_UNREACHABLE, CONFIGURATION_DISABLED}
        if category == GENERATED_OR_SUBMODULE and not in_scope:
            excluded = True
            reason += "; module is explicitly outside the configured verification scope"
        records.append(
            {
                "cid": item.cid,
                "official_status": item.status,
                "exact_statuses": sorted(statuses),
                "classification": category,
                "included_in_effective_denominator": not excluded,
                "in_verification_scope": in_scope,
                "reason": reason,
                "region_id": region_by_cid.get(item.cid, "unmapped"),
                "module": item.module,
                "file": item.file,
                "line_start": item.line_start,
                "line_end": item.line_end,
                "signal_or_expression": item.expression,
                "cover_item_type": item.cover_item_type,
            }
        )
    counts = Counter(record["classification"] for record in records)
    included = Counter(
        record["classification"] for record in records if record["included_in_effective_denominator"]
    )
    excluded = Counter(
        record["classification"] for record in records if not record["included_in_effective_denominator"]
    )
    raw_covered = sum(item.status == "covered_and_checked" for item in items)
    effective_covered = counts[COVERED]
    effective_denominator = sum(included.values())
    total = len(records)
    summary = {
        "schema": "effective-coverage-denominator.v1",
        "official_total": total,
        "covered": raw_covered,
        "effective_covered": effective_covered,
        "reachable_uncovered": counts[REACHABLE_UNCOVERED],
        "formally_unreachable": counts[FORMALLY_UNREACHABLE],
        "configuration_disabled": counts[CONFIGURATION_DISABLED],
        "generated_or_submodule": counts[GENERATED_OR_SUBMODULE],
        "tool_undetectable": counts[TOOL_UNDETECTABLE],
        "unknown": counts[UNKNOWN],
        "category_counts": {category: counts[category] for category in CATEGORIES},
        "included_breakdown": {category: included[category] for category in CATEGORIES},
        "excluded_breakdown": {category: excluded[category] for category in CATEGORIES},
        "excluded_items": sum(excluded.values()),
        "effective_denominator": effective_denominator,
        "raw_proof_core_coverage_percent": round(100.0 * raw_covered / total, 2) if total else 0.0,
        "effective_reachable_coverage_percent": (
            round(100.0 * effective_covered / effective_denominator, 2) if effective_denominator else 0.0
        ),
        "policy": {
            "formally_unreachable": "excluded only with exact Jasper unreachable/deadcode status",
            "configuration_disabled": "excluded only with unreachable proof plus parameter/constant-fold evidence",
            "generated_or_submodule": "included unless its module is explicitly configured out of scope",
            "tool_undetectable": "included",
            "unknown": "included",
            "include_submodules": include_submodules,
            "out_of_scope_modules": sorted(out_of_scope_modules),
        },
    }
    if sum(counts.values()) != total or effective_denominator + summary["excluded_items"] != total:
        raise AssertionError("coverage denominator partition is not exhaustive")
    return records, summary


def apply_classification_to_gap(
    gap: dict[str, Any], records: list[dict[str, Any]], summary: dict[str, Any]
) -> dict[str, Any]:
    """Replace heuristic reachable counts with evidence-backed item classifications."""
    by_cid = {record["cid"]: record for record in records}
    for region in gap.get("regions", []):
        region_records = [by_cid[cid] for cid in region.get("item_ids", []) if cid in by_cid]
        category_counts = Counter(record["classification"] for record in region_records)
        reachable_ids = {
            record["cid"] for record in region_records if record["classification"] == REACHABLE_UNCOVERED
        }
        region["covered_elements"] = category_counts[COVERED]
        region["reachable_uncovered_elements"] = category_counts[REACHABLE_UNCOVERED]
        region["reachable_uncovered_item_ids"] = sorted(reachable_ids)
        region["classification_counts"] = {
            category: category_counts[category] for category in CATEGORIES
        }
        region["effective_denominator"] = sum(
            record["included_in_effective_denominator"] for record in region_records
        )
        region["effective_coverage_percent"] = (
            round(100.0 * category_counts[COVERED] / region["effective_denominator"], 2)
            if region["effective_denominator"] else 0.0
        )
        region["total_reachable_items"] = category_counts[COVERED] + category_counts[REACHABLE_UNCOVERED]
        region["uncovered_logic"] = [
            item for item in region.get("uncovered_logic", []) if item["cid"] in reachable_ids
        ]
        region["uncovered_lines"] = sorted(
            {line for item in region["uncovered_logic"] for line in range(item["line_start"], item["line_end"] + 1)}
        )
        region["uncovered_signals"] = sorted(
            {signal for item in region["uncovered_logic"] for signal in item.get("signals", [])}
        )
    gap["summary"].update(summary)
    return gap
