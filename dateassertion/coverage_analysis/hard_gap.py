"""Evidence, classification, clustering, and recovery accounting for hard coverage gaps."""

from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import PropertyIR
from dateassertion.rtl_frontend.parser import RTLDesign
from .item_classification import (
    CONFIGURATION_DISABLED as BROAD_CONFIGURATION_DISABLED,
    COVERED,
    FORMALLY_UNREACHABLE as BROAD_FORMALLY_UNREACHABLE,
    GENERATED_OR_SUBMODULE,
    REACHABLE_UNCOVERED,
    TOOL_UNDETECTABLE,
    UNKNOWN as BROAD_UNKNOWN,
)
from .proof_core import CoverItem


HIERARCHY_MAPPING_ISSUE = "HIERARCHY_MAPPING_ISSUE"
GENERATED_LOGIC = "GENERATED_LOGIC"
SUBMODULE_IN_SCOPE = "SUBMODULE_IN_SCOPE"
SUBMODULE_OUT_OF_SCOPE = "SUBMODULE_OUT_OF_SCOPE"
NO_PROPERTY_CONE = "NO_PROPERTY_CONE"
LOW_OBSERVABILITY = "LOW_OBSERVABILITY"
FORMAL_UNREACHABLE = "FORMAL_UNREACHABLE"
CONFIG_DISABLED = "CONFIG_DISABLED"
TOOL_LIMITATION = "TOOL_LIMITATION"
UNKNOWN = "UNKNOWN"

HARD_GAP_CLASSES = (
    HIERARCHY_MAPPING_ISSUE,
    GENERATED_LOGIC,
    SUBMODULE_IN_SCOPE,
    SUBMODULE_OUT_OF_SCOPE,
    NO_PROPERTY_CONE,
    LOW_OBSERVABILITY,
    FORMAL_UNREACHABLE,
    CONFIG_DISABLED,
    TOOL_LIMITATION,
    UNKNOWN,
)

RECOVERABLE = {
    HIERARCHY_MAPPING_ISSUE: (True, 0.90, "repair hierarchy/source mapping"),
    GENERATED_LOGIC: (True, 0.82, "map generated item to its semantic parent"),
    SUBMODULE_IN_SCOPE: (True, 0.92, "create and bind a submodule-local contract"),
    NO_PROPERTY_CONE: (True, 0.88, "create a local or cross-region property cone"),
    LOW_OBSERVABILITY: (True, 0.72, "introduce a traceable observation event and indirect contract"),
    SUBMODULE_OUT_OF_SCOPE: (False, 1.0, "explicitly outside verification scope"),
    FORMAL_UNREACHABLE: (False, 1.0, "independent reachability proof is conclusive"),
    CONFIG_DISABLED: (False, 1.0, "elaboration configuration disables the item"),
    TOOL_LIMITATION: (False, 0.85, "confirmed reporting/cone limitation; track separately"),
    UNKNOWN: (False, 0.2, "insufficient evidence for safe recovery"),
}

FAMILIES_BY_CLASS = {
    HIERARCHY_MAPPING_ISSUE: ["CONTROL_TO_OUTPUT_CONSISTENCY", "CROSS_REGION_CAUSALITY"],
    GENERATED_LOGIC: ["GENERATED_BLOCK_CONTRACT", "INTERNAL_EVENT_TO_EFFECT"],
    SUBMODULE_IN_SCOPE: ["SUBMODULE_INTERFACE_CONTRACT", "INTERNAL_EVENT_TO_EFFECT"],
    NO_PROPERTY_CONE: ["INTERNAL_EVENT_TO_EFFECT", "CONTROL_TO_OUTPUT_CONSISTENCY", "CROSS_REGION_CAUSALITY"],
    LOW_OBSERVABILITY: ["HELPER_OBSERVATION", "INTERNAL_EVENT_TO_EFFECT", "CROSS_REGION_CAUSALITY"],
}

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")
SV_WORDS = {
    "and", "or", "not", "if", "else", "begin", "end", "true", "false",
    "posedge", "negedge", "genblk", "Term", "Term1",
}


def _source_text(file: str, start: int, end: int, radius: int = 1) -> tuple[str, str]:
    try:
        lines = Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return "", ""
    exact = "\n".join(lines[max(0, start - 1):min(len(lines), end)])
    window = "\n".join(lines[max(0, start - radius - 1):min(len(lines), end + radius)])
    return exact, window


def _item_signals(item: CoverItem, source: str, design: RTLDesign) -> list[str]:
    # Signal metadata is intentionally keyed by unqualified name in RTLDesign;
    # shared interface names therefore retain the first module declaration.
    module_signals = set(design.signals)
    names = set(IDENT.findall(" ".join((item.expression, item.description, source))))
    return sorted(name for name in names if name in module_signals and name not in SV_WORDS)


def _always_block(item: CoverItem, design: RTLDesign) -> dict[str, Any] | None:
    matches = [
        block for block in design.always_blocks
        if block.module == item.module and block.file == item.file
        and block.line_start <= item.line_start <= block.line_end
    ]
    if not matches:
        return None
    block = min(matches, key=lambda value: value.line_end - value.line_start)
    return {
        "id": f"{block.module}:always:{block.line_start}-{block.line_end}",
        "kind": block.kind,
        "event_control": block.event_control,
        "line_start": block.line_start,
        "line_end": block.line_end,
        "assigned_signals": block.assigned_signals,
    }


def _dependencies(signals: set[str], module: str, design: RTLDesign) -> tuple[list[str], list[str]]:
    fanin: set[str] = set()
    fanout: set[str] = set()
    frontier = set(signals)
    for assignment in design.assignments:
        if assignment.module != module:
            continue
        deps = set(assignment.dependencies) | (set(IDENT.findall(assignment.guard)) & set(design.signals))
        if assignment.lhs in frontier:
            fanin.update(deps)
        if deps & frontier:
            fanout.add(assignment.lhs)
    return sorted(fanin), sorted(fanout)


def _hierarchy_path(item: CoverItem, top_module: str, design: RTLDesign) -> str:
    if item.instance:
        return item.instance
    if item.module == top_module:
        return top_module
    parents: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for parent in design.modules:
        for instance in parent.instances:
            parents[instance["module"]].append((parent.name, instance["instance"]))
    queue = [(item.module, item.module)]
    seen: set[str] = set()
    while queue:
        module, suffix = queue.pop(0)
        if module in seen:
            continue
        seen.add(module)
        for parent, instance in parents.get(module, []):
            path = f"{instance}.{suffix}"
            if parent == top_module:
                return f"{top_module}.{path}"
            queue.append((parent, path))
    return f"{top_module}.<unresolved>.{item.module}"


def _related_properties(
    signals: set[str], module: str, region_id: str, properties: list[PropertyIR]
) -> list[str]:
    return sorted(
        prop.property_id for prop in properties
        if (not prop.target_module or prop.target_module == module)
        and (set(prop.signals) & signals or prop.region_id == region_id)
    )


def _cluster_id(classification: str, module: str, region_id: str, block_id: str) -> str:
    raw_id = f"{classification}_{module}_{region_id}_{block_id}"
    return re.sub(r"[^a-z0-9]+", "_", raw_id.lower()).strip("_")


def _subclassification(
    item: CoverItem,
    broad: dict[str, Any],
    signals: list[str],
    related: list[str],
    source: str,
    top_module: str,
) -> tuple[str, str]:
    current = broad.get("classification")
    if current == BROAD_FORMALLY_UNREACHABLE:
        return FORMAL_UNREACHABLE, "independent Jasper stimuli/dead-code evidence proves the item unreachable"
    if current == BROAD_CONFIGURATION_DISABLED:
        return CONFIG_DISABLED, "elaboration evidence proves the item disabled by the active configuration"
    if current == BROAD_UNKNOWN:
        return UNKNOWN, "current reachability/checker evidence is insufficient for a safe recovery decision"
    if item.module != top_module:
        if not broad.get("in_verification_scope", True):
            return SUBMODULE_OUT_OF_SCOPE, "descendant module is explicitly outside configured scope"
        return SUBMODULE_IN_SCOPE, "descendant module is in scope but has no submodule-local proof cone"
    text = " ".join((item.expression, item.description, item.instance, source)).lower()
    if "genblk" in text or "generate" in text:
        return GENERATED_LOGIC, "generated item has not been mapped to a semantic parent contract"
    if broad.get("region_id") == "unmapped":
        return HIERARCHY_MAPPING_ISSUE, "coverage item has no current verification-region mapping"
    if not signals:
        return TOOL_LIMITATION, "item exposes no usable RTL signal in the exported coverage record"
    if not related:
        return NO_PROPERTY_CONE, "no active property references this item's local dependency evidence"
    return LOW_OBSERVABILITY, "logic is reachable but remains outside checked proof cores despite related properties"


def build_hard_gap_items(
    items: list[CoverItem],
    classifications: list[dict[str, Any]],
    design: RTLDesign,
    properties: list[PropertyIR],
    top_module: str,
    baseline_hard: dict[int, dict[str, Any]] | None = None,
    proven_property_ids: set[str] | None = None,
) -> tuple[list[dict[str, Any]], dict[int, dict[str, Any]]]:
    """Track every baseline hard item, including items recovered in later iterations."""
    item_by_id = {item.cid: item for item in items}
    broad_by_id = {int(record["cid"]): record for record in classifications}
    if baseline_hard is None:
        baseline_hard = {
            int(record["cid"]): {
                "baseline_classification": record["classification"],
                "baseline_reason": record["reason"],
            }
            for record in classifications
            if record["classification"] in {GENERATED_OR_SUBMODULE, TOOL_UNDETECTABLE}
        }
    rendered: list[dict[str, Any]] = []
    for cid, baseline in sorted(baseline_hard.items()):
        item = item_by_id.get(cid)
        broad = broad_by_id.get(cid)
        if item is None or broad is None:
            continue
        exact, window = _source_text(item.file, item.line_start, item.line_end)
        signals = _item_signals(item, window, design)
        fanin, fanout = _dependencies(set(signals), item.module, design)
        region_id = str(broad.get("region_id", "unmapped"))
        related = _related_properties(set(signals), item.module, region_id, properties)
        current = broad["classification"]
        subclass, reason = _subclassification(item, broad, signals, related, exact, top_module)
        block = _always_block(item, design)
        block_id = (block or {}).get("id", "continuous_or_generated")
        cluster_id = _cluster_id(subclass, item.module, region_id, block_id)
        proven_targets = [
            prop.property_id for prop in properties
            if prop.property_id in (proven_property_ids or set())
            and prop.hard_gap_cluster_id == cluster_id
            and set(prop.signals) & set(signals)
        ]
        if current == COVERED:
            recovery = "RECOVERED_COVERED"
        elif current == REACHABLE_UNCOVERED:
            recovery = "RECOVERED_REACHABLE"
        elif proven_targets:
            recovery = "RECOVERED_REACHABLE"
            reason += "; a proven cluster-local contract intersects this item's RTL signals"
        else:
            recovery = "HARD_GAP_REMAINING"
        recoverable, confidence, action = RECOVERABLE[subclass]
        rendered.append(
            {
                "cid": cid,
                "baseline_classification": baseline["baseline_classification"],
                "current_broad_classification": current,
                "hard_gap_classification": subclass,
                "recovery_status": recovery,
                "recoverable": bool(recoverable and recovery == "HARD_GAP_REMAINING"),
                "recoverability_confidence": confidence,
                "recommended_action": action,
                "classification_reason": reason,
                "source_file": item.file,
                "source_line": {"start": item.line_start, "end": item.line_end},
                "source_text": exact,
                "module": item.module,
                "hierarchy_path": _hierarchy_path(item, top_module, design),
                "signal": signals,
                "always_block": block,
                "fanin": fanin,
                "fanout": fanout,
                "current_region": region_id,
                "semantic_function": region_id.rsplit("_", 1)[-1],
                "related_property": related,
                "recovered_by_property": proven_targets,
                "coverage_classification_reason": broad.get("reason", ""),
                "official_status": item.status,
                "exact_statuses": broad.get("exact_statuses", []),
                "cover_item_type": item.cover_item_type,
                "expression": item.expression,
            }
        )
    return rendered, baseline_hard


def cluster_hard_gap_items(
    records: list[dict[str, Any]],
    previous_cluster_state: dict[str, dict[str, Any]] | None = None,
) -> list[dict[str, Any]]:
    """Cluster by module/region/procedural cone while retaining all required dimensions."""
    previous_cluster_state = previous_cluster_state or {}
    groups: dict[tuple[str, str, str, str], list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        block_id = (record.get("always_block") or {}).get("id", "continuous_or_generated")
        key = (
            record["hard_gap_classification"],
            record["module"],
            record["current_region"],
            block_id,
        )
        groups[key].append(record)
    clusters: list[dict[str, Any]] = []
    for (classification, module, region_id, block_id), members in groups.items():
        cluster_id = _cluster_id(classification, module, region_id, block_id)
        remaining = [item for item in members if item["recovery_status"] == "HARD_GAP_REMAINING"]
        recovered = [item for item in members if item["recovery_status"] != "HARD_GAP_REMAINING"]
        can_recover, confidence, action = RECOVERABLE[classification]
        state = previous_cluster_state.get(cluster_id, {})
        semantic_importance = 1.4 if any(
            token in region_id for token in ("control", "decode", "branch", "irq", "memory")
        ) else 1.15 if "pcpi" in region_id else 1.0
        selection_count = int(state.get("selection_count", 0))
        novelty = 1.0 / (1.0 + 0.6 * selection_count)
        previous_gain = max(0.35, 1.0 + 0.05 * float(state.get("last_gain", 0)))
        expected = len(remaining)
        priority = expected * semantic_importance * novelty * previous_gain * confidence
        hierarchy_paths = sorted({item["hierarchy_path"] for item in members})
        all_signals = sorted({signal for item in members for signal in item["signal"]})
        clusters.append(
            {
                "cluster_id": cluster_id,
                "target_type": "HARD_GAP",
                "hard_gap_classification": classification,
                "module": module,
                "hierarchy_paths": hierarchy_paths,
                "always_block": block_id,
                "verification_region": region_id,
                "semantic_function": members[0]["semantic_function"],
                "item_ids": sorted(item["cid"] for item in members),
                "remaining_item_ids": sorted(item["cid"] for item in remaining),
                "recovered_item_ids": sorted(item["cid"] for item in recovered),
                "total_items": len(members),
                "remaining_items": len(remaining),
                "recovered_items": len(recovered),
                "signals": all_signals,
                "fanin": sorted({signal for item in members for signal in item["fanin"]}),
                "fanout": sorted({signal for item in members for signal in item["fanout"]}),
                "source_files": sorted({item["source_file"] for item in members}),
                "source_lines": sorted({item["source_line"]["start"] for item in members}),
                "related_properties": sorted({prop for item in members for prop in item["related_property"]}),
                "recoverable": bool(can_recover and remaining),
                "recoverability_confidence": confidence,
                "recoverability_reason": action,
                "expected_recoverable_items": expected if can_recover else 0,
                "available_property_families": FAMILIES_BY_CLASS.get(classification, []),
                "recovered_region_id": (
                    f"hardgap_{module}_{members[0]['semantic_function']}"
                    if classification in {SUBMODULE_IN_SCOPE, GENERATED_LOGIC, HIERARCHY_MAPPING_ISSUE}
                    else region_id
                ),
                "priority_score": round(priority, 6),
                "priority_factors": {
                    "expected_recoverable_items": expected,
                    "semantic_importance": semantic_importance,
                    "novelty": round(novelty, 6),
                    "previous_gain": round(previous_gain, 6),
                    "recoverability_confidence": confidence,
                },
                "selection_count": selection_count,
                "status": state.get("status", "ACTIVE"),
            }
        )
    return sorted(clusters, key=lambda item: (-item["priority_score"], item["cluster_id"]))


def hard_gap_summary(records: list[dict[str, Any]]) -> dict[str, Any]:
    baseline = len(records)
    recovered_covered = sum(item["recovery_status"] == "RECOVERED_COVERED" for item in records)
    recovered_reachable = sum(item["recovery_status"] == "RECOVERED_REACHABLE" for item in records)
    recovered = recovered_covered + recovered_reachable
    remaining = baseline - recovered
    by_class = Counter(item["hard_gap_classification"] for item in records if item["recovery_status"] == "HARD_GAP_REMAINING")
    return {
        "schema": "hard-gap-summary.v1",
        "analyzed_hard_gap_items": baseline,
        "recovered_hard_gap_items": recovered,
        "recovered_as_covered": recovered_covered,
        "recovered_as_reachable": recovered_reachable,
        "remaining_hard_gap_items": remaining,
        "recoverability_rate_percent": round(100.0 * recovered / baseline, 2) if baseline else 0.0,
        "remaining_classification_counts": {name: by_class[name] for name in HARD_GAP_CLASSES},
    }
