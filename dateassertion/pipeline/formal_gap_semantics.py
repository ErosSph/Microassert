"""Formal-gap localization and deterministic semantic refinement for Req8.9.

The module deliberately keeps Formal evidence, graph structure, semantic
interpretation, and SVA compilation separate.  A Jasper coverage item can
only become a property after it has been mapped to a literal graph node and a
fixed primitive has been selected.  LLM output is descriptive data only.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import re
from typing import Any, Iterable

from dateassertion.coverage_analysis.proof_core import CoverItem
from dateassertion.ir.schema import ObjectType, PropertyIR
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


class Requirement89ValidationError(ValueError):
    """Raised when semantic interpretation is not grounded in supplied data."""


def stable_cover_item_id(item: CoverItem) -> str:
    values = (
        item.file, item.line_start, item.column_start, item.line_end,
        item.column_end, item.cover_item_type, item.description,
        item.expression, item.module, item.instance,
    )
    payload = "\x1f".join(str(value) for value in values).encode("utf-8")
    return "rtl_item_" + hashlib.sha256(payload).hexdigest()[:20]


def coverage_by_type(items: Iterable[CoverItem]) -> dict[str, Any]:
    """Return statement/branch/condition and full-model coverage metrics."""

    rows = list(items)
    aliases = {
        "statement": "statement", "branch": "branch",
        "expression": "condition", "toggle": "toggle",
    }
    result: dict[str, Any] = {}
    for raw_type, name in aliases.items():
        selected = [item for item in rows if item.cover_item_type == raw_type]
        checked = sum(item.status == "covered_and_checked" for item in selected)
        unchecked = sum(item.status == "uncovered_or_unchecked" for item in selected)
        non_actionable = len(selected) - checked - unchecked
        result[name] = {
            "jasper_cover_item_type": raw_type,
            "checked": checked,
            "unchecked": unchecked,
            "unreachable_or_undetectable": non_actionable,
            "total": len(selected),
            "raw_percent": round(100 * checked / len(selected), 2) if selected else 0.0,
            "effective_reachable_denominator": checked + unchecked,
            "effective_percent": round(100 * checked / (checked + unchecked), 2)
            if checked + unchecked else 0.0,
        }
    checked = sum(item.status == "covered_and_checked" for item in rows)
    unchecked = sum(item.status == "uncovered_or_unchecked" for item in rows)
    result["all"] = {
        "checked": checked,
        "unchecked": unchecked,
        "unreachable_or_undetectable": len(rows) - checked - unchecked,
        "total": len(rows),
        "raw_percent": round(100 * checked / len(rows), 2) if rows else 0.0,
        "effective_reachable_denominator": checked + unchecked,
        "effective_percent": round(100 * checked / (checked + unchecked), 2)
        if checked + unchecked else 0.0,
    }
    return result


def _node_locations(graph: dict[str, Any]) -> dict[tuple[str, str, int], list[dict[str, Any]]]:
    result: dict[tuple[str, str, int], list[dict[str, Any]]] = defaultdict(list)
    for node in graph.get("nodes", []):
        source = node.get("source", {})
        if source.get("file") and source.get("line"):
            result[(str(source["file"]), str(node.get("module", "")), int(source["line"]))].append(node)
    return result


def _region_ownership(regions: list[dict[str, Any]]) -> dict[str, set[str]]:
    ownership: dict[str, set[str]] = defaultdict(set)
    for region in regions:
        for node_id in region.get("core_node_ids", []):
            ownership[str(node_id)].add(str(region["region_id"]))
    return ownership


def localize_coverage_gaps(
    items: list[CoverItem], graph: dict[str, Any], regions: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    """Map every non-checked Jasper item to literal typed-graph nodes."""

    locations = _node_locations(graph)
    ownership = _region_ownership(regions)
    result = []
    for item in items:
        if item.status == "covered_and_checked":
            continue
        nodes: dict[str, dict[str, Any]] = {}
        for line in range(item.line_start, item.line_end + 1):
            for node in locations.get((item.file, item.module, line), []):
                nodes[str(node["id"])] = node
        # Container branch/expression items often start on an if/case line.
        # A one-line bounded lookup is evidence-preserving and never crosses
        # an always-block-sized neighborhood.
        if not nodes:
            for line in range(max(1, item.line_start - 1), item.line_end + 2):
                for node in locations.get((item.file, item.module, line), []):
                    nodes[str(node["id"])] = node
        node_ids = sorted(nodes)
        owner_ids = sorted({rid for node_id in node_ids for rid in ownership.get(node_id, set())})
        if item.status == "unreachable_or_undetectable":
            gap_type = "D_NON_ACTIONABLE"
            reason = "Jasper classified this item unreachable or undetectable"
        elif item.cover_item_type == "toggle" and not any(
            node.get("kind") == "assignment" for node in nodes.values()
        ):
            gap_type = "D_NON_ACTIONABLE"
            reason = "input/declaration toggle has no RTL producer obligation"
        elif not any(node.get("kind") == "assignment" for node in nodes.values()):
            gap_type = "D_NON_ACTIONABLE"
            reason = "coverage container has no exact assignment node at the bounded source location"
        elif not owner_ids:
            gap_type = "A_REGION_GAP"
            reason = "literal RTL assignment exists but is owned by no current Region core"
        else:
            gap_type = "B_CONTRACT_GAP"
            reason = "assignment belongs to an existing Region but remains outside trusted proof cores"
        result.append({
            "rtl_item_id": stable_cover_item_id(item), "cid": item.cid,
            "official_status": item.status, "cover_item_type": item.cover_item_type,
            "module": item.module, "file": item.file,
            "line_start": item.line_start, "line_end": item.line_end,
            "expression": item.expression, "description": item.description,
            "graph_node_ids": node_ids, "existing_region_ids": owner_ids,
            "gap_type": gap_type, "diagnosis_reason": reason,
        })
    return result


def build_elaborated_toggle_mapping_index(
    graph: dict[str, Any], design_map: dict[str, Any] | None,
) -> dict[str, Any]:
    """Build reusable exact-lookup indexes for elaborated toggle localization."""

    nodes = {str(node.get("id", "")): node for node in graph.get("nodes", [])}
    local_producers: dict[str, list[str]] = defaultdict(list)
    for edge in graph.get("edges", []):
        source = str(edge.get("source", ""))
        target = str(edge.get("target", ""))
        if edge.get("type") == "DATA" and nodes.get(source, {}).get("kind") == "assignment":
            local_producers[target].append(source)
    instance_lookup: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    connection_lookup: dict[tuple[str, str, str], list[dict[str, Any]]] = defaultdict(list)
    if design_map:
        for instance in design_map.get("instances", []):
            module = str(instance.get("module", ""))
            path_parts = str(instance.get("path", "")).split(".")
            # Index full paths and every dotted suffix.  Ambiguous short suffixes
            # are retained as multiple records and are rejected by the resolver.
            for offset in range(len(path_parts)):
                instance_lookup[(module, ".".join(path_parts[offset:]))].append(instance)
        for edge in design_map.get("cross_module_dependencies", []):
            target = edge.get("target", {})
            if (
                edge.get("type") == "CROSS_MODULE"
                and edge.get("semantic_kind") == "DATA"
                and edge.get("direction") == "input"
            ):
                connection_lookup[(
                    str(target.get("instance_path", "")),
                    str(target.get("module", "")),
                    str(target.get("signal", "")),
                )].append(edge)
    return {
        "nodes": nodes,
        "local_producers": {
            target: sorted(set(producers)) for target, producers in local_producers.items()
        },
        "instance_lookup": instance_lookup,
        "connection_lookup": connection_lookup,
    }


def resolve_elaborated_toggle_producers(
    item: CoverItem, graph: dict[str, Any], design_map: dict[str, Any] | None,
    *, mapping_index: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Resolve a declaration toggle to literal producers without name heuristics.

    The semantic graph is deliberately module-definition scoped.  Consequently,
    a Jasper item for a parameterized child *input* has no local producer even
    when the elaborated instance is connected to a parent net driven by an RTL
    assignment.  This helper admits one bounded hierarchy hop only:

    ``child input port -> exact design-map DATA connection -> parent signal``

    It then accepts only literal ``assignment -> signal`` DATA edges in the
    parent module.  Generated instances are supported because the matching key
    is the complete instance-path suffix, including ``[index]`` components.
    Missing, ambiguous, non-DATA, or producer-free metadata remains unresolved;
    callers must retain its non-actionable diagnosis rather than infer an edge.
    """

    raw_module = str(getattr(item, "module", ""))
    module = raw_module.split(":(", 1)[0]
    description = str(getattr(item, "description", ""))
    match = re.search(r'"([^"\n]+)"', description)
    if not match:
        return {
            "resolved": False,
            "producer_resolution": "NO_EXACT_DECLARATION_NAME",
            "diagnosis_reason": "toggle description has no quoted declaration name",
            "signal_node_ids": [], "producer_assignment_ids": [],
            "cross_module_evidence": [],
        }
    signal_name = re.sub(r"\[[^\]]+\]$", "", match.group(1)).rsplit(".", 1)[-1]
    signal_id = f"signal:{module}.{signal_name}"
    index = mapping_index or build_elaborated_toggle_mapping_index(graph, design_map)
    nodes = index["nodes"]
    signal = nodes.get(signal_id)
    source = signal.get("source", {}) if signal else {}
    if (
        not signal
        or signal.get("kind") != "signal"
        or source.get("file") != getattr(item, "file", None)
        or source.get("line") != getattr(item, "line_start", None)
    ):
        return {
            "resolved": False,
            "producer_resolution": "NO_EXACT_DECLARATION_NODE",
            "diagnosis_reason": "reported toggle has no exact declaration graph node",
            "signal_node_ids": [], "producer_assignment_ids": [],
            "cross_module_evidence": [],
        }

    local_producers = list(index["local_producers"].get(signal_id, []))
    if local_producers:
        return {
            "resolved": True,
            "producer_resolution": "EXACT_TYPED_DATA_EDGE",
            "diagnosis_reason": "declaration toggle traced through literal DATA result edges to local producers",
            "signal_node_ids": [signal_id], "producer_assignment_ids": local_producers,
            "cross_module_evidence": [],
        }

    if not design_map:
        return {
            "resolved": False,
            "producer_resolution": "NO_LOCAL_PRODUCER_NO_DESIGN_MAP",
            "diagnosis_reason": "reported toggle has no exact declaration-to-local-producer path",
            "signal_node_ids": [signal_id], "producer_assignment_ids": [],
            "cross_module_evidence": [],
        }

    raw_instance = str(getattr(item, "instance", ""))
    instances = list(index["instance_lookup"].get((module, raw_instance), [])) if raw_instance else []
    if len(instances) != 1:
        return {
            "resolved": False,
            "producer_resolution": (
                "NO_EXACT_ELABORATED_INSTANCE" if not instances
                else "AMBIGUOUS_ELABORATED_INSTANCE"
            ),
            "diagnosis_reason": "toggle instance does not identify one exact elaborated module instance",
            "signal_node_ids": [signal_id], "producer_assignment_ids": [],
            "cross_module_evidence": [],
        }
    instance_path = str(instances[0].get("path", ""))
    connections = list(index["connection_lookup"].get((instance_path, module, signal_name), []))
    source_keys = {
        (
            str(edge.get("source", {}).get("module", "")),
            str(edge.get("source", {}).get("signal", "")),
        )
        for edge in connections
    }
    if len(source_keys) != 1:
        return {
            "resolved": False,
            "producer_resolution": (
                "NO_EXACT_DATA_PORT_CONNECTION" if not source_keys
                else "AMBIGUOUS_EXACT_DATA_PORT_CONNECTION"
            ),
            "diagnosis_reason": "toggle input has no unique exact DATA port connection in elaboration metadata",
            "signal_node_ids": [signal_id], "producer_assignment_ids": [],
            "cross_module_evidence": sorted(str(edge.get("id", "")) for edge in connections),
        }
    parent_module, parent_signal = next(iter(source_keys))
    parent_signal_id = f"signal:{parent_module}.{parent_signal}"
    parent_producers = list(index["local_producers"].get(parent_signal_id, []))
    if not parent_producers:
        return {
            "resolved": False,
            "producer_resolution": "EXACT_PORT_SOURCE_WITHOUT_LOCAL_PRODUCER",
            "diagnosis_reason": "exact DATA port source has no literal local assignment producer",
            "signal_node_ids": [signal_id, parent_signal_id], "producer_assignment_ids": [],
            "cross_module_evidence": sorted(str(edge.get("id", "")) for edge in connections),
        }
    return {
        "resolved": True,
        "producer_resolution": "EXACT_CROSS_MODULE_DATA_PORT",
        "diagnosis_reason": "declaration toggle traced through one exact elaborated DATA input-port connection to parent assignment producers",
        "signal_node_ids": [signal_id, parent_signal_id],
        "producer_assignment_ids": parent_producers,
        "cross_module_evidence": sorted(str(edge.get("id", "")) for edge in connections),
    }


def gap_summary(records: list[dict[str, Any]]) -> dict[str, Any]:
    counts = Counter(record["gap_type"] for record in records)
    type_a_subtypes = Counter(
        record.get("type_a_subtype") for record in records
        if record.get("gap_type") == "A_REGION_GAP" and record.get("type_a_subtype")
    )
    by_cover_type = Counter(
        (record["gap_type"], record["cover_item_type"]) for record in records
    )
    return {
        "gaps": len(records),
        "by_type": dict(sorted(counts.items())),
        "type_a_subtypes": dict(sorted(type_a_subtypes.items())),
        "high_value_refinement_candidates": sum(
            bool(record.get("priority", {}).get("eligible_for_refinement"))
            for record in records
        ),
        "by_gap_and_cover_type": [
            {"gap_type": key[0], "cover_item_type": key[1], "items": value}
            for key, value in sorted(by_cover_type.items())
        ],
    }


def refine_gap_classification(
    records: list[dict[str, Any]], graph: dict[str, Any],
    regions: list[dict[str, Any]], *, priority_threshold: float = 7.0,
) -> list[dict[str, Any]]:
    """Refine Type-A gaps and attach a design-independent priority record.

    A coherent producer family with state/control structure is a NEW_REGION.
    A node already present in an existing Region's bounded COI, or directly
    adjacent to an owned core node, is a REGION_BOUNDARY.  A remaining lone,
    combinational producer is RTL_DETAIL.  Signal spellings are never used.
    """

    nodes = {str(node["id"]): node for node in graph.get("nodes", [])}
    assignments = _assignment_nodes(graph)
    core_owner = _region_ownership(regions)
    coi_owner: dict[str, set[str]] = defaultdict(set)
    for region in regions:
        region_id = str(region["region_id"])
        for node_id in region.get("coi", {}).get("node_ids", []):
            coi_owner[str(node_id)].add(region_id)
    adjacent: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in graph.get("edges", []):
        source, target = str(edge.get("source", "")), str(edge.get("target", ""))
        adjacent[source].append(edge)
        adjacent[target].append(edge)
    producer_count = Counter(
        (str(node.get("module", "")), str(node.get("lhs", "")))
        for node in assignments.values()
    )

    refined = []
    for raw in records:
        record = deepcopy(raw)
        subtype = ""
        context_regions: set[str] = set()
        neighbor_regions: set[str] = set()
        typed_edges: Counter[str] = Counter()
        strong_cluster = False
        if record.get("gap_type") == "A_REGION_GAP":
            assignment_nodes = [
                assignments[node_id] for node_id in record.get("graph_node_ids", [])
                if node_id in assignments
            ]
            for node in assignment_nodes:
                node_id = str(node["id"])
                context_regions.update(coi_owner.get(node_id, set()))
                local_edges = adjacent.get(node_id, [])
                typed_edges.update(str(edge.get("type", "")) for edge in local_edges)
                for edge in local_edges:
                    other = str(edge.get("target")) if str(edge.get("source")) == node_id else str(edge.get("source"))
                    neighbor_regions.update(core_owner.get(other, set()))
                signal = nodes.get(f"signal:{node.get('module')}.{node.get('lhs')}", {})
                structured_boundary = (
                    signal.get("direction") == "output"
                    or signal.get("role") in {"state", "counter", "event", "control"}
                    or typed_edges["SEQUENTIAL"] > 0
                )
                family_size = producer_count[(str(node.get("module", "")), str(node.get("lhs", "")))]
                if family_size >= 2 and (typed_edges["CONTROL"] > 0 or structured_boundary):
                    strong_cluster = True
            if strong_cluster:
                subtype = "NEW_REGION"
                subtype_reason = "coherent multi-producer family has control/state structure"
            elif context_regions or neighbor_regions:
                subtype = "REGION_BOUNDARY"
                subtype_reason = "unowned producer lies in a Region COI or touches an owned core node"
            else:
                subtype = "RTL_DETAIL"
                subtype_reason = "isolated combinational implementation producer has no independent semantic boundary"
            record.update({
                "type_a_subtype": subtype,
                "type_a_subtype_reason": subtype_reason,
                "boundary_region_ids": sorted(context_regions | neighbor_regions),
                "subtype_structural_evidence": {
                    "coi_region_ids": sorted(context_regions),
                    "owned_neighbor_region_ids": sorted(neighbor_regions),
                    "incident_edge_types": dict(sorted(typed_edges.items())),
                    "coherent_multi_producer_cluster": strong_cluster,
                },
            })

        cover_type = str(record.get("cover_item_type", ""))
        reachable_importance = 0 if record.get("official_status") != "uncovered_or_unchecked" else {
            "branch": 5, "expression": 5, "statement": 4, "toggle": 1,
        }.get(cover_type, 2)
        semantic_value = {
            "NEW_REGION": 5, "REGION_BOUNDARY": 4, "RTL_DETAIL": 1,
        }.get(subtype, {"B_CONTRACT_GAP": 4, "C_COMPOSITION_GAP": 5}.get(str(record.get("gap_type")), 0))
        novelty = {
            "NEW_REGION": 5, "REGION_BOUNDARY": 2, "RTL_DETAIL": 0,
        }.get(subtype, 2 if record.get("gap_type") in {"B_CONTRACT_GAP", "C_COMPOSITION_GAP"} else 0)
        overlap = len(set(record.get("existing_region_ids", [])) | context_regions | neighbor_regions)
        formal_cost = max(1.0, len(record.get("graph_node_ids", [])) + len(str(record.get("expression", ""))) / 80.0)
        total = reachable_importance + semantic_value + novelty - overlap - formal_cost
        eligible = (
            record.get("official_status") == "uncovered_or_unchecked"
            and record.get("gap_type") in {"B_CONTRACT_GAP", "C_COMPOSITION_GAP"}
            or (
                record.get("official_status") == "uncovered_or_unchecked"
                and record.get("gap_type") == "A_REGION_GAP"
                and subtype in {"NEW_REGION", "REGION_BOUNDARY"}
            )
        ) and total >= priority_threshold
        record["priority"] = {
            "reachable_importance": reachable_importance,
            "semantic_value": semantic_value,
            "novelty": novelty,
            "overlap_penalty": overlap,
            "formal_cost_penalty": round(formal_cost, 3),
            "total": round(total, 3),
            "threshold": float(priority_threshold),
            "eligible_for_refinement": bool(eligible),
            "disposition": (
                "HIGH_VALUE_REFINEMENT" if eligible else
                "NON_ACTIONABLE" if record.get("gap_type") == "D_NON_ACTIONABLE" else
                "LOW_VALUE_OVERLAP_OR_RTL_DETAIL"
            ),
        }
        refined.append(record)
    return refined


def _assignment_nodes(graph: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {
        str(node["id"]): node for node in graph.get("nodes", [])
        if node.get("kind") == "assignment"
    }


def select_residual_region_candidate(
    mappings: list[dict[str, Any]], graph: dict[str, Any], design: RTLDesign,
    *, max_assignments: int = 8,
) -> dict[str, Any]:
    """Choose a coherent residual producer family using graph evidence only."""

    assignments = _assignment_nodes(graph)
    score: Counter[tuple[str, str, int, int]] = Counter()
    covered_cids: dict[tuple[str, str, int, int], set[int]] = defaultdict(set)

    def enclosing_span(module: str, file: str, line: int) -> tuple[int, int]:
        blocks = [
            block for block in design.always_blocks
            if block.module == module and block.file == file
            and block.line_start <= line <= block.line_end
        ]
        if not blocks:
            return line, line
        block = min(blocks, key=lambda value: value.line_end - value.line_start)
        return int(block.line_start), int(block.line_end)

    for gap in mappings:
        if gap["gap_type"] != "A_REGION_GAP":
            continue
        if gap.get("type_a_subtype") not in {None, "", "NEW_REGION"}:
            continue
        if gap.get("priority") and not gap["priority"].get("eligible_for_refinement", False):
            continue
        for node_id in gap["graph_node_ids"]:
            node = assignments.get(node_id)
            if node:
                start, end = enclosing_span(
                    str(node["module"]), str(node.get("source", {}).get("file", "")),
                    int(node.get("source", {}).get("line", 0)),
                )
                key = (str(node["module"]), str(node["lhs"]), start, end)
                weight = {"statement": 5, "branch": 4, "expression": 3}.get(
                    gap["cover_item_type"], 1
                )
                score[key] += weight
                covered_cids[key].add(int(gap["cid"]))
    if not score:
        raise RuntimeError("no graph-grounded Type-A residual Region candidate")
    def density(key: tuple[str, str, int, int]) -> float:
        return score[key] / (1.0 + max(0, key[3] - key[2]) / 20.0)

    module, lhs, block_start, block_end = sorted(
        score, key=lambda key: (-density(key), -score[key], key)
    )[0]
    producers = sorted(
        [
            node for node in assignments.values()
            if node.get("module") == module and node.get("lhs") == lhs
            and block_start <= int(node.get("source", {}).get("line", 0)) <= block_end
        ],
        key=lambda node: (node.get("source", {}).get("line", 0), node["id"]),
    )[:max_assignments]
    producer_ids = {str(node["id"]) for node in producers}
    signal_ids = set()
    local_edges = []
    for edge in graph.get("edges", []):
        if edge.get("source") in producer_ids or edge.get("target") in producer_ids:
            local_edges.append({key: edge.get(key) for key in ("type", "source", "target", "clock", "evidence") if key in edge})
            for endpoint in (edge.get("source", ""), edge.get("target", "")):
                if str(endpoint).startswith(f"signal:{module}."):
                    signal_ids.add(str(endpoint))
    node_by_id = {str(node["id"]): node for node in graph.get("nodes", [])}
    signal_nodes = [node_by_id[node_id] for node_id in sorted(signal_ids) if node_id in node_by_id]
    signals = sorted({str(node["name"]) for node in signal_nodes})
    state = sorted({str(node["name"]) for node in signal_nodes if node.get("role") in {"state", "counter"}})
    events = sorted({str(node["name"]) for node in signal_nodes if node.get("role") in {"event", "predicate", "control"}})
    inputs = sorted({str(node["name"]) for node in signal_nodes if node.get("direction") == "input"})
    outputs = sorted({str(node["name"]) for node in signal_nodes if node.get("direction") == "output"})
    raw_id = hashlib.sha256(f"{module}\x1f{lhs}\x1f{'|'.join(sorted(producer_ids))}".encode()).hexdigest()[:12]
    region_id = f"region_gap_residual_{raw_id}"
    source_lines = [int(node["source"]["line"]) for node in producers]
    source_file = str(producers[0]["source"]["file"])
    file_lines = open(source_file, encoding="utf-8", errors="replace").read().splitlines()
    start, end = min(source_lines), max(source_lines)
    nearby = []
    for region in []:  # stable schema slot; populated by the orchestrator if needed
        nearby.append(region)
    return {
        "schema": "region_flow.9-extension-region-candidate.v1",
        "region_id": region_id, "module": module, "residual_target": lhs,
        "candidate_kind": "DATAPATH", "selection_score": round(density((module, lhs, block_start, block_end)), 3),
        "raw_gap_score": score[(module, lhs, block_start, block_end)],
        "gap_item_ids": sorted(covered_cids[(module, lhs, block_start, block_end)]),
        "core_node_ids": sorted(producer_ids | signal_ids),
        "local_graph_nodes": producers + signal_nodes,
        "local_graph_edges": local_edges,
        "signals": signals, "important_state_candidates": state,
        "important_event_candidates": events, "inputs": inputs, "outputs": outputs,
        "source_evidence": {
            "file": source_file, "line_start": start, "line_end": end,
            "snippet": "\n".join(file_lines[start - 1:end]),
        },
        "structural_evidence": {
            "shared_output_producers": len(producers),
            "typed_edges": dict(Counter(edge["type"] for edge in local_edges)),
            "producer_guard_count": len({str(node.get("guard", "")) for node in producers}),
            "state_ownership": state,
            "input_output_boundary": {"inputs": inputs, "outputs": outputs},
        },
        "whole_design_rtl_supplied": False,
    }


def package_extension_interpretation_context(
    candidate: dict[str, Any], nearby_regions: list[dict[str, Any]],
    spec_lines: list[dict[str, Any]],
) -> dict[str, Any]:
    compact_regions = [{
        "region_id": region["region_id"], "kind": region.get("kind"),
        "module": region.get("module"), "signals": region.get("signals", []),
    } for region in nearby_regions[:12]]
    return {
        "schema": "region_flow.9-extension-interpretation-context.v1",
        "candidate_region_id": candidate["region_id"],
        "module": candidate["module"], "coverage_gap_description": {
            "gap_type": "A_REGION_GAP", "gap_item_ids": candidate["gap_item_ids"],
            "reason": "uncovered assignment nodes have no existing Region owner",
        },
        "local_typed_subgraph": {
            "nodes": candidate["local_graph_nodes"], "edges": candidate["local_graph_edges"],
        },
        "rtl_slice": candidate["source_evidence"],
        "signals": candidate["signals"],
        "important_state_candidates": candidate["important_state_candidates"],
        "important_event_candidates": candidate["important_event_candidates"],
        "inputs": candidate["inputs"], "outputs": candidate["outputs"],
        "nearby_regions": compact_regions, "optional_spec_evidence": spec_lines,
        "whole_design_rtl_supplied": False,
        "llm_may_generate_sva": False,
    }


def _all_strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from _all_strings(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from _all_strings(item)


def validate_extension_interpretation(
    response: dict[str, Any], context: dict[str, Any],
) -> dict[str, Any]:
    required = {
        "candidate_region_id", "candidate_region_name", "functional_meaning",
        "important_state", "important_events", "inputs", "outputs",
        "confidence", "evidence",
    }
    if not isinstance(response, dict) or not required <= set(response):
        raise Requirement89ValidationError(f"missing response fields: {sorted(required - set(response or {}))}")
    forbidden_keys = {"sva", "assertion", "property", "assumption", "formal_status"}
    if any(str(key).lower() in forbidden_keys for key in response):
        raise Requirement89ValidationError("LLM must not generate SVA, assumptions, or Formal status")
    if response["candidate_region_id"] != context["candidate_region_id"]:
        raise Requirement89ValidationError("candidate_region_id was invented or changed")
    allowed_signals = set(context["signals"])
    for field in ("important_state", "important_events", "inputs", "outputs"):
        if not isinstance(response[field], list) or not set(map(str, response[field])) <= allowed_signals:
            raise Requirement89ValidationError(f"{field} contains a signal outside the local subgraph")
    confidence = response["confidence"]
    if not isinstance(confidence, (int, float)) or isinstance(confidence, bool) or not 0 <= confidence <= 1:
        raise Requirement89ValidationError("confidence must be numeric in [0,1]")
    allowed_nodes = {str(node["id"]): node for node in context["local_typed_subgraph"]["nodes"]}
    if not isinstance(response["evidence"], list) or not response["evidence"]:
        raise Requirement89ValidationError("at least one graph-node evidence record is required")
    checked_evidence = []
    for raw in response["evidence"]:
        if not isinstance(raw, dict) or not {"node_id", "reason"} <= set(raw):
            raise Requirement89ValidationError("evidence must contain node_id and reason")
        node_id = str(raw["node_id"])
        if node_id not in allowed_nodes:
            raise Requirement89ValidationError(f"invented evidence node: {node_id}")
        source = allowed_nodes[node_id].get("source", {})
        checked_evidence.append({
            "node_id": node_id, "file": source.get("file"), "line": source.get("line"),
            "reason": str(raw["reason"]),
        })
    if any(re.search(r"\b(?:assert|assume)\s+property\b", text, re.I) for text in _all_strings(response)):
        raise Requirement89ValidationError("executable assertion/assumption text is forbidden")
    result = deepcopy(response)
    result["important_state"] = sorted(set(map(str, result["important_state"])))
    result["important_events"] = sorted(set(map(str, result["important_events"])))
    result["inputs"] = sorted(set(map(str, result["inputs"])))
    result["outputs"] = sorted(set(map(str, result["outputs"])))
    result["evidence"] = checked_evidence
    result["validated_against_local_subgraph"] = True
    result["generated_sva"] = False
    return result


def extension_region_from_interpretation(
    candidate: dict[str, Any], interpretation: dict[str, Any],
) -> dict[str, Any]:
    return {
        "region_id": candidate["region_id"], "kind": candidate["candidate_kind"],
        "module": candidate["module"], "name": interpretation["candidate_region_name"],
        "functional_meaning": interpretation["functional_meaning"],
        "signals": candidate["signals"], "core_node_ids": candidate["core_node_ids"],
        "state": interpretation["important_state"], "events": interpretation["important_events"],
        "inputs": interpretation["inputs"], "outputs": interpretation["outputs"],
        "confidence": interpretation["confidence"], "llm_evidence": interpretation["evidence"],
        "evidence": candidate["source_evidence"],
        "ontology_classification": "EXTENSION_REGION",
        "creation_reason": "FORMAL_TYPE_A_REGION_GAP",
    }


def property_from_assignment(
    node: dict[str, Any], region_id: str, property_id: str, iteration: int,
    *, source_classification: str = "RTL_STRUCTURAL",
    reset_asserted: str = "!resetn",
) -> PropertyIR:
    """Compile a literal assignment relation through fixed UPDATE/DATA primitive."""

    if node.get("kind") != "assignment":
        raise ValueError("only assignment nodes can be compiled")
    guard = str(node.get("guard") or "1'b1")
    lhs, rhs = str(node["lhs"]), str(node["rhs"])
    timing = str(node.get("timing", "unknown"))
    if timing == "next_cycle":
        body = f"({guard}) |=> {lhs} == $past({rhs})"
        family, template = "PRIMITIVE_UPDATE", "UPDATE"
        bindings = {"CONDITION": guard, "TARGET": lhs, "VALUE": rhs, "DELAY": 1}
    elif timing == "same_cycle":
        body = f"({guard}) |-> {lhs} == ({rhs})"
        family, template = "PRIMITIVE_DATA_INTEGRITY", "DATA_INTEGRITY"
        bindings = {"CONDITION": guard, "SOURCE": rhs, "TARGET": lhs, "DELAY": 0}
    else:
        raise ValueError(f"unsupported assignment timing: {timing}")
    signals = sorted({lhs} | expression_signals(guard) | expression_signals(rhs))
    source = node.get("source", {})
    return PropertyIR(
        property_id=property_id, region_id=region_id, object_type=ObjectType.EXTENSION,
        family=family, template=template, bindings=bindings, signals=signals,
        source="formal-gap+typed-graph+exact-rtl-relation+fixed-primitive",
        llm_confidence=1.0, body=body, disable_iff=reset_asserted,
        description=f"[REQ8.9 ITERATION {iteration}] graph-grounded {lhs} assignment obligation",
        source_classification=source_classification, iteration_added=iteration,
        evidence=[{
            "files": [source.get("file")], "line_start": source.get("line"),
            "line_end": source.get("line"), "snippet": f"{lhs} <=/={{ {rhs} }}",
            "graph_node_id": node["id"], "region_flow_scope": "LOCAL",
        }], target_module=str(node["module"]),
    )


def compile_region_gap_properties(
    candidate: dict[str, Any], graph: dict[str, Any], iteration: int,
    *, reset_asserted: str = "!resetn",
) -> list[PropertyIR]:
    nodes = _assignment_nodes(graph)
    result = []
    for index, node_id in enumerate(
        [value for value in candidate["core_node_ids"] if value.startswith("assignment:")], 1
    ):
        node = nodes[node_id]
        result.append(property_from_assignment(
            node, candidate["region_id"], f"gap_i{iteration}_region_{index:03d}", iteration,
            reset_asserted=reset_asserted,
        ))
    return result


def select_contract_gap_assignments(
    mappings: list[dict[str, Any]], graph: dict[str, Any], *, focus_modules: list[str], limit: int,
) -> list[tuple[dict[str, Any], list[str], list[int]]]:
    nodes = _assignment_nodes(graph)
    grouped: dict[str, dict[str, Any]] = {}
    for gap in mappings:
        if gap["gap_type"] != "B_CONTRACT_GAP" or gap["module"] not in focus_modules:
            continue
        for node_id in gap["graph_node_ids"]:
            node = nodes.get(node_id)
            if not node or node.get("timing") != "next_cycle" or str(node.get("guard")) == "1'b1":
                continue
            row = grouped.setdefault(node_id, {"node": node, "regions": set(), "cids": set(), "score": 0})
            row["regions"].update(gap["existing_region_ids"])
            row["cids"].add(int(gap["cid"]))
            row["score"] += {"statement": 5, "branch": 4, "expression": 3}.get(gap["cover_item_type"], 1)
    selected = sorted(grouped.values(), key=lambda row: (-row["score"], row["node"]["id"]))[:limit]
    return [(row["node"], sorted(row["regions"]), sorted(row["cids"])) for row in selected]


def refine_local_contract(
    base_contracts: list[dict[str, Any]], selected: list[tuple[dict[str, Any], list[str], list[int]]],
    properties: list[PropertyIR], iteration: int,
) -> dict[str, Any]:
    region_ids = sorted({rid for _, rids, _ in selected for rid in rids})
    base = next((item for item in base_contracts if item.get("region_id") in region_ids), {})
    digest = hashlib.sha256("|".join(prop.property_id for prop in properties).encode()).hexdigest()[:12]
    events = []
    for node, _, _ in selected:
        events.append({
            "event_id": f"event_{hashlib.sha256(str(node['id']).encode()).hexdigest()[:12]}",
            "name": f"{node['lhs']}_updated", "predicate": str(node["lhs"]),
            "producer_node_id": node["id"], "guard": node.get("guard"),
        })
    return {
        "contract_id": f"local_contract_gap_refined_{digest}",
        "version_of_contract_id": base.get("contract_id"),
        "region_id": region_ids[0] if region_ids else "",
        "related_region_ids": region_ids, "module": selected[0][0]["module"] if selected else "",
        "object_type": base.get("object_type", "EXTENSION"),
        "readiness_level": 3, "iteration_added": iteration,
        "events": events, "trusted_local_obligation_ids": [prop.property_id for prop in properties],
        "gap_item_ids": sorted({cid for _, _, cids in selected for cid in cids}),
        "refinement_kind": "MISSING_LOCAL_OBLIGATION",
        "assumptions": [], "source": "formal-gap+existing-region+fixed-primitive",
    }


def compile_completion_composition(
    refined_contract: dict[str, Any], base_contracts: list[dict[str, Any]],
    graph: dict[str, Any], iteration: int, *, reset_asserted: str = "!resetn",
) -> tuple[dict[str, Any], PropertyIR]:
    """Connect same-guard completion outputs in two distinct Local Contracts."""

    assignments = list(_assignment_nodes(graph).values())
    refined_nodes = {
        str(event["producer_node_id"]): event for event in refined_contract.get("events", [])
    }
    candidates = []
    for target_id, target_event in refined_nodes.items():
        target = next((node for node in assignments if node["id"] == target_id), None)
        if not target or str(target.get("rhs")).strip() not in {"1", "1'b1"}:
            continue
        for source in assignments:
            if source["id"] == target_id or source.get("module") != target.get("module"):
                continue
            if str(source.get("rhs")).strip() not in {"1", "1'b1"}:
                continue
            if re.sub(r"\s+", "", str(source.get("guard"))) != re.sub(r"\s+", "", str(target.get("guard"))):
                continue
            source_contracts = [
                contract for contract in base_contracts
                if contract.get("module") == source.get("module")
                and any(
                    str(event.get("predicate", "")) == str(source["lhs"])
                    for event in (
                        contract.get("events", [])
                        or contract.get("interface", {}).get("events", [])
                    )
                )
            ]
            if source_contracts:
                candidates.append((source, target, source_contracts[0], target_event))
    if not candidates:
        raise RuntimeError("no exact same-guard completion relation for composition refinement")
    source, target, source_contract, target_event = sorted(
        candidates, key=lambda row: (row[0]["lhs"], row[1]["lhs"])
    )[0]
    relation_payload = "|".join((source_contract["contract_id"], refined_contract["contract_id"], source["lhs"], target["lhs"]))
    relation_id = "contract_edge_gap_" + hashlib.sha256(relation_payload.encode()).hexdigest()[:12]
    relation = {
        "relation_id": relation_id, "relation_type": "CAUSALITY",
        "source_contract_id": source_contract["contract_id"],
        "target_contract_id": refined_contract["contract_id"],
        "source_event": source["lhs"], "target_event": target["lhs"],
        "delay_range": [0, 0], "context_status": "STRONG",
        "evidence": [{
            "kind": "EXACT_SHARED_RTL_GUARD", "guard": source.get("guard"),
            "source_node_id": source["id"], "target_node_id": target["id"],
            "source_line": source.get("source", {}).get("line"),
            "target_line": target.get("source", {}).get("line"),
        }],
        "iteration_added": iteration, "assumptions": [],
    }
    signals = sorted({str(source["lhs"]), str(target["lhs"])})
    prop = PropertyIR(
        property_id=f"gap_i{iteration}_composition_001",
        region_id=f"contract_composition_{relation_id}", object_type=ObjectType.EXTENSION,
        family="COMPOSITE_ADJACENT", template="COMPOSITE_ADJACENT",
        bindings={
            "SOURCE_EVENT": source["lhs"], "TARGET_EVENT": target["lhs"],
            "SOURCE_CONTRACT_ID": source_contract["contract_id"],
            "TARGET_CONTRACT_ID": refined_contract["contract_id"], "DELAY_RANGE": [0, 0],
        }, signals=signals,
        source="formal-gap+contract-graph+exact-shared-guard+fixed-sequence-template",
        llm_confidence=1.0, body=f"({source['lhs']}) |-> ({target['lhs']})",
        disable_iff=reset_asserted,
        description=f"[REQ8.9 ITERATION {iteration}] adjacent completion Contract relation",
        source_classification="COMPOSITIONAL_CONTRACT", iteration_added=iteration,
        evidence=relation["evidence"], target_module=str(source["module"]),
    )
    return relation, prop


def candidate_score(
    *, cover_types: list[str], semantic_importance: float, proofability: float,
    novelty: float, overlap: float, formal_cost: float,
) -> dict[str, Any]:
    importance = sum({"statement": 3, "branch": 4, "expression": 4, "toggle": 1}.get(item, 1) for item in cover_types)
    total = importance + semantic_importance + proofability + novelty - overlap - formal_cost
    return {
        "coverage_importance": importance, "semantic_importance": semantic_importance,
        "proofability": proofability, "novel_verification_value": novelty,
        "overlap_penalty": overlap, "formal_cost_penalty": formal_cost,
        "total": round(total, 3),
    }


def incremental_update_audit(
    initial_regions: list[dict[str, Any]], initial_contracts: list[dict[str, Any]],
    initial_relations: list[dict[str, Any]], updates: list[dict[str, Any]],
    retained_property_ids: list[str], rerun_property_ids: list[str],
) -> dict[str, Any]:
    return {
        "schema": "region_flow.9-incremental-update-audit.v1",
        "initial": {"regions": len(initial_regions), "contracts": len(initial_contracts), "relations": len(initial_relations)},
        "updates": updates,
        "final": {
            "regions": len(initial_regions) + sum(update.get("new_regions", 0) for update in updates),
            "contracts": len(initial_contracts) + sum(update.get("new_contracts", 0) for update in updates),
            "relations": len(initial_relations) + sum(update.get("new_relations", 0) for update in updates),
        },
        "retained_verified_property_ids": sorted(retained_property_ids),
        "affected_targets_rerun": sorted(rerun_property_ids),
        "unrelated_targets_invalidated": 0,
        "whole_pipeline_reparsed_per_iteration": False,
        "targeted_validation_policy": "each iteration runs only newly affected properties; one final cumulative audit run measures the exact portfolio",
    }
