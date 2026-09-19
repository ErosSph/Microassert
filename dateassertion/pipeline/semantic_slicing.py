"""Graph-pattern-based microarchitecture region discovery (Requirement 8.4).

This module keeps the public Requirement-8 slicing API while replacing the
former case/name heuristics and ordinary undirected BFS with typed, directed
motif detection and bounded semantic expansion.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from pathlib import Path
import re
from typing import Any

from dateassertion.rtl_frontend.graph_patterns import detect_graph_patterns, directed_typed_expand
from dateassertion.rtl_frontend.parser import RTLDesign


def _safe_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_$]+", "_", value).strip("_").lower()


def _source_excerpt(file: str, lines: list[int], radius: int = 2, limit: int = 5000) -> str:
    path = Path(file)
    if not path.is_file() or not lines:
        return ""
    text = path.read_text(encoding="utf-8", errors="replace").splitlines()
    selected: set[int] = set()
    for line in lines:
        selected.update(range(max(1, line - radius), min(len(text), line + radius) + 1))
    return "\n".join(f"{line:6d}: {text[line - 1]}" for line in sorted(selected))[:limit]


def _add_rtl_context(slice_doc: dict[str, Any]) -> dict[str, Any]:
    files: dict[str, list[int]] = defaultdict(list)
    for item in slice_doc.get("nodes", []):
        if item.get("kind") != "assignment":
            continue
        source = item.get("source", {})
        if source.get("file") and source.get("line"):
            files[str(source["file"])].append(int(source["line"]))
    slice_doc["rtl_context"] = [
        {"file": file, "lines": sorted(set(lines)), "snippet": _source_excerpt(file, lines)}
        for file, lines in sorted(files.items())
    ]
    return slice_doc


def _module_boundary(design_map: dict[str, Any], module: str) -> list[dict[str, Any]]:
    boundary = []
    for edge in design_map.get("cross_module_dependencies", []):
        source, target = edge["source"], edge["target"]
        if source["module"] == module:
            boundary.append({**edge, "region_direction": "EXPORT"})
        elif target["module"] == module:
            boundary.append({**edge, "region_direction": "IMPORT"})
    return boundary


def _module_source(record: dict[str, Any]) -> dict[str, Any]:
    return dict(record.get("source", {}))


def _signal_names(module: str, node_ids: list[str]) -> list[str]:
    prefix = f"signal:{module}."
    return sorted(item[len(prefix):] for item in node_ids if item.startswith(prefix))


def _pattern_evidence(pattern: dict[str, Any], graph_nodes: dict[str, dict[str, Any]]) -> dict[str, Any]:
    sources = [
        graph_nodes[item].get("source", {}) for item in pattern.get("core_node_ids", [])
        if item in graph_nodes and graph_nodes[item].get("source", {}).get("file")
    ]
    if not sources:
        return {"file": "", "line_start": 0, "line_end": 0}
    file = str(sources[0]["file"])
    lines = [int(item.get("line", 0)) for item in sources if item.get("file") == file and item.get("line")]
    return {
        "file": file,
        "line_start": min(lines) if lines else 0,
        "line_end": max(lines) if lines else 0,
        "matched_features": pattern.get("matched_features", []),
    }


def _pattern_region(
    pattern: dict[str, Any], graph: dict[str, Any], design_map: dict[str, Any],
    all_pattern_core_nodes: set[str], *, depth: int, max_nodes: int,
) -> dict[str, Any]:
    module = pattern["module"]
    coi = _add_rtl_context(directed_typed_expand(
        graph, module, pattern["core_node_ids"], depth=depth, max_nodes=max_nodes,
        stop_core_nodes=all_pattern_core_nodes - set(pattern["core_node_ids"]),
    ))
    signals = _signal_names(module, coi["node_ids"])
    relevant = set(signals) | set(pattern.get("anchor_signals", []))
    boundary = [
        item for item in _module_boundary(design_map, module)
        if (item["source"]["module"] == module and item["source"]["signal"] in relevant)
        or (item["target"]["module"] == module and item["target"]["signal"] in relevant)
    ]
    imported = sorted({
        item["target"]["signal"] if item["target"]["module"] == module else item["source"]["signal"]
        for item in boundary if item["region_direction"] == "IMPORT"
    })
    exported = sorted({
        item["source"]["signal"] if item["source"]["module"] == module else item["target"]["signal"]
        for item in boundary if item["region_direction"] == "EXPORT"
    })
    nodes = {item["id"]: item for item in graph.get("nodes", [])}
    return {
        "region_id": "region_" + pattern["candidate_id"],
        "kind": pattern["kind"],
        "module": module,
        "seed_signals": sorted(set(pattern.get("anchor_signals", []))),
        "signals": signals,
        "core_node_ids": pattern["core_node_ids"],
        "coi": coi,
        "boundary": {
            "imported_signals": imported, "exported_signals": exported,
            "cross_edges": boundary, "semantic_cut_edges": coi["boundary_edges"],
            "explicit_stop_boundaries": coi["explicit_stop_boundaries"],
            "unresolved_dependencies": list(imported),
        },
        "evidence": _pattern_evidence(pattern, nodes),
        "score": pattern["score"], "pattern_scores": pattern["pattern_scores"],
        "score_semantics": pattern.get("score_semantics", "LEGACY_WEIGHTED_SCORE"),
        "detection_status": pattern["detection_status"],
        "matched_features": pattern["matched_features"],
        "match_certificate": pattern.get("match_certificate"),
        "slicing_basis": ["typed_directed_semantic_graph", pattern.get("decision_basis", "local_approximate_graph_pattern"), "bounded_producer_consumer_expansion"],
    }


def _module_region(
    module: str, record: dict[str, Any], graph: dict[str, Any], design_map: dict[str, Any],
    *, depth: int, max_nodes: int,
) -> dict[str, Any]:
    """Structural container only; never a functional classification."""
    module_nodes = [
        item["id"] for item in graph.get("nodes", [])
        if item.get("module") == module and item.get("kind") == "assignment"
    ]
    seeds = module_nodes[: min(16, len(module_nodes))]
    if seeds:
        coi = _add_rtl_context(directed_typed_expand(graph, module, seeds, depth=max(1, depth), max_nodes=max_nodes))
    else:
        coi = _add_rtl_context({
            "depth": depth, "max_nodes": max_nodes, "truncated": False,
            "node_ids": [], "nodes": [], "edges": [], "traversal_steps": [],
            "boundary_edges": [], "explicit_stop_boundaries": [],
            "policy": {"ordinary_undirected_bfs": False, "edge_types_preserved": True, "edge_direction_preserved": True},
        })
    boundary = _module_boundary(design_map, module)
    imported = sorted({
        item["target"]["signal"] if item["target"]["module"] == module else item["source"]["signal"]
        for item in boundary if item["region_direction"] == "IMPORT"
    })
    exported = sorted({
        item["source"]["signal"] if item["source"]["module"] == module else item["target"]["signal"]
        for item in boundary if item["region_direction"] == "EXPORT"
    })
    return {
        "region_id": f"region_module_{_safe_id(module)}", "kind": "MODULE", "module": module,
        "seed_signals": [], "signals": _signal_names(module, coi["node_ids"]),
        "core_node_ids": [], "coi": coi,
        "boundary": {
            "imported_signals": imported, "exported_signals": exported,
            "cross_edges": boundary, "semantic_cut_edges": coi["boundary_edges"],
            "explicit_stop_boundaries": coi["explicit_stop_boundaries"],
            "unresolved_dependencies": list(imported),
        },
        "evidence": _module_source(record), "score": 0.0, "pattern_scores": {},
        "detection_status": "STRUCTURAL_CONTAINER", "matched_features": [],
        "slicing_basis": ["hierarchical_module_container"],
    }


def _cross_region_edges(regions: list[dict[str, Any]], graph: dict[str, Any]) -> list[dict[str, Any]]:
    functional = [item for item in regions if item["kind"] != "MODULE"]
    membership: dict[str, set[str]] = defaultdict(set)
    for region in functional:
        # Cross-region semantics are defined between detected functional cores,
        # not between every pair of overlapping context nodes.  The latter is
        # a Cartesian explosion and does not add a stronger dependency fact.
        for node_id in region.get("core_node_ids", []):
            membership[node_id].add(region["region_id"])
    records: dict[tuple[str, str, str], dict[str, Any]] = {}
    for edge in graph.get("edges", []):
        source_members = sorted(
            membership.get(edge.get("source", ""), set()),
        )[:4]
        target_members = sorted(
            membership.get(edge.get("target", ""), set()),
        )[:4]
        for source_region in source_members:
            for target_region in target_members:
                if source_region == target_region:
                    continue
                key = (source_region, target_region, str(edge.get("type", "")))
                if key not in records:
                    records[key] = {
                        "source_region": source_region, "target_region": target_region,
                        "semantic_type": edge.get("type"), "source_node": edge.get("source"),
                        "target_node": edge.get("target"), "direction_preserved": True,
                        "edge_count": 0, "evidence_edges": [],
                    }
                records[key]["edge_count"] += 1
                if len(records[key]["evidence_edges"]) < 4:
                    records[key]["evidence_edges"].append({
                        "source_node": edge.get("source"), "target_node": edge.get("target"),
                        "evidence": edge.get("evidence", {}),
                    })
    return list(records.values())


def build_verification_regions(
    design: RTLDesign, graph: dict[str, Any], design_map: dict[str, Any], *,
    coi_depth: int = 2, max_nodes: int = 96, max_candidates_per_kind: int | None = None,
    matching_backend: str = "attributed_vf2",
) -> dict[str, Any]:
    """Discover functional regions from graph motifs, then expand locally."""
    pattern_doc = detect_graph_patterns(graph, max_candidates_per_kind=max_candidates_per_kind,
                                       matching_backend=matching_backend)
    module_records = {item["module"]: item for item in design_map["modules"]}
    all_core = {node_id for item in pattern_doc["patterns"] for node_id in item.get("core_node_ids", [])}
    regions = [
        _module_region(module, record, graph, design_map, depth=coi_depth, max_nodes=max_nodes)
        for module, record in sorted(module_records.items())
    ]
    regions.extend(
        _pattern_region(pattern, graph, design_map, all_core, depth=coi_depth + 2, max_nodes=max_nodes)
        for pattern in pattern_doc["patterns"] if pattern["module"] in module_records
    )
    module_region = {item["module"]: item["region_id"] for item in regions if item["kind"] == "MODULE"}
    functional = [item for item in regions if item["kind"] != "MODULE"]
    owner_records = []
    for state in design_map["ownership"]["state_registers"]:
        signal_id = f"signal:{state['module']}.{state['signal']}"
        owners = [item for item in functional if signal_id in item.get("core_node_ids", [])]
        owners.sort(key=lambda item: item["region_id"])
        owner_records.append({
            **state,
            "owner_region": owners[0]["region_id"] if owners else module_region[state["module"]],
            "overlapping_regions": [item["region_id"] for item in owners],
        })
    cross_edge_coverage = []
    for edge in design_map.get("cross_module_dependencies", []):
        owners = sorted({module_region.get(edge["source"]["module"], ""), module_region.get(edge["target"]["module"], "")} - {""})
        cross_edge_coverage.append({"edge_id": edge["id"], "regions": owners})
    cross_regions = _cross_region_edges(regions, graph)
    node_membership = Counter(node_id for item in functional for node_id in item["coi"]["node_ids"])
    counts = Counter(item["kind"] for item in regions)
    return {
        "schema": "region_flow.4-graph-pattern-regions.v1",
        "pattern_library": pattern_doc,
        "slicing_policy": {
            "mechanical_line_or_token_splitting": False, "ordinary_undirected_bfs": False,
            "signal_names_used_for_region_classification": False,
            "pattern_detection": pattern_doc["method"],
            "edge_types": ["DATA", "CONTROL", "SEQUENTIAL"], "edge_direction_preserved": True,
            "coi_depth": coi_depth, "max_nodes_per_region": max_nodes,
            "max_candidates_per_kind_per_module": max_candidates_per_kind,
            "candidate_truncation_count": pattern_doc["summary"]["truncated"],
            "cross_region_memberships_per_edge_endpoint": 4,
            "cross_region_evidence_examples_per_pair": 4,
            "boundaries": ["module", "another_pattern_core", "high_fanout_shared_control", "bounded_depth"],
        },
        "regions": sorted(regions, key=lambda item: (item["kind"] == "MODULE", item["region_id"])),
        "ownership": {"state_registers": owner_records},
        "cross_region_semantic_edges": cross_regions, "cross_edge_coverage": cross_edge_coverage,
        "summary": {
            "region_count": len(regions), "functional_region_count": len(functional),
            "by_kind": dict(counts),
            "by_detection_status": dict(Counter(item["detection_status"] for item in functional)),
            "state_registers": len(owner_records),
            "state_registers_with_owner": sum(bool(item["owner_region"]) for item in owner_records),
            "cross_edges": len(cross_edge_coverage),
            "cross_edges_assigned": sum(bool(item["regions"]) for item in cross_edge_coverage),
            "cross_region_semantic_edges": len(cross_regions),
            "overlapping_nodes": sum(count > 1 for count in node_membership.values()),
            "regions_with_imports": sum(bool(item["boundary"]["imported_signals"]) for item in regions),
        },
    }


def expand_region_context(
    region: dict[str, Any], graph: dict[str, Any], design_map: dict[str, Any], signals: list[str], *,
    depth_increment: int = 2, max_nodes: int = 192,
) -> dict[str, Any]:
    """Honor NEED_CONTEXT with another typed, directed bounded expansion."""
    expanded = dict(region)
    requested = sorted(set(signals))
    requested_ids = [f"signal:{region['module']}.{item}" for item in requested]
    core = sorted(set(region.get("core_node_ids", [])) | set(requested_ids))
    previous_depth = int(region.get("coi", {}).get("depth", 0))
    expanded["core_node_ids"] = core
    expanded["seed_signals"] = sorted(set(region.get("seed_signals", [])) | set(requested))
    expanded["coi"] = _add_rtl_context(directed_typed_expand(
        graph, region["module"], core, depth=previous_depth + depth_increment, max_nodes=max_nodes,
    ))
    expanded["signals"] = _signal_names(region["module"], expanded["coi"]["node_ids"])
    related = [
        edge for edge in design_map.get("cross_module_dependencies", [])
        if (edge["source"]["module"] == region["module"] and edge["source"]["signal"] in requested)
        or (edge["target"]["module"] == region["module"] and edge["target"]["signal"] in requested)
    ]
    edge_adjacency: dict[tuple[str, str, str], list[dict[str, Any]]] = defaultdict(list)
    for edge in design_map.get("cross_module_dependencies", []):
        for endpoint in (edge["source"], edge["target"]):
            edge_adjacency[(endpoint["instance_path"], endpoint["module"], endpoint["signal"])].append(edge)
    imported_context = []
    resolved_requests: set[str] = set()
    for first_edge in related:
        local = first_edge["source"] if first_edge["source"]["module"] == region["module"] else first_edge["target"]
        external = first_edge["target"] if local is first_edge["source"] else first_edge["source"]
        requested_local = local["signal"]
        queue = deque([(external, [first_edge["id"]], 0)])
        seen: set[tuple[str, str, str]] = set()
        while queue:
            endpoint, path_edges, distance = queue.popleft()
            key = (endpoint["instance_path"], endpoint["module"], endpoint["signal"])
            if key in seen:
                continue
            seen.add(key)
            external_coi = _add_rtl_context(directed_typed_expand(
                graph, endpoint["module"], [f"signal:{endpoint['module']}.{endpoint['signal']}"],
                depth=min(9, max(3, previous_depth)), max_nodes=128,
            ))
            has_semantics = any(item.get("kind") == "assignment" for item in external_coi["nodes"])
            imported_context.append({
                "requested_local_signal": requested_local, "external_endpoint": endpoint,
                "cross_edge_path": path_edges, "semantic_nodes": external_coi["nodes"],
                "semantic_edges": external_coi["edges"], "rtl_context": external_coi["rtl_context"],
                "terminal_semantics_found": has_semantics, "traversal_policy": external_coi["policy"],
            })
            if has_semantics:
                resolved_requests.add(requested_local)
            if distance >= 4 or has_semantics:
                continue
            for next_edge in edge_adjacency.get(key, []):
                other = next_edge["target"] if next_edge["source"] == endpoint else next_edge["source"]
                next_key = (other["instance_path"], other["module"], other["signal"])
                if next_key not in seen:
                    queue.append((other, path_edges + [next_edge["id"]], distance + 1))
    expanded_boundary = dict(region["boundary"])
    expanded_boundary["expanded_cross_edges"] = related
    expanded_boundary["imported_semantic_context"] = imported_context
    expanded_boundary["semantic_cut_edges"] = expanded["coi"]["boundary_edges"]
    expanded_boundary["unresolved_dependencies"] = sorted(set(expanded_boundary.get("unresolved_dependencies", [])) - resolved_requests)
    expanded["boundary"] = expanded_boundary
    expanded["context_expansion"] = {
        "requested_signals": requested, "resolved_cross_edges": [item["id"] for item in related],
        "resolved_requests": sorted(resolved_requests), "depth_before": previous_depth,
        "depth_after": expanded["coi"]["depth"], "typed_and_directed": True,
    }
    return expanded
