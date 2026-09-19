"""Typed, directed graph-pattern discovery for microarchitecture regions.

The detector intentionally does not inspect signal names.  Names are retained
only as source evidence after a topology has been matched.  This makes the
primary decision depend on DATA / CONTROL / SEQUENTIAL relationships, signal
width and port direction, assignment timing, and feedback/producer-consumer
structure.
"""

from __future__ import annotations

from collections import defaultdict, deque
from copy import deepcopy
import re
from typing import Any, Iterable


PRIMARY_PATTERNS = ("FSM", "DECODE", "HANDSHAKE", "PIPELINE")
ALL_PATTERNS = PRIMARY_PATTERNS + ("REGISTER_UPDATE", "DATAPATH", "COUNTER",
    "ACCUMULATOR", "SHIFTER", "COMPARATOR", "MULTIPLIER", "DIVIDER", "MUX", "ALU",
    "REGISTER_FILE", "LSU", "ITERATIVE_MULTIPLIER", "ITERATIVE_DIVIDER", "ONEHOT_PROGRESS")


def _node_module(node):
    return str(node.get("module", ""))


class TypedGraphIndex:
    """Direction- and type-preserving index over the semantic graph."""

    def __init__(self, graph: dict[str, Any]):
        self.graph = graph
        self.nodes = {item["id"]: item for item in graph.get("nodes", [])}
        self.outgoing: dict[str, dict[str, list[dict[str, Any]]]] = defaultdict(
            lambda: defaultdict(list)
        )
        self.incoming: dict[str, dict[str, list[dict[str, Any]]]] = defaultdict(
            lambda: defaultdict(list)
        )
        for edge in graph.get("edges", []):
            edge_type = str(edge.get("type", "UNKNOWN")).upper()
            self.outgoing[edge.get("source", "")][edge_type].append(edge)
            self.incoming[edge.get("target", "")][edge_type].append(edge)

        self.assignments_by_target: dict[str, list[str]] = defaultdict(list)
        self.assignment_target: dict[str, str] = {}
        self.assignment_inputs: dict[str, set[str]] = defaultdict(set)
        self.assignment_controls: dict[str, set[str]] = defaultdict(set)
        for node_id, node in self.nodes.items():
            if node.get("kind") != "assignment":
                continue
            for edge in self.outgoing[node_id].get("DATA", []):
                if self.is_signal(edge.get("target", "")):
                    self.assignment_target[node_id] = edge["target"]
                    self.assignments_by_target[edge["target"]].append(node_id)
            self.assignment_inputs[node_id] = {
                edge["source"] for edge in self.incoming[node_id].get("DATA", [])
                if self.is_signal(edge.get("source", ""))
            }
            self.assignment_controls[node_id] = {
                edge["source"] for edge in self.incoming[node_id].get("CONTROL", [])
                if self.is_signal(edge.get("source", ""))
            }

    def is_signal(self, node_id: str) -> bool:
        return self.nodes.get(node_id, {}).get("kind") == "signal"

    def is_assignment(self, node_id: str) -> bool:
        return self.nodes.get(node_id, {}).get("kind") == "assignment"

    def signal_width(self, node_id: str) -> int | None:
        value = self.nodes.get(node_id, {}).get("width")
        return int(value) if isinstance(value, int) else None

    def signal_direction(self, node_id: str) -> str:
        return str(self.nodes.get(node_id, {}).get("direction", "unknown"))

    def assignment_timing(self, assignment_id: str) -> str:
        return str(self.nodes.get(assignment_id, {}).get("timing", "unknown"))

    def controls(self, signal_id: str) -> set[str]:
        return {
            edge["target"] for edge in self.outgoing[signal_id].get("CONTROL", [])
            if self.is_assignment(edge.get("target", ""))
        }

    def sequential_successors(self, signal_id: str) -> set[str]:
        return {
            edge["target"] for edge in self.outgoing[signal_id].get("SEQUENTIAL", [])
            if self.is_signal(edge.get("target", ""))
        }

    def sequential_predecessors(self, signal_id: str) -> set[str]:
        return {
            edge["source"] for edge in self.incoming[signal_id].get("SEQUENTIAL", [])
            if self.is_signal(edge.get("source", ""))
        }


def detect_graph_patterns(graph: dict[str, Any], *, max_candidates_per_kind: int | None = None,
                          matching_backend: str = "attributed_vf2") -> dict[str, Any]:
    """Certified matching, or topology-only VF2 for controlled ablation."""
    if matching_backend not in {"attributed_vf2", "topology_vf2"}:
        raise ValueError(f"Unknown graph matching backend: {matching_backend}")
    from dateassertion.rtl_frontend.graph_motif_matching import match_graph_motifs
    return match_graph_motifs(graph, max_candidates_per_kind=max_candidates_per_kind,
                              feature_mode="full" if matching_backend == "attributed_vf2" else "topology")


def directed_typed_expand(
    graph: dict[str, Any],
    module: str,
    core_node_ids: Iterable[str],
    *,
    depth: int = 3,
    max_nodes: int = 96,
    high_fanout_limit: int = 24,
    stop_core_nodes: set[str] | None = None,
) -> dict[str, Any]:
    """Expand producers upstream and consumers downstream with explicit rules.

    Incoming traversal is used only for producer discovery and outgoing
    traversal only for consumer/effect discovery.  Every retained edge keeps
    its original type and orientation.
    """

    index = TypedGraphIndex(graph)
    seeds = [item for item in dict.fromkeys(core_node_ids) if item in index.nodes]
    visited = set(seeds)
    queue = deque((item, 0) for item in seeds)
    traversed: dict[tuple[str, str, str], dict[str, Any]] = {}
    boundaries: list[dict[str, Any]] = []
    stop_core_nodes = stop_core_nodes or set()

    def consider(edge: dict[str, Any], neighbor: str, distance: int, traversal: str) -> None:
        signature = (edge.get("type", ""), edge.get("source", ""), edge.get("target", ""))
        traversed[signature] = {**edge, "traversed_as": traversal}
        node = index.nodes.get(neighbor)
        if node is None or (_node_module(node) and _node_module(node) != module):
            boundaries.append({**edge, "boundary_reason": "module_boundary", "traversed_as": traversal})
            return
        if neighbor in stop_core_nodes and neighbor not in seeds:
            boundaries.append({**edge, "boundary_reason": "another_pattern_core", "traversed_as": traversal})
            return
        fanout = sum(len(values) for values in index.outgoing[neighbor].values())
        if fanout > high_fanout_limit and neighbor not in seeds:
            boundaries.append({**edge, "boundary_reason": "high_fanout_shared_control", "traversed_as": traversal})
            visited.add(neighbor)
            return
        if neighbor not in visited and len(visited) < max_nodes:
            visited.add(neighbor)
            queue.append((neighbor, distance + 1))

    while queue and len(visited) < max_nodes:
        node_id, distance = queue.popleft()
        if distance >= depth:
            continue
        node = index.nodes[node_id]
        kind = node.get("kind")
        if kind == "signal":
            # Producer discovery: assignment -> signal and prior-state -> signal.
            for edge in index.incoming[node_id].get("DATA", []):
                consider(edge, edge["source"], distance, "UPSTREAM_PRODUCER")
            for edge in index.incoming[node_id].get("SEQUENTIAL", []):
                consider(edge, edge["source"], distance, "UPSTREAM_SEQUENTIAL")
            # Consumer/effect discovery follows original edge direction.
            for edge_type in ("DATA", "CONTROL", "SEQUENTIAL"):
                for edge in index.outgoing[node_id].get(edge_type, []):
                    consider(edge, edge["target"], distance, f"DOWNSTREAM_{edge_type}")
        elif kind == "assignment":
            # An assignment's inputs/guards are producers; its target is effect.
            for edge_type in ("DATA", "CONTROL"):
                for edge in index.incoming[node_id].get(edge_type, []):
                    consider(edge, edge["source"], distance, f"UPSTREAM_{edge_type}")
            for edge in index.outgoing[node_id].get("DATA", []):
                consider(edge, edge["target"], distance, "DOWNSTREAM_EFFECT")

    selected_edges = [
        edge for edge in graph.get("edges", [])
        if edge.get("source") in visited and edge.get("target") in visited
    ]
    cut_edges = []
    for edge in graph.get("edges", []):
        source_in = edge.get("source") in visited
        target_in = edge.get("target") in visited
        if source_in == target_in:
            continue
        cut_edges.append({
            **edge,
            "region_direction": "EXPORT" if source_in else "IMPORT",
            "boundary_reason": "bounded_typed_expansion",
        })
    cut_edge_count = len(cut_edges)
    cut_edges = sorted(
        cut_edges,
        key=lambda item: (item.get("type", ""), item.get("source", ""), item.get("target", "")),
    )[:192]
    return {
        "depth": depth,
        "max_nodes": max_nodes,
        "truncated": bool(queue) or len(visited) >= max_nodes,
        "node_ids": sorted(visited),
        "nodes": [index.nodes[item] for item in sorted(visited)],
        "edges": selected_edges,
        "traversal_steps": list(traversed.values()),
        "boundary_edges": cut_edges,
        "boundary_edge_count": cut_edge_count,
        "explicit_stop_boundaries": boundaries,
        "policy": {
            "ordinary_undirected_bfs": False,
            "edge_types_preserved": True,
            "edge_direction_preserved": True,
            "upstream": ["DATA producer", "SEQUENTIAL predecessor", "CONTROL guard of selected assignment"],
            "downstream": ["DATA consumer", "CONTROL effect", "SEQUENTIAL successor"],
        },
    }


def anonymize_signal_names(graph: dict[str, Any]) -> tuple[dict[str, Any], dict[str, str]]:
    """Return a topology-identical graph with every signal identifier replaced."""

    copied = deepcopy(graph)
    signal_nodes = sorted(
        (item for item in copied.get("nodes", []) if item.get("kind") == "signal"),
        key=lambda item: (item.get("module", ""), item.get("id", "")),
    )
    counters: dict[str, int] = defaultdict(int)
    mapping: dict[str, str] = {}
    name_mapping: dict[tuple[str, str], str] = {}
    for node in signal_nodes:
        module = str(node.get("module", ""))
        counters[module] += 1
        anonymous = f"s{counters[module]:04d}"
        old_id = node["id"]
        mapping[old_id] = f"signal:{module}.{anonymous}"
        name_mapping[(module, str(node.get("name", "")))] = anonymous
        node["id"] = mapping[old_id]
        node["name"] = anonymous
        node["role"] = "redacted"

    def scrub_expression(value: Any, module: str) -> str:
        text = str(value or "")
        # Keep Verilog base digits (1'b0, 8'hff) intact while replacing every
        # identifier token.  Operators/constants are topology-adjacent facts;
        # lexical signal names are not.
        return re.sub(r"(?<!')\b[A-Za-z_][A-Za-z0-9_$]*\b",
                      lambda m: name_mapping.get((module, m[0]), m[0]), text)

    for node in copied.get("nodes", []):
        if node.get("constant_expression"):
            node["constant_expression"] = scrub_expression(node["constant_expression"], str(node.get("module", "")))
        if node.get("kind") == "assignment":
            module = str(node.get("module", ""))
            node["lhs"] = name_mapping.get((str(node.get("module", "")), str(node.get("lhs", ""))), "target")
            node["rhs"] = scrub_expression(node.get("rhs"), module)
            if node.get("lhs_expression"):
                node["lhs_expression"] = scrub_expression(node["lhs_expression"], module)
            node["guard"] = scrub_expression(node.get("guard"), module)
            node["clock"] = name_mapping.get((module, node.get("clock")), node.get("clock"))
            if node.get("event_control"):
                node["event_control"] = scrub_expression(node["event_control"], module)
            node["reset"] = [name_mapping.get((module, str(item)), f"reset_{index}") for index, item in enumerate(node.get("reset", []), start=1)]
        elif node.get("kind") == "expression":
            node["text"] = scrub_expression(node.get("text"), str(node.get("module", "")))
    for edge in copied.get("edges", []):
        edge["source"] = mapping.get(edge.get("source", ""), edge.get("source", ""))
        edge["target"] = mapping.get(edge.get("target", ""), edge.get("target", ""))
    for assignment in copied.get("assignments", []):
        module = str(assignment.get("module", ""))
        assignment["lhs"] = name_mapping.get((module, str(assignment.get("lhs", ""))), "target")
        assignment["rhs"] = scrub_expression(assignment.get("rhs"), module)
        if assignment.get("lhs_expression"):
            assignment["lhs_expression"] = scrub_expression(assignment["lhs_expression"], module)
        assignment["guard"] = scrub_expression(assignment.get("guard"), module)
    copied["name_ablation"] = {"all_signal_names_replaced": True, "mapping_size": len(mapping)}
    return copied, mapping


def ablation_signature(patterns: dict[str, Any]) -> dict[str, Any]:
    """Name-independent aggregate used to compare original and ablated runs."""

    records = patterns.get("patterns", [])
    primary = [item for item in records if item.get("kind") in PRIMARY_PATTERNS]
    return {
        "by_kind_and_status": {
            f"{kind}:{status}": sum(
                item.get("kind") == kind and item.get("detection_status") == status
                for item in primary
            )
            for kind in PRIMARY_PATTERNS for status in ("MATCH", "AMBIGUOUS")
        },
        "score_histogram": {
            kind: sorted(round(float(item.get("score", 0.0)), 2) for item in primary if item.get("kind") == kind)
            for kind in PRIMARY_PATTERNS
        },
    }
