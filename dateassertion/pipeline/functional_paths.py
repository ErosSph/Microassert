"""Region-graph construction and formal-query planning for Requirement 8.5.

The module is deliberately design independent.  Signal spelling is retained as
grounding evidence, but region activation and path selection use assignment
timing, port direction, typed graph edges, region kinds and bounded topology.
Static connectivity only creates candidates; it never validates execution.
"""

from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import re
from typing import Any

from dateassertion.ir.schema import ObjectType, PropertyIR
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


FUNCTIONAL_KINDS = {
    "DECODE", "HANDSHAKE", "REGISTER_UPDATE", "DATAPATH", "PIPELINE", "FSM",
}
EDGE_TYPES = {"DATA", "CONTROL", "SEQUENTIAL"}
TYPE_COMPATIBILITY = {
    "DECODE": {"HANDSHAKE", "REGISTER_UPDATE", "DATAPATH", "PIPELINE", "FSM"},
    "HANDSHAKE": {"HANDSHAKE", "REGISTER_UPDATE", "DATAPATH", "PIPELINE", "FSM"},
    "REGISTER_UPDATE": {"HANDSHAKE", "DATAPATH", "PIPELINE", "FSM"},
    "DATAPATH": {"HANDSHAKE", "REGISTER_UPDATE", "DATAPATH", "PIPELINE", "FSM"},
    "PIPELINE": {"HANDSHAKE", "REGISTER_UPDATE", "DATAPATH", "PIPELINE", "FSM"},
    "FSM": {"HANDSHAKE", "REGISTER_UPDATE", "DATAPATH", "PIPELINE"},
}


def _safe_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_$]+", "_", value).strip("_").lower()


def _assignment_id(index: int) -> str:
    return f"assignment:{index}"


def _literal_int(value: str) -> int | None:
    text = re.sub(r"[\s()]", "", value).lower()
    if text in {"0", "'0"}:
        return 0
    if text in {"1", "'1"}:
        return 1
    match = re.fullmatch(r"(?:\d+)?'([bodh])([0-9a-f_]+)", text)
    if match:
        base = {"b": 2, "o": 8, "d": 10, "h": 16}[match.group(1)]
        try:
            return int(match.group(2).replace("_", ""), base)
        except ValueError:
            return None
    return None


def _predicate_complexity(value: str) -> int:
    return len(re.findall(r"[A-Za-z_][A-Za-z0-9_$]*|&&|\|\||==|!=|<=|>=", value))


def _signal_node_name(node_id: str) -> str:
    return node_id.split(".", 1)[1] if node_id.startswith("signal:") and "." in node_id else ""


def _predicate_grounded(expression: str, design: RTLDesign, module: str) -> bool:
    names = expression_signals(expression)
    known = set(design.module_signals.get(module, {}))
    return bool(expression.strip()) and names <= known


def _candidate_role(rhs: str, width: str, guard: str) -> str:
    literal = _literal_int(rhs)
    if not width and literal == 1:
        return "EVENT"
    if not width and literal == 0 and guard:
        return "EXIT_OR_CLEAR"
    return "UPDATE"


def extract_activation_predicate(
    region: dict[str, Any], design: RTLDesign, *, reset: str = "resetn",
) -> dict[str, Any]:
    """Extract one auditable activation predicate plus ranked alternatives.

    A region is activated by a guarded core update, an event-setting update, or
    (for a one-bit feedback/FSM anchor) its active state.  Constant defaults and
    reset clears are evidence but are not selected as functional activations.
    """

    module = region["module"]
    signals = design.module_signals.get(module, {})
    core = set(region.get("core_node_ids", []))
    local_context = core | set(region.get("coi", {}).get("node_ids", []))
    anchors = set(region.get("seed_signals", []))
    candidates: list[dict[str, Any]] = []
    assignments = {
        _assignment_id(index): assignment
        for index, assignment in enumerate(design.assignments, start=1)
        if assignment.module == module
    }

    if region.get("kind") == "FSM":
        for anchor in sorted(anchors):
            signal = signals.get(anchor)
            producers = [item for item in assignments.values() if item.lhs == anchor]
            values = {_literal_int(item.rhs) for item in producers}
            if signal and not signal.width and {0, 1} <= values:
                candidates.append({
                    "candidate_id": f"activation_{_safe_id(region['region_id'])}_active_{_safe_id(anchor)}",
                    "predicate": anchor,
                    "role": "ACTIVE",
                    "assignment_id": "",
                    "target": anchor,
                    "source": {"file": signal.file, "line": signal.line},
                    "structural_facts": ["one_bit_anchor", "set_and_clear_feedback_state"],
                })

    for assignment_id, assignment in assignments.items():
        if assignment_id not in local_context:
            continue
        target = signals.get(assignment.lhs)
        if target is None:
            continue
        guard = assignment.guard.strip()
        literal = _literal_int(assignment.rhs)
        is_anchor = assignment.lhs in anchors
        reset_only_guard = bool(guard and expression_signals(guard) <= {reset})
        default_constant = not guard and literal is not None
        if reset_only_guard or default_constant:
            continue
        predicate = guard
        if not predicate and not target.width and literal == 1:
            predicate = assignment.lhs
        if not predicate or not _predicate_grounded(predicate, design, module):
            continue
        candidates.append({
            "candidate_id": f"activation_{_safe_id(region['region_id'])}_{assignment_id.replace(':', '_')}",
            "predicate": predicate,
            "role": _candidate_role(assignment.rhs, target.width, guard),
            "assignment_id": assignment_id,
            "target": assignment.lhs,
            "source": {"file": assignment.file, "line": assignment.line},
            "structural_facts": [
                "core_assignment" if assignment_id in core else "bounded_coi_assignment",
                "anchor_target" if is_anchor else "context_target",
                "guarded_update" if guard else "event_value",
                f"target_direction:{target.direction}",
                f"assignment_timing:{assignment.kind}",
            ],
            "predicate_complexity": _predicate_complexity(predicate),
            "is_core_assignment": assignment_id in core,
        })

    # Remove semantic duplicates while retaining the strongest evidence record.
    deduplicated: dict[str, dict[str, Any]] = {}
    for item in candidates:
        deduplicated.setdefault(re.sub(r"\s+", "", item["predicate"]), item)
    candidates = list(deduplicated.values())

    kind = region.get("kind")

    def rank(item: dict[str, Any]) -> tuple[Any, ...]:
        target = signals.get(item.get("target", ""))
        direction = target.direction if target else ""
        role_order = {
            "DECODE": {"EVENT": 0, "UPDATE": 1, "ACTIVE": 2, "EXIT_OR_CLEAR": 3},
            "HANDSHAKE": {"EVENT": 0, "UPDATE": 1, "ACTIVE": 2, "EXIT_OR_CLEAR": 3},
            "FSM": {"ACTIVE": 0, "EVENT": 1, "UPDATE": 2, "EXIT_OR_CLEAR": 3},
        }.get(kind, {"UPDATE": 0, "EVENT": 1, "ACTIVE": 2, "EXIT_OR_CLEAR": 3})
        output_first = kind in {"HANDSHAKE", "PIPELINE"} and direction == "output"
        anchor_first = item.get("target") in anchors
        core_first = bool(item.get("is_core_assignment"))
        if kind == "HANDSHAKE":
            structural_prefix = (-int(anchor_first), -int(output_first), -int(core_first))
        elif kind == "FSM":
            # An FSM region's active state is a more stable transaction
            # activation than one particular entry/exit assignment.  The
            # latter remain alternatives and are used as edge evidence.
            structural_prefix = (role_order.get(item["role"], 9), -int(core_first), -int(anchor_first))
        else:
            structural_prefix = (-int(core_first), -int(anchor_first), -int(output_first))
        role_suffix = () if kind == "FSM" else (role_order.get(item["role"], 9),)
        return (
            *structural_prefix,
            *role_suffix,
            int(item.get("predicate_complexity", 0)), int(item.get("source", {}).get("line", 0)),
            item["candidate_id"],
        )

    candidates.sort(key=rank)
    if not candidates:
        return {
            "status": "UNKNOWN", "predicate": "", "role": "UNKNOWN",
            "reason": "no non-default grounded core activation event", "alternatives": [],
        }
    selected = candidates[0]
    return {
        "status": "GROUNDED",
        "predicate": selected["predicate"],
        "role": selected["role"],
        "candidate_id": selected["candidate_id"],
        "assignment_id": selected.get("assignment_id", ""),
        "target": selected.get("target", ""),
        "source": selected.get("source", {}),
        "reason": "deterministic structural ranking of grounded core activation evidence",
        "alternatives": candidates,
    }


def build_region_graph(
    regions_doc: dict[str, Any], graph: dict[str, Any], design: RTLDesign,
    *, reset: str = "resetn",
) -> dict[str, Any]:
    """Aggregate Req8.4 regions and typed RTL evidence into a high-level graph."""

    regions = {
        item["region_id"]: item for item in regions_doc.get("regions", [])
        if item.get("kind") in FUNCTIONAL_KINDS
        and item.get("detection_status") in {"MATCH", "LLM_VALIDATED"}
    }
    nodes = []
    for region_id, region in sorted(regions.items()):
        nodes.append({
            "region_id": region_id,
            "module": region["module"],
            "kind": region["kind"],
            "pattern_score": float(region.get("score", 0.0)),
            "core_node_ids": region.get("core_node_ids", []),
            "boundary_signals": sorted(set(region.get("seed_signals", []))),
            "activation": extract_activation_predicate(region, design, reset=reset),
            "evidence": region.get("evidence", {}),
        })
    node_by_id = {item["region_id"]: item for item in nodes}

    grouped: dict[tuple[str, str, str], dict[str, Any]] = {}
    for raw in regions_doc.get("cross_region_semantic_edges", []):
        source_id, target_id = raw.get("source_region"), raw.get("target_region")
        semantic_type = str(raw.get("semantic_type", ""))
        if source_id not in node_by_id or target_id not in node_by_id or semantic_type not in EDGE_TYPES:
            continue
        source, target = node_by_id[source_id], node_by_id[target_id]
        if source["module"] != target["module"]:
            scope = "CROSS_MODULE"
        else:
            scope = "CROSS_REGION_INTRA_MODULE"
        if source["activation"]["status"] != "GROUNDED" or target["activation"]["status"] != "GROUNDED":
            continue
        if re.sub(r"\s+", "", source["activation"]["predicate"]) == re.sub(r"\s+", "", target["activation"]["predicate"]):
            continue
        compatible = target["kind"] in TYPE_COMPATIBILITY.get(source["kind"], set())
        if not compatible:
            continue
        key = (source_id, target_id, semantic_type)
        evidence = list(raw.get("evidence_edges", []))
        source_activation_signals = expression_signals(source["activation"]["predicate"])
        boundary = {
            _signal_node_name(str(raw.get("source_node", ""))),
            _signal_node_name(str(raw.get("target_node", ""))),
        } - {""}
        target_activation_node = target["activation"].get("assignment_id", "")
        target_activation_signal = target["activation"].get("target", "")
        event_alignment = bool(
            source_activation_signals & boundary
            or target_activation_node in {raw.get("source_node"), raw.get("target_node")}
            or target_activation_signal in boundary
        )
        facts = [
            semantic_type in EDGE_TYPES,
            bool(evidence),
            source["module"] == target["module"],
            compatible,
            bool(set(source["core_node_ids"]) ^ set(target["core_node_ids"])),
            event_alignment,
        ]
        grouped[key] = {
            "edge_id": "region_edge_" + hashlib.sha1("|".join(key).encode()).hexdigest()[:12],
            "source_region": source_id,
            "target_region": target_id,
            "edge_type": semantic_type,
            "scope": scope,
            "underlying_rtl_nodes": sorted({
                str(raw.get("source_node", "")), str(raw.get("target_node", ""))
            } - {""}),
            "underlying_rtl_edges": evidence,
            "source_locations": [item.get("evidence", {}) for item in evidence],
            "boundary_signals": sorted(boundary),
            "edge_count": int(raw.get("edge_count", 0)),
            "structural_constraints": {
                "typed_edge": facts[0], "rtl_evidence": facts[1],
                "same_module_v1": facts[2], "type_compatible": facts[3],
                "nonidentical_cores": facts[4], "activation_evidence_aligned": facts[5],
            },
            "normalized_structural_similarity": round(sum(facts) / len(facts), 6),
        }
    edges = sorted(grouped.values(), key=lambda item: (
        item["source_region"], item["target_region"], item["edge_type"]
    ))
    return {
        "schema": "region_flow.5-region-graph.v1",
        "nodes": nodes,
        "edges": edges,
        "policy": {
            "source": "Req8.4 typed directed semantic graph and functional regions",
            "edge_types": sorted(EDGE_TYPES),
            "signal_names_used_for_path_scoring": False,
            "static_connectivity_is_validation": False,
            "cross_region_classes": ["LOCAL", "CROSS_REGION_INTRA_MODULE", "CROSS_MODULE"],
            "v1_formal_scope": "CROSS_REGION_INTRA_MODULE",
            "pattern_scoring": "core constraints plus normalized structural similarity",
        },
        "summary": {
            "region_nodes": len(nodes), "region_edges": len(edges),
            "activation_grounded": sum(item["activation"]["status"] == "GROUNDED" for item in nodes),
            "activation_unknown": sum(item["activation"]["status"] == "UNKNOWN" for item in nodes),
            "edges_by_type": dict(Counter(item["edge_type"] for item in edges)),
            "edges_by_scope": dict(Counter(item["scope"] for item in edges)),
        },
    }


def discover_candidate_paths(
    region_graph: dict[str, Any], *, min_regions: int = 2, max_regions: int = 5,
    max_paths_per_module: int = 6, max_outgoing: int = 6,
    max_pair_candidates_per_module: int = 24,
) -> dict[str, Any]:
    """Bounded typed path discovery; never enumerates arbitrary full-graph paths."""

    nodes = {item["region_id"]: item for item in region_graph.get("nodes", [])}
    outgoing: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in region_graph.get("edges", []):
        if edge["scope"] != "CROSS_REGION_INTRA_MODULE":
            continue
        source, target = nodes[edge["source_region"]], nodes[edge["target_region"]]
        left, right = set(source["core_node_ids"]), set(target["core_node_ids"])
        overlap = len(left & right) / len(left | right) if left | right else 0.0
        copied = dict(edge)
        copied["core_jaccard"] = round(overlap, 6)
        if overlap < 0.9:
            outgoing[edge["source_region"]].append(copied)
    for source_id in outgoing:
        outgoing[source_id].sort(key=lambda item: (
            -item["normalized_structural_similarity"], item["core_jaccard"],
            -nodes[item["target_region"]]["pattern_score"], item["target_region"], item["edge_type"],
        ))
        # Dense overlapping Req8.4 regions often yield DATA/CONTROL/SEQUENTIAL
        # variants and several region IDs for the same target event.  Spend the
        # outgoing budget on distinct activation events, not duplicate graph
        # encodings of one event.
        distinct_targets: dict[str, dict[str, Any]] = {}
        for edge in outgoing[source_id]:
            predicate = re.sub(
                r"\s+", "", nodes[edge["target_region"]]["activation"]["predicate"]
            )
            distinct_targets.setdefault(predicate, edge)
        outgoing[source_id] = list(distinct_targets.values())[:max_outgoing]

    raw_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    starts = [
        item for item in nodes.values()
        if item["kind"] in {"DECODE", "HANDSHAKE"}
        and item["activation"]["status"] == "GROUNDED"
    ]

    def emit(path_nodes: list[str], path_edges: list[dict[str, Any]]) -> None:
        if len(path_nodes) < min_regions:
            return
        records = [nodes[item] for item in path_nodes]
        kinds = [item["kind"] for item in records]
        if len(set(kinds)) < 2:
            return
        if len(path_nodes) >= 3 and not ({"FSM", "DATAPATH", "PIPELINE", "REGISTER_UPDATE"} & set(kinds)):
            return
        predicates = [re.sub(r"\s+", "", item["activation"]["predicate"]) for item in records]
        if len(predicates) != len(set(predicates)):
            return
        edge_types = [item["edge_type"] for item in path_edges]
        features = [
            sum(item["normalized_structural_similarity"] for item in path_edges) / len(path_edges),
            len(set(kinds)) / len(kinds),
            len(set(edge_types)) / len(EDGE_TYPES),
            1.0 if kinds[0] == "DECODE" else 0.0,
            1.0 if kinds[-1] in {"HANDSHAKE", "REGISTER_UPDATE"} else 0.0,
        ]
        digest = hashlib.sha1("|".join(path_nodes + [item["edge_id"] for item in path_edges]).encode()).hexdigest()[:12]
        raw_by_module[records[0]["module"]].append({
            "path_id": f"candidate_path_{digest}",
            "module": records[0]["module"],
            "regions": path_nodes,
            "region_kinds": kinds,
            "region_edges": [item["edge_id"] for item in path_edges],
            "edge_types": edge_types,
            "activation_predicates": [item["activation"]["predicate"] for item in records],
            "activation_roles": [item["activation"]["role"] for item in records],
            "normalized_structural_similarity": round(sum(features) / len(features), 6),
            "static_evidence": [
                {key: edge[key] for key in (
                    "edge_id", "source_region", "target_region", "edge_type",
                    "underlying_rtl_nodes", "underlying_rtl_edges", "source_locations", "boundary_signals",
                )}
                for edge in path_edges
            ],
            "validation_status": "NOT_FORMALLY_VALIDATED",
        })

    def walk(current: str, path_nodes: list[str], path_edges: list[dict[str, Any]]) -> None:
        emit(path_nodes, path_edges)
        if len(path_nodes) >= max_regions:
            return
        for edge in outgoing.get(current, []):
            target = edge["target_region"]
            if target in path_nodes or nodes[target]["module"] != nodes[current]["module"]:
                continue
            walk(target, path_nodes + [target], path_edges + [edge])

    # Adjacent-event relation discovery is not restricted to Decode/Handshake
    # starts.  These pair candidates are the Formal-validated edges from which
    # longer execution paths are composed.
    for source_id, edges in sorted(outgoing.items()):
        for edge in edges:
            emit([source_id, edge["target_region"]], [edge])

    for start in sorted(starts, key=lambda item: (item["module"], item["kind"] != "DECODE", -item["pattern_score"], item["region_id"])):
        walk(start["region_id"], [start["region_id"]], [])

    selected = []
    generated = sum(len(items) for items in raw_by_module.values())
    for module, items in sorted(raw_by_module.items()):
        unique: dict[tuple[str, ...], dict[str, Any]] = {}
        for item in items:
            # Req8.4 regions overlap by design.  Distinct region IDs that
            # produce the same activation sequence are one functional-path
            # candidate, not independent evidence.
            signature = tuple(re.sub(r"\s+", "", value) for value in item["activation_predicates"])
            current = unique.get(signature)
            if current is None or item["normalized_structural_similarity"] > current["normalized_structural_similarity"]:
                unique[signature] = item
        ranked = sorted(unique.values(), key=lambda item: (
            -item["normalized_structural_similarity"],
            -len(set(item["region_kinds"])), item["path_id"],
        ))
        # Preserve multiple bounded lengths.  Always taking the longest paths
        # biases a dense overlapping graph toward spurious detours and can hide
        # the shorter executable chain that Formal is meant to validate.
        by_length: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for item in ranked:
            by_length[len(item["regions"])].append(item)
        module_selected: list[dict[str, Any]] = []
        while len(module_selected) < max_paths_per_module and any(by_length.values()):
            for length in range(max_regions, min_regions - 1, -1):
                if by_length[length] and len(module_selected) < max_paths_per_module:
                    module_selected.append(by_length[length].pop(0))
        selected.extend(module_selected)
        # Formal-guided synthesis needs a sufficiently complete adjacent-event
        # relation set.  Retain a separate bounded pair budget so longer static
        # candidates cannot crowd out the executable backbone edges.
        pair_candidates = [item for item in ranked if len(item["regions"]) == 2]
        selected_ids = {item["path_id"] for item in module_selected}
        selected.extend(
            item for item in pair_candidates[:max_pair_candidates_per_module]
            if item["path_id"] not in selected_ids
        )
    selected.sort(key=lambda item: (item["module"], -len(item["regions"]), item["path_id"]))
    return {
        "schema": "region_flow.5-candidate-functional-paths.v1",
        "policy": {
            "bounded_regions": [min_regions, max_regions],
            "arbitrary_length_enumeration": False,
            "max_paths_per_module": max_paths_per_module,
            "max_pair_candidates_per_module": max_pair_candidates_per_module,
            "max_outgoing_per_region": max_outgoing,
            "static_candidate_is_validated_path": False,
        },
        "paths": selected,
        "summary": {
            "raw_bounded_paths": generated,
            "candidate_paths": len(selected),
            "by_module": dict(Counter(item["module"] for item in selected)),
            "by_length": dict(Counter(str(len(item["regions"])) for item in selected)),
        },
    }


def _query_property(
    query_id: str, module: str, body: str, signals: set[str], *, reset_asserted: str,
) -> PropertyIR:
    return PropertyIR(
        property_id=query_id,
        region_id=query_id,
        object_type=ObjectType.EXTENSION,
        family="FUNCTIONAL_PATH_FORMAL_QUERY",
        template="FUNCTIONAL_PATH_QUERY",
        bindings={},
        signals=sorted(signals),
        source="region-graph-formal-validation-query",
        llm_confidence=0.0,
        body=body,
        disable_iff=reset_asserted,
        description="Req8.5 formal path validation query; not a verification portfolio assertion.",
        source_classification="RTL_STRUCTURAL",
        target_module=module,
    )


def build_formal_path_queries(
    candidate_doc: dict[str, Any], region_graph: dict[str, Any], *,
    reset_asserted: str = "!resetn", ordering_bound: int = 48,
) -> tuple[list[PropertyIR], dict[str, dict[str, Any]]]:
    """Build reachability, possible-order, dominance and progress queries.

    Possible ordering is encoded as a tautological implication whose complete
    sequence is the antecedent.  Jasper's generated ``:precondition`` target is
    therefore an exact cover query for that bounded event sequence.
    """

    nodes = {item["region_id"]: item for item in region_graph["nodes"]}
    properties: list[PropertyIR] = []
    metadata: dict[str, dict[str, Any]] = {}
    seen: set[tuple[str, ...]] = set()

    for path in candidate_doc.get("paths", []):
        for region_id in path["regions"]:
            key = ("REACHABILITY", region_id)
            if key in seen:
                continue
            seen.add(key)
            activation = nodes[region_id]["activation"]["predicate"]
            query_id = "req85_reach_" + hashlib.sha1(region_id.encode()).hexdigest()[:12]
            prop = _query_property(
                query_id, path["module"], f"({activation}) |-> 1'b1",
                expression_signals(activation), reset_asserted=reset_asserted,
            )
            properties.append(prop)
            metadata[query_id] = {
                "query_type": "REACHABILITY", "region_id": region_id,
                "activation_predicate": activation, "path_ids": [path["path_id"]],
            }
        for left_id, right_id in zip(path["regions"], path["regions"][1:]):
            left = nodes[left_id]["activation"]["predicate"]
            right = nodes[right_id]["activation"]["predicate"]
            pair = (left_id, right_id)
            for query_type in ("ORDERING_POSSIBLE", "DOMINANCE", "PROGRESS"):
                key = (query_type, *pair)
                if key in seen:
                    query = next((item for item in metadata.values() if item.get("dedup_key") == list(key)), None)
                    if query and path["path_id"] not in query["path_ids"]:
                        query["path_ids"].append(path["path_id"])
                    continue
                seen.add(key)
                digest = hashlib.sha1("|".join(key).encode()).hexdigest()[:12]
                query_id = f"req85_{query_type.lower()}_{digest}"
                if query_type == "ORDERING_POSSIBLE":
                    body = f"(({left}) ##[0:{ordering_bound}] ({right})) |-> 1'b1"
                elif query_type == "DOMINANCE":
                    history = " || ".join(
                        [f"({left})"] + [f"$past(({left}), {delay})" for delay in range(1, ordering_bound + 1)]
                    )
                    body = f"({right}) |-> ({history})"
                else:
                    body = f"({left}) |-> ##[0:{ordering_bound}] ({right})"
                prop = _query_property(
                    query_id, path["module"], body,
                    expression_signals(left) | expression_signals(right),
                    reset_asserted=reset_asserted,
                )
                properties.append(prop)
                metadata[query_id] = {
                    "query_type": query_type, "source_region": left_id,
                    "target_region": right_id, "source_activation": left,
                    "target_activation": right, "bound": ordering_bound,
                    "path_ids": [path["path_id"]], "dedup_key": list(key),
                }
    return properties, metadata


def classify_formal_paths(
    candidate_doc: dict[str, Any], query_metadata: dict[str, dict[str, Any]],
    formal_result: Any,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Interpret formal query results without asking an LLM to judge dynamics."""

    results = {item.property_id: item for item in formal_result.results}
    reachability: list[dict[str, Any]] = []
    dominance: list[dict[str, Any]] = []
    exclusivity: list[dict[str, Any]] = []
    ordering: list[dict[str, Any]] = []
    progress: dict[tuple[str, str], dict[str, Any]] = {}

    for query_id, meta in query_metadata.items():
        result = results.get(query_id)
        if result is None:
            status, vacuity = "UNKNOWN", "UNKNOWN"
        else:
            status, vacuity = result.result, result.vacuity or "UNKNOWN"
        common = {
            **{key: value for key, value in meta.items() if key != "dedup_key"},
            "query_id": query_id, "formal_result": status, "vacuity": vacuity,
            "runtime_seconds": result.runtime_seconds if result else None,
        }
        if meta["query_type"] == "REACHABILITY":
            common["status"] = (
                "REACHABLE" if status == "PASS" and vacuity == "NON_VACUOUS" else
                "UNREACHABLE" if vacuity == "VACUOUS" else "UNKNOWN"
            )
            reachability.append(common)
        elif meta["query_type"] == "ORDERING_POSSIBLE":
            common["status"] = (
                "ORDERED_REACHABLE" if status == "PASS" and vacuity == "NON_VACUOUS" else
                "ORDERED_UNREACHABLE_WITHIN_BOUND" if vacuity == "VACUOUS" else "UNKNOWN"
            )
            ordering.append(common)
            exclusivity.append({
                **common,
                "status": (
                    "NOT_EXCLUSIVE_WITHIN_BOUND" if common["status"] == "ORDERED_REACHABLE" else
                    "EXCLUSIVE_OR_OUT_OF_BOUND" if common["status"] == "ORDERED_UNREACHABLE_WITHIN_BOUND" else
                    "UNKNOWN"
                ),
                "interpretation": "bounded ordered co-occurrence; not an unbounded transaction-equivalence proof",
            })
        elif meta["query_type"] == "DOMINANCE":
            common["status"] = (
                "BOUNDED_DOMINANCE_PROVEN" if status == "PASS" and vacuity == "NON_VACUOUS" else
                "NOT_DOMINANT" if status == "FAIL" else "UNKNOWN"
            )
            dominance.append(common)
        else:
            common["status"] = (
                "BOUNDED_PROGRESS_PROVEN" if status == "PASS" and vacuity == "NON_VACUOUS" else
                "PROGRESS_CEX" if status == "FAIL" else "UNKNOWN"
            )
            progress[(meta["source_region"], meta["target_region"])] = common

    reach_by_region = {item["region_id"]: item for item in reachability}
    order_by_pair = {(item["source_region"], item["target_region"]): item for item in ordering}
    dom_by_pair = {(item["source_region"], item["target_region"]): item for item in dominance}
    validated = []
    rejected = Counter()
    for path in candidate_doc.get("paths", []):
        pairs = list(zip(path["regions"], path["regions"][1:]))
        reach = [reach_by_region.get(item, {"status": "UNKNOWN"}) for item in path["regions"]]
        orders = [order_by_pair.get(item, {"status": "UNKNOWN"}) for item in pairs]
        if any(item["status"] == "UNREACHABLE" for item in reach):
            rejected["reachability"] += 1
            continue
        if any(item["status"] != "REACHABLE" for item in reach):
            rejected["reachability_unknown"] += 1
            continue
        if any(item["status"] == "ORDERED_UNREACHABLE_WITHIN_BOUND" for item in orders):
            rejected["dominance_or_exclusivity"] += 1
            continue
        if any(item["status"] != "ORDERED_REACHABLE" for item in orders):
            rejected["ordering_unknown"] += 1
            continue
        # A coverable A-before-B sequence alone can join two unrelated
        # transactions.  Require a directional same-context fact for every
        # adjacent pair: either A necessarily progresses to B or every B is
        # bounded-dominated by A.
        if any(
            progress.get(pair, {}).get("status") != "BOUNDED_PROGRESS_PROVEN"
            and dom_by_pair.get(pair, {}).get("status") != "BOUNDED_DOMINANCE_PROVEN"
            for pair in pairs
        ):
            rejected["no_same_context_causality"] += 1
            continue
        support = []
        for pair in pairs:
            support.append(order_by_pair[pair]["status"] == "ORDERED_REACHABLE")
            support.append(dom_by_pair.get(pair, {}).get("status") == "BOUNDED_DOMINANCE_PROVEN")
            support.append(progress.get(pair, {}).get("status") == "BOUNDED_PROGRESS_PROVEN")
        mandatory_relations = []
        for left, right in pairs:
            pair = (left, right)
            progress_record = progress[pair]
            if progress_record["status"] == "BOUNDED_PROGRESS_PROVEN":
                mandatory_relations.append({
                    "source_region": left, "target_region": right,
                    "causality_type": "PROGRESS", **progress_record,
                })
            else:
                mandatory_relations.append({
                    "source_region": left, "target_region": right,
                    "causality_type": "BOUNDED_DOMINANCE", **dom_by_pair[pair],
                })
        validated.append({
            **path,
            "validation_status": "FORMALLY_VALIDATED",
            "reachability_results": [item["query_id"] for item in reach],
            "dominance_results": [dom_by_pair[item]["query_id"] for item in pairs],
            "exclusivity_results": [order_by_pair[item]["query_id"] for item in pairs],
            "ordering_results": [order_by_pair[item]["query_id"] for item in pairs],
            "progress_results": [progress[item]["query_id"] for item in pairs],
            "formal_confidence": round(sum(support) / len(support), 6) if support else 0.0,
            "mandatory_adjacent_relations": mandatory_relations,
            "function_context": "AMBIGUOUS",
        })

    # Compose longer FRPs from independently validated strong adjacent event
    # relations.  Joining is by the exact grounded activation predicate, so
    # overlapping Req8.4 region IDs cannot prevent composition and unrelated
    # transactions cannot be joined merely because they are coverable in one
    # 48-cycle window.
    strong_pairs = [item for item in validated if len(item["regions"]) == 2]
    pair_outgoing: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for item in strong_pairs:
        source_key = re.sub(r"\s+", "", item["activation_predicates"][0])
        pair_outgoing[(item["module"], source_key)].append(item)
    for key in pair_outgoing:
        pair_outgoing[key].sort(key=lambda item: (
            -item["formal_confidence"], -item["normalized_structural_similarity"], item["path_id"]
        ))

    composed_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)

    def compose_walk(chain: list[dict[str, Any]]) -> None:
        predicates = [chain[0]["activation_predicates"][0]] + [
            item["activation_predicates"][1] for item in chain
        ]
        if len(chain) >= 2:
            regions = [chain[0]["regions"][0], chain[0]["regions"][1]] + [
                item["regions"][1] for item in chain[1:]
            ]
            kinds = [chain[0]["region_kinds"][0], chain[0]["region_kinds"][1]] + [
                item["region_kinds"][1] for item in chain[1:]
            ]
            signature = "|".join([
                chain[0]["module"],
                *(re.sub(r"\s+", "", value) for value in predicates),
            ])
            digest = hashlib.sha1(signature.encode()).hexdigest()[:12]
            composed_by_module[chain[0]["module"]].append({
                "path_id": f"validated_composed_path_{digest}",
                "module": chain[0]["module"],
                "regions": regions,
                "region_kinds": kinds,
                "region_edges": [item["region_edges"][0] for item in chain],
                "edge_types": [item["edge_types"][0] for item in chain],
                "activation_predicates": predicates,
                "activation_roles": [chain[0]["activation_roles"][0]] + [
                    item["activation_roles"][1] for item in chain
                ],
                "normalized_structural_similarity": round(
                    sum(item["normalized_structural_similarity"] for item in chain) / len(chain), 6
                ),
                "static_evidence": [item["static_evidence"][0] for item in chain],
                "validation_status": "FORMALLY_COMPOSED_FROM_STRONG_ADJACENT_RELATIONS",
                "reachability_results": list(dict.fromkeys(
                    query_id for item in chain for query_id in item["reachability_results"]
                )),
                "dominance_results": [item["dominance_results"][0] for item in chain],
                "exclusivity_results": [item["exclusivity_results"][0] for item in chain],
                "ordering_results": [item["ordering_results"][0] for item in chain],
                "progress_results": [item["progress_results"][0] for item in chain],
                "formal_confidence": round(
                    sum(item["formal_confidence"] for item in chain) / len(chain), 6
                ),
                "mandatory_adjacent_relations": [item["mandatory_adjacent_relations"][0] for item in chain],
                "function_context": "AMBIGUOUS",
                "composition_evidence": [item["path_id"] for item in chain],
            })
        if len(chain) >= 4:
            return
        tail = re.sub(r"\s+", "", chain[-1]["activation_predicates"][1])
        seen_predicates = {
            re.sub(r"\s+", "", value) for value in predicates
        }
        for next_pair in pair_outgoing.get((chain[0]["module"], tail), []):
            next_target = re.sub(r"\s+", "", next_pair["activation_predicates"][1])
            if next_target not in seen_predicates:
                compose_walk(chain + [next_pair])

    for pair in strong_pairs:
        compose_walk([pair])
    composed = []
    for module, items in sorted(composed_by_module.items()):
        unique: dict[tuple[str, ...], dict[str, Any]] = {}
        for item in items:
            signature = tuple(re.sub(r"\s+", "", value) for value in item["activation_predicates"])
            unique.setdefault(signature, item)
        ranked = sorted(unique.values(), key=lambda item: (
            -len(item["regions"]), -item["formal_confidence"],
            -item["normalized_structural_similarity"], item["path_id"],
        ))
        composed.extend(ranked[:12])
    validated.extend(composed)
    validated_doc = {
        "schema": "region_flow.5-validated-functional-region-paths.v1",
        "paths": validated,
        "summary": {
            "candidate_paths": len(candidate_doc.get("paths", [])),
            "validated_paths": len(validated),
            "formally_composed_paths": len(composed),
            "rejected": dict(rejected),
            "multiple_paths_per_function_supported": True,
        },
    }
    return (
        {"schema": "region_flow.5-region-reachability.v1", "results": reachability},
        {"schema": "region_flow.5-region-dominance.v1", "results": dominance},
        {"schema": "region_flow.5-region-exclusivity.v1", "results": exclusivity},
        {"schema": "region_flow.5-region-ordering.v1", "results": ordering, "progress": list(progress.values())},
        validated_doc,
    )


def structural_path_signature(path_doc: dict[str, Any]) -> list[tuple[Any, ...]]:
    """Name-free signature used by signal-name ablation tests."""
    return sorted(
        (tuple(item["region_kinds"]), tuple(item["edge_types"]), len(item["regions"]))
        for item in path_doc.get("paths", [])
    )
