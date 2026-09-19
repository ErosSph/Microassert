"""Compatibility adapter from Req8.4 graph motifs to VerificationRegion IR.

The former case/name/suffix heuristics were removed.  This entry point remains
because the original CLI and IR analyzer consume ``VerificationRegion``; all
functional candidates now originate in ``detect_graph_patterns``.
"""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import ObjectType, SourceEvidence, VerificationRegion
from dateassertion.ir.validation import validate_candidate
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.graph_patterns import ALL_PATTERNS, TypedGraphIndex, detect_graph_patterns
from dateassertion.rtl_frontend.hierarchy import reachable_modules
from dateassertion.rtl_frontend.parser import RTLDesign
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph
from dateassertion.rtl_frontend.signal_analysis import dependency_graph


TYPE_MAP = {
    "FSM": ObjectType.FSM,
    "DECODE": ObjectType.DECODE,
    "HANDSHAKE": ObjectType.HANDSHAKE,
    "PIPELINE": ObjectType.PIPELINE,
    "REGISTER_UPDATE": ObjectType.REGISTER_UPDATE,
    "DATAPATH": ObjectType.DATAPATH,
}
TYPE_MAP.update({kind: ObjectType.REGISTER_UPDATE if kind in {"COUNTER", "ACCUMULATOR"}
                 else ObjectType.DATAPATH for kind in ALL_PATTERNS if kind not in TYPE_MAP
                 and kind not in {"REGISTER_FILE", "LSU", "ITERATIVE_MULTIPLIER", "ITERATIVE_DIVIDER"}})


def _context(path: str, lines: list[int], radius: int = 5) -> tuple[str, int, int]:
    source = Path(path).read_text(encoding="utf-8", errors="replace").splitlines()
    if not source or not lines:
        return "", 1, 1
    start = max(1, min(lines) - radius)
    end = min(len(source), max(lines) + radius)
    return "\n".join(source[start - 1:end]), start, end


def _evidence(
    pattern: dict[str, Any], index: TypedGraphIndex, correctness_sources: list[str],
) -> SourceEvidence:
    sources = [
        index.nodes[item].get("source", {}) for item in pattern.get("core_node_ids", [])
        if item in index.nodes and index.nodes[item].get("source", {}).get("file")
    ]
    file = str(sources[0]["file"]) if sources else ""
    lines = [int(item["line"]) for item in sources if item.get("file") == file and item.get("line")]
    snippet, start, end = _context(file, lines) if file else ("", 1, 1)
    return SourceEvidence(
        rtl_files=[file] if file else [], line_start=start, line_end=end,
        snippet=snippet, confidence=float(pattern.get("score", 0.0)),
        correctness_sources=correctness_sources,
    )


def _core_assignments(pattern: dict[str, Any], index: TypedGraphIndex) -> list[dict[str, Any]]:
    return [
        dict(index.nodes[item]) for item in pattern.get("core_node_ids", [])
        if index.is_assignment(item)
    ]


def _fsm_metadata(
    design: RTLDesign, pattern: dict[str, Any], index: TypedGraphIndex,
) -> dict[str, Any]:
    state_id = next((item for item in pattern["anchor_nodes"] if index.is_signal(item)), "")
    state = str(index.nodes.get(state_id, {}).get("name", ""))
    case = next(
        (
            item for item in design.cases
            if item.module == pattern["module"] and state in expression_signals(item.selector)
        ),
        None,
    )
    states: dict[str, str] = {}
    if case and case.file:
        source = Path(case.file).read_text(encoding="utf-8", errors="replace")
        for label in case.labels:
            match = re.search(
                rf"\b(?:localparam|parameter)\b[^;]*\b{re.escape(label)}\s*=\s*([^,;]+)", source,
            )
            states[label] = " ".join(match.group(1).split()) if match else label
    return {
        "state_variable": state, "states": states,
        "case_labels": list(case.labels) if case else [],
        "assignments": _core_assignments(pattern, index),
    }


def _decode_metadata(pattern: dict[str, Any], index: TypedGraphIndex) -> dict[str, Any]:
    assignments = _core_assignments(pattern, index)
    roles = (pattern.get("match_certificate") or {}).get("roles", {})
    if roles:
        selectors = (pattern["match_certificate"].get("composition_details") or {}).get("selector_signals", [])
        selector = index.nodes[roles["selector"]]["name"] if "selector" in roles else selectors[0] if len(selectors) == 1 else None
        return {"selector": selector, "selector_signals": selectors,
                "outputs": [index.nodes[roles["result"]]["name"]], "assignments": assignments}
    targets = [index.assignment_target.get(item["id"], "") for item in assignments]
    target = max(set(targets), key=targets.count) if targets else ""
    controls = set().union(*(index.assignment_controls[item["id"]] for item in assignments)) if assignments else set()
    selector_id = max(controls, key=lambda item: len(index.controls(item)), default="")
    return {
        "selector": index.nodes.get(selector_id, {}).get("name"),
        "outputs": [index.nodes[target].get("name")] if target in index.nodes else [],
        "assignments": assignments,
    }


def _handshake_metadata(pattern: dict[str, Any], index: TypedGraphIndex) -> dict[str, Any]:
    roles = (pattern.get("match_certificate") or {}).get("roles", {})
    if roles:
        request, response, active = (index.nodes[roles[r]]["name"] for r in ("request", "response", "active"))
        return {"request": request, "response": response, "active_state": active,
                "payload": [], "protocol_roles_verified": False,
                "events": {"request_active": request, "response_observed": response,
                           "completed": None, "stalled": None},
                "assignments": _core_assignments(pattern, index)}
    anchors = [item for item in pattern["anchor_nodes"] if index.is_signal(item)]
    names = [str(index.nodes[item].get("name", "")) for item in anchors]
    # Roles are topology hypotheses.  The bounded LLM may swap or reject them;
    # spelling is never consulted here.
    request = names[0] if names else None
    response = names[1] if len(names) > 1 else None
    core_signals = [
        str(index.nodes[item].get("name", "")) for item in pattern["core_node_ids"]
        if index.is_signal(item) and str(index.nodes[item].get("name", "")) not in {request, response}
        and (index.signal_width(item) or 1) > 1
    ]
    return {
        "request": request, "response": response, "payload": sorted(set(core_signals)),
        "events": {
            "request_active": request,
            "completed": f"{request} && {response}" if request and response else None,
            "stalled": f"{request} && !{response}" if request and response else None,
        },
        "assignments": _core_assignments(pattern, index),
    }


def _pipeline_metadata(pattern: dict[str, Any], index: TypedGraphIndex) -> dict[str, Any]:
    roles = (pattern.get("match_certificate") or {}).get("roles", {})
    if roles:
        names = {r: index.nodes[n].get("name") for r, n in roles.items()}
        updates = [index.nodes[roles[r]] for r in ("first", "second")]
        unguarded = all(str(n.get("guard", "")).strip() in {"", "1", "1'b1"} for n in updates)
        return {"transfers": [{"input": names["source"], "output": names["sink"]}],
                "stage_signals": [names[r] for r in ("source", "middle", "sink")],
                "stage_update_guards": [n.get("guard") for n in updates],
                "stall": None, "flush": None, "valid_in": None, "valid_out": None,
                "latency": 2 if unguarded else None, "register_stages": 2,
                "storage_instances": [], "assignments": _core_assignments(pattern, index)}
    signals = [item for item in pattern["anchor_nodes"] if index.is_signal(item)]
    transfers = []
    if len(signals) >= 2:
        transfers.append({
            "input": str(index.nodes[signals[0]].get("name", "")),
            "output": str(index.nodes[signals[-1]].get("name", "")),
        })
    assignments = _core_assignments(pattern, index)
    controls = set().union(*(index.assignment_controls[item["id"]] for item in assignments)) if assignments else set()
    control_names = [str(index.nodes[item].get("name", "")) for item in sorted(controls)]
    return {
        "transfers": transfers, "stall": control_names[0] if control_names else None,
        "flush": None, "valid_in": None, "valid_out": None,
        "latency": max(1, len(signals) - 1), "storage_instances": [],
        "assignments": assignments,
    }


def _register_metadata(pattern: dict[str, Any], index: TypedGraphIndex) -> dict[str, Any]:
    target_id = next((item for item in pattern["anchor_nodes"] if index.is_signal(item)), "")
    target = str(index.nodes.get(target_id, {}).get("name", ""))
    assignments = _core_assignments(pattern, index)
    representative = next((item for item in assignments if item.get("lhs") == target and item.get("guard")), assignments[0] if assignments else {})
    reset_assignment = next(
        (item for item in assignments if re.fullmatch(r"(?:\d+)?'[bBdDhHoO]?[0_]+|0|'0", str(item.get("rhs", "")).strip())),
        None,
    )
    return {
        "register": target, "enable": representative.get("guard") or "1'b1",
        "update_expression": representative.get("rhs"),
        "reset_value": reset_assignment.get("rhs") if reset_assignment else None,
        "assignments": assignments,
    }


def _datapath_metadata(pattern: dict[str, Any], index: TypedGraphIndex) -> dict[str, Any]:
    assignments = _core_assignments(pattern, index)
    assignment = max(assignments, key=lambda item: len(index.assignment_inputs[item["id"]]), default={})
    roles = (pattern.get("match_certificate") or {}).get("roles", {})
    if roles:
        selected = roles.get("transform") or roles.get("operation") or roles.get("select")
        if selected:
            assignment = index.nodes[selected]
    assignment_id = str(assignment.get("id", ""))
    target_id = index.assignment_target.get(assignment_id, "")
    operands = [str(index.nodes[item].get("name", "")) for item in sorted(index.assignment_inputs[assignment_id])]
    return {
        "result": index.nodes.get(target_id, {}).get("name"),
        "expression": assignment.get("rhs"), "operands": operands,
        "operation_select": None,
        "latency": 1 if assignment.get("timing") == "next_cycle" else 0,
        "assignments": assignments,
    }


def _metadata(design: RTLDesign, pattern: dict[str, Any], index: TypedGraphIndex) -> dict[str, Any]:
    kind = pattern["kind"]
    if kind in {"COUNTER", "ACCUMULATOR"}:
        return {**_register_metadata(pattern, index), "graph_function_kind": kind,
                "match_certificate": pattern["match_certificate"]}
    if kind in {"SHIFTER", "COMPARATOR", "MULTIPLIER", "DIVIDER", "MUX", "ALU"}:
        return {**_datapath_metadata(pattern, index), "graph_function_kind": kind,
                "match_certificate": pattern["match_certificate"]}
    builders = {
        "FSM": lambda: _fsm_metadata(design, pattern, index),
        "DECODE": lambda: _decode_metadata(pattern, index),
        "HANDSHAKE": lambda: _handshake_metadata(pattern, index),
        "PIPELINE": lambda: _pipeline_metadata(pattern, index),
        "REGISTER_UPDATE": lambda: _register_metadata(pattern, index),
        "DATAPATH": lambda: _datapath_metadata(pattern, index),
    }
    result = builders[kind]()
    result.update({
        "graph_pattern_scores": pattern["pattern_scores"],
        "graph_score_semantics": pattern.get("score_semantics", "LEGACY_WEIGHTED_SCORE"),
        "match_certificate": pattern.get("match_certificate"),
        "graph_detection_status": pattern["detection_status"],
        "matched_features": pattern["matched_features"],
        "core_node_ids": pattern["core_node_ids"],
        "signal_names_used_for_scoring": False,
    })
    return result


def extract_candidates(
    design: RTLDesign,
    top: str,
    spec_paths: list[str] | None = None,
    per_type: int = 3,
    include_submodules: bool = False,
    discovery_limit: int = 0,
    matching_backend: str = "attributed_vf2",
) -> list[VerificationRegion]:
    """Adapt name-independent graph-pattern matches to the legacy IR API."""
    if top not in design.module_signals:
        raise ValueError(f"top module {top!r} has no extracted signals")
    graph = build_semantic_graph(design)
    index = TypedGraphIndex(graph)
    patterns = detect_graph_patterns(graph, max_candidates_per_kind=None,
                                     matching_backend=matching_backend)["patterns"]
    modules = set(reachable_modules(design, top) if include_submodules else [top])
    correctness_sources = [str(Path(path).resolve()) for path in (spec_paths or [])]
    dependencies = {module: dependency_graph(design, module) for module in modules}
    selected: list[dict[str, Any]] = []
    for kind in TYPE_MAP:
        values = [
            item for item in patterns
            if item["kind"] == kind and item["module"] in modules and item["detection_status"] == "MATCH"
        ]
        selected.extend(sorted(values, key=lambda item: item["candidate_id"])[:per_type])

    regions = []
    for pattern in selected:
        module = pattern["module"]
        signal_names = sorted({
            str(index.nodes[item].get("name", "")) for item in pattern["core_node_ids"]
            if index.is_signal(item) and index.nodes[item].get("name") in design.module_signals[module]
        })
        regions.append(VerificationRegion(
            region_id=pattern["candidate_id"], suggested_type=TYPE_MAP[pattern["kind"]],
            module=module, signals=signal_names,
            dependencies={name: dependencies[module].get(name, {"fanin": []})["fanin"] for name in signal_names},
            evidence=_evidence(pattern, index, correctness_sources),
            metadata=_metadata(design, pattern, index),
        ))

    if discovery_limit > 0:
        selected_ids = {item["candidate_id"] for item in selected}
        ambiguous = [
            item for item in patterns
            if item["module"] in modules and item["detection_status"] == "AMBIGUOUS"
            and item["candidate_id"] not in selected_ids
        ]
        for pattern in sorted(ambiguous, key=lambda item: item["candidate_id"])[:discovery_limit]:
            module = pattern["module"]
            signal_names = sorted({
                str(index.nodes[item].get("name", "")) for item in pattern["core_node_ids"]
                if index.is_signal(item) and index.nodes[item].get("name") in design.module_signals[module]
            })
            regions.append(VerificationRegion(
                region_id=pattern["candidate_id"] + "_ambiguous",
                suggested_type=ObjectType.UNKNOWN, module=module, signals=signal_names,
                dependencies={name: dependencies[module].get(name, {"fanin": []})["fanin"] for name in signal_names},
                evidence=_evidence(pattern, index, correctness_sources),
                metadata={
                    **_metadata(design, pattern, index),
                    "candidate_kind": "GRAPH_PATTERN_AMBIGUITY",
                    "discovery_score": pattern["score"],
                },
            ))

    known = set(design.signals)
    for candidate in regions:
        validate_candidate(candidate, known)
    return regions
