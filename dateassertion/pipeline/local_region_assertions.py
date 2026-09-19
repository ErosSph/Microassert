"""Design-agnostic local Region/assertion expansion for Requirement 8.7.

This module deliberately separates three concerns:

* typed-graph membership decides which RTL relation belongs to a Region;
* an LLM may name an unresolved local Extension Region or extract SPEC facts;
* the existing fixed primitive compiler is the only component that emits SVA.

No CPU, module, or signal name is embedded in the implementation.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from copy import deepcopy
from dataclasses import dataclass, field
import hashlib
from math import sqrt
from pathlib import Path
import re
from typing import Any, Iterable

from dateassertion.ir.schema import ContractIR, FormalPropertyResult, PropertyIR, TemplateBindingIR
from dateassertion.ontology.primitives import _compile, bind_extension_primitives, expression_signals
from dateassertion.ontology.architecture_obligations import architecture_contract_support
from dateassertion.pipeline.property_portfolio_planner import PortfolioCandidate
from dateassertion.pipeline.region_contracts import RULE_FIELD
from dateassertion.rtl_frontend.parser import RTLDesign


CORE_REGION_TYPES = (
    "FETCH_FRONTEND", "DECODE", "CONTROL_FSM", "REGISTER_UPDATE",
    "PIPELINE_FLOW", "HANDSHAKE_REQUEST_RESPONSE", "MEMORY_CONTROL",
    "WRITEBACK", "QUEUE_BUFFER", "RESOURCE_ARBITRATION", "DATAPATH",
    "COUNTER", "ACCUMULATOR", "SHIFTER", "COMPARATOR", "MULTIPLIER",
    "DIVIDER", "MUX", "ALU",
    "REGISTER_FILE", "LSU", "ITERATIVE_MULTIPLIER", "ITERATIVE_DIVIDER",
    "ONEHOT_PROGRESS",
)

GENERIC_PRIMITIVES = (
    "RESET", "UPDATE", "HOLD", "CAUSALITY", "ORDERING", "STABILITY",
    "DATA_INTEGRITY", "PERSISTENCE", "PROGRESS",
    "CONTROL_ASSERT", "CONTROL_DEASSERT",
)

_CORE_KIND = {
    "FSM": "CONTROL_FSM",
    "DECODE": "DECODE",
    "HANDSHAKE": "HANDSHAKE_REQUEST_RESPONSE",
    "PIPELINE": "PIPELINE_FLOW",
    "REGISTER_UPDATE": "REGISTER_UPDATE",
    "DATAPATH": "DATAPATH",
}

_PRIMITIVE_ROLES = {
    "UPDATE": {"CONDITION", "TARGET", "VALUE", "DELAY"},
    "HOLD": {"CONDITION", "TARGET"},
    "CAUSALITY": {"CAUSE", "EFFECT", "DELAY"},
    "ORDERING": {"FIRST", "SECOND", "DELAY"},
    "STABILITY": {"CONDITION", "SIGNALS"},
    "DATA_INTEGRITY": {"CONDITION", "SOURCE", "TARGET", "DELAY"},
    "PERSISTENCE": {"START", "END"},
    "CONTROL_ASSERT": {"CONDITION", "TARGET", "DELAY"},
    "CONTROL_DEASSERT": {"CONDITION", "TARGET", "DELAY"},
    "RESET": {"RESET", "TARGET", "VALUE"},
    "PROGRESS": {"START", "END", "MAX_DELAY"},
}


class Requirement87ValidationError(ValueError):
    """Raised when an LLM result cannot enter the deterministic pipeline."""


@dataclass
class LocalCandidateBinding:
    candidate: PortfolioCandidate
    compatible_region_ids: list[str]
    binding_evidence_by_region: dict[str, dict[str, Any]] = field(default_factory=dict)
    primary_region_id: str = ""
    selection_rank: int | None = None
    selection_score: float | None = None
    selected: bool = False
    selection_reason: str = ""


def _safe_id(value: str) -> str:
    return re.sub(r"[^A-Za-z0-9_$]+", "_", value).strip("_").lower()


def _all_strings(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from _all_strings(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from _all_strings(item)


def _forbidden_generated_text(value: Any) -> bool:
    for key in value if isinstance(value, dict) else ():
        if str(key).lower() in {"sva", "assertion", "property_body"}:
            return True
    if isinstance(value, dict):
        return any(_forbidden_generated_text(item) for item in value.values())
    if isinstance(value, list):
        return any(_forbidden_generated_text(item) for item in value)
    return False


def spec_lines(path: str | Path, ranges: list[list[int]]) -> list[dict[str, Any]]:
    """Read only configured SPEC ranges and retain exact line evidence."""

    source = Path(path).resolve()
    lines = source.read_text(encoding="utf-8", errors="replace").splitlines()
    selected: list[dict[str, Any]] = []
    seen: set[int] = set()
    for raw in ranges:
        if not isinstance(raw, list) or len(raw) != 2:
            raise ValueError(f"invalid SPEC line range: {raw!r}")
        start, end = (int(raw[0]), int(raw[1]))
        if start < 1 or end < start or end > len(lines):
            raise ValueError(f"SPEC line range outside {source}: {start}-{end}")
        for number in range(start, end + 1):
            if number in seen:
                continue
            seen.add(number)
            selected.append({"line": number, "text": lines[number - 1]})
    return selected


def package_spec_context(
    path: str | Path, lines: list[dict[str, Any]], design: RTLDesign, module: str,
) -> dict[str, Any]:
    """Provide only selected SPEC lines and a module interface signature."""

    source = Path(path).resolve()
    interface = [
        {
            "name": name, "width": signal.width, "direction": signal.direction,
            "kind": signal.kind,
        }
        for name, signal in sorted(design.module_signals.get(module, {}).items())
        if signal.direction in {"input", "output", "inout"}
    ]
    return {
        "schema": "region_flow.7-spec-extraction-context.v2",
        "spec_source": str(source),
        "spec_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "spec_lines": lines,
        "target_module": module,
        "rtl_interface_signature": interface,
        "allowed_fixed_primitive_roles": {
            name: sorted(roles) for name, roles in _PRIMITIVE_ROLES.items()
        },
        "whole_design_rtl_supplied": False,
    }


def _compact_node(node: dict[str, Any]) -> dict[str, Any]:
    if node.get("kind") == "assignment":
        return {
            key: node.get(key) for key in (
                "id", "kind", "module", "lhs", "rhs", "guard", "timing", "clock", "reset", "source"
            )
        }
    return {
        key: node.get(key) for key in (
            "id", "kind", "module", "name", "width", "direction", "signal_kind", "role", "source"
        ) if key in node
    }


def package_extension_context(
    region: dict[str, Any], design: RTLDesign, optional_spec_lines: list[dict[str, Any]],
    *, max_nodes: int = 48, max_edges: int = 72, max_rtl_chars: int = 7000,
) -> dict[str, Any]:
    """Package one bounded local slice; never include a global design summary."""

    module = str(region["module"])
    local_signals = design.module_signals.get(module, {})
    raw_nodes = region.get("coi", {}).get("nodes", [])[:max_nodes]
    referenced_names: set[str] = set()
    for node in raw_nodes:
        if node.get("kind") == "assignment":
            referenced_names.add(str(node.get("lhs", "")))
            referenced_names.update(expression_signals(str(node.get("rhs", ""))))
            referenced_names.update(expression_signals(str(node.get("guard", ""))))
        elif node.get("kind") == "signal":
            referenced_names.add(str(node.get("name", "")))
    region_names = (
        set(region.get("signals", [])) | set(region.get("seed_signals", []))
        | (referenced_names & set(local_signals))
    )
    io = [
        {
            "name": name, "width": signal.width, "direction": signal.direction,
            "kind": signal.kind,
        }
        for name, signal in sorted(local_signals.items())
        if name in region_names and signal.direction in {"input", "output", "inout"}
    ]
    state = [
        {"name": name, "width": signal.width, "kind": signal.kind}
        for name, signal in sorted(local_signals.items())
        if name in region_names and signal.direction == "internal" and signal.kind in {"reg", "logic"}
    ]
    local_events = [
        {"name": name, "width": signal.width, "kind": signal.kind}
        for name, signal in sorted(local_signals.items())
        if name in region_names and signal.direction == "internal" and signal.kind not in {"reg", "logic"}
    ]
    nodes = [_compact_node(item) for item in raw_nodes]
    node_ids = {item.get("id") for item in nodes}
    edges = [
        {key: edge.get(key) for key in ("type", "source", "target", "clock", "evidence") if key in edge}
        for edge in region.get("coi", {}).get("edges", [])
        if edge.get("source") in node_ids and edge.get("target") in node_ids
    ][:max_edges]
    snippets = []
    remaining = max_rtl_chars
    for item in region.get("coi", {}).get("rtl_context", []):
        snippet = str(item.get("snippet", ""))[:remaining]
        if not snippet:
            continue
        snippets.append({"file": item.get("file"), "lines": item.get("lines", []), "snippet": snippet})
        remaining -= len(snippet)
        if remaining <= 0:
            break
    return {
        "schema": "region_flow.7-local-extension-context.v1",
        "region_id": region["region_id"],
        "candidate_core_kind": region.get("kind"),
        "candidate_pattern_scores": region.get("pattern_scores", {}),
        "matched_graph_features": region.get("matched_features", []),
        "module": module,
        "related_inputs_outputs": io,
        "major_register_state": state,
        "local_events_controls": local_events,
        "local_graph_nodes": nodes,
        "local_graph_edges": edges,
        "target_rtl_slice": snippets,
        "optional_spec_evidence": optional_spec_lines,
        "whole_design_rtl_supplied": False,
    }


def validate_extension_response(response: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(response, dict) or response.get("region_id") != context.get("region_id"):
        raise Requirement87ValidationError("Extension response region_id does not match local context")
    if _forbidden_generated_text(response):
        raise Requirement87ValidationError("Extension response attempted to provide SVA/assertion text")
    classification = response.get("classification")
    if classification not in {"EXTENSION", "CORE", "UNRESOLVED"}:
        raise Requirement87ValidationError("classification must be EXTENSION, CORE, or UNRESOLVED")
    confidence = response.get("confidence")
    if not isinstance(confidence, (int, float)) or not 0 <= float(confidence) <= 1:
        raise Requirement87ValidationError("confidence must be in [0, 1]")
    known_signals = {
        item["name"] for key in ("related_inputs_outputs", "major_register_state", "local_events_controls")
        for item in context.get(key, [])
    }
    known_nodes = {item.get("id") for item in context.get("local_graph_nodes", [])}
    signal_fields = ("important_state", "important_events", "inputs", "outputs")
    copied = deepcopy(response)
    for field in signal_fields:
        values = copied.get(field, [])
        if not isinstance(values, list) or any(not isinstance(item, str) for item in values):
            raise Requirement87ValidationError(f"{field} must be an array of signal names")
        unknown = set(values) - known_signals
        if unknown:
            raise Requirement87ValidationError(f"{field} contains signals outside local context: {sorted(unknown)}")
    evidence_nodes = copied.get("evidence_node_ids", [])
    if not isinstance(evidence_nodes, list) or not evidence_nodes:
        raise Requirement87ValidationError("evidence_node_ids must be a non-empty array")
    if set(evidence_nodes) - known_nodes:
        raise Requirement87ValidationError("evidence_node_ids contains nodes outside local context")
    if classification == "EXTENSION":
        extension_type = str(copied.get("extension_type", "")).strip()
        name = str(copied.get("name", "")).strip()
        meaning = str(copied.get("functional_meaning", "")).strip()
        if not extension_type or not name or not meaning:
            raise Requirement87ValidationError("EXTENSION requires type, name, and functional meaning")
        if extension_type.upper() in CORE_REGION_TYPES:
            raise Requirement87ValidationError("Extension type duplicates the fixed Core ontology")
    return copied


def extension_region_from_response(
    source_region: dict[str, Any], response: dict[str, Any], context_sha256: str,
) -> dict[str, Any] | None:
    if response.get("classification") != "EXTENSION":
        return None
    digest = hashlib.sha1(
        f"{source_region['region_id']}\n{response['extension_type']}".encode("utf-8")
    ).hexdigest()[:10]
    return {
        "region_id": f"region_extension_{_safe_id(str(response['extension_type']))}_{digest}",
        "kind": "EXTENSION",
        "extension_type": str(response["extension_type"]),
        "name": str(response["name"]),
        "functional_meaning": str(response["functional_meaning"]),
        "module": source_region["module"],
        "seed_signals": sorted(set(response.get("important_state", [])) | set(response.get("important_events", []))),
        "signals": sorted(set(response.get("important_state", [])) | set(response.get("important_events", [])) | set(response.get("inputs", [])) | set(response.get("outputs", []))),
        "important_state": response.get("important_state", []),
        "important_events": response.get("important_events", []),
        "inputs": response.get("inputs", []),
        "outputs": response.get("outputs", []),
        "confidence": float(response["confidence"]),
        "core_node_ids": sorted(set(response.get("evidence_node_ids", []))),
        "coi": deepcopy(source_region.get("coi", {})),
        "boundary": deepcopy(source_region.get("boundary", {})),
        "evidence": deepcopy(source_region.get("evidence", {})),
        "source_core_candidate": source_region["region_id"],
        "ontology_classification": "EXTENSION_REGION",
        "analysis_source": "deepseek-local-rtl-slice",
        "llm_context_sha256": context_sha256,
        "llm_generated_sva": False,
    }


def build_region_inventory(
    base_regions: dict[str, Any], extensions: list[dict[str, Any]],
    spec_role_overlays: dict[str, set[str]] | None = None,
) -> dict[str, Any]:
    spec_role_overlays = spec_role_overlays or {}
    regions = []
    replaced = {item.get("source_core_candidate") for item in extensions}
    for item in base_regions.get("regions", []):
        if item.get("kind") == "MODULE":
            continue
        if item.get("region_id") in replaced:
            continue
        copied = deepcopy(item)
        copied["ontology_classification"] = "CORE_REGION"
        roles = {_CORE_KIND.get(str(item.get("kind")), str(item.get("kind")))}
        roles.update(spec_role_overlays.get(item["region_id"], set()))
        copied["core_region_roles"] = sorted(roles)
        support = architecture_contract_support(str(item.get("kind")), item.get("match_certificate"))
        if support is not None:
            copied["architecture_contract_support"] = support
        regions.append(copied)
    regions.extend(deepcopy(extensions))
    matched = Counter(role for item in regions for role in item.get("core_region_roles", []))
    return {
        "schema": "region_flow.7-region-inventory.v1",
        "core_ontology": [
            {"type": name, "matched_regions": matched[name], "observed": bool(matched[name])}
            for name in CORE_REGION_TYPES
        ],
        "regions": regions,
        "summary": {
            "regions": len(regions),
            "core_regions": sum(item.get("ontology_classification") == "CORE_REGION" for item in regions),
            "extension_regions": sum(item.get("ontology_classification") == "EXTENSION_REGION" for item in regions),
            "core_roles_observed": dict(matched),
            "extension_types": dict(Counter(item.get("extension_type") for item in extensions)),
        },
    }


def _candidate_assignment_id(item: PortfolioCandidate) -> str:
    return str(item.rtl_relation.get("assignment_id") or "")


def _candidate_assignment_ids(item: PortfolioCandidate) -> list[str]:
    identifiers = item.rtl_relation.get("assignment_ids", [])
    values = [str(value) for value in identifiers] if isinstance(identifiers, list) else []
    primary = _candidate_assignment_id(item)
    return list(dict.fromkeys(([primary] if primary else []) + [value for value in values if value]))


def _candidate_relation_key(item: PortfolioCandidate) -> tuple[str, str, str]:
    """Return a stable semantic-relation key for selection deduplication.

    Most candidates are grounded by an assignment node.  HOLD candidates can
    instead be grounded directly by their target signal, so an empty
    assignment id must not collapse all HOLD relations in one module.
    """

    anchor = _candidate_assignment_id(item)
    if not anchor:
        target = str(item.rtl_relation.get("lhs", ""))
        anchor = f"signal:{item.module}.{target}" if target else item.candidate_id
    return item.module, anchor, item.primitive


_BINDING_LEVEL_RANK = {
    "TYPED_COI_PATH": 1,
    "TYPED_BOUNDARY": 2,
    "EXACT_CORE": 3,
}


def _boundary_endpoint_node(value: Any) -> str:
    if isinstance(value, str):
        return value
    if isinstance(value, dict):
        module, signal = str(value.get("module", "")), str(value.get("signal", ""))
        if module and signal:
            return f"signal:{module}.{signal}"
    return ""


def _region_binding_evidence_index(
    region: dict[str, Any], *, maximum_path_edges: int = 3,
    requested_node_ids: set[str] | None = None,
) -> dict[str, dict[str, Any]]:
    """Index three auditable candidate-to-Region binding levels.

    Exact core membership is strongest.  A typed Region cut endpoint is the
    second level.  Remaining COI nodes are eligible only when a bounded path
    of literal DATA/CONTROL/SEQUENTIAL edges reaches a core node.
    """

    region_id = str(region.get("region_id", ""))
    module = str(region.get("module", ""))
    core = {str(item) for item in region.get("core_node_ids", [])}
    wanted = lambda node_id: requested_node_ids is None or node_id in requested_node_ids
    index: dict[str, dict[str, Any]] = {
        node_id: {
            "binding_level": "EXACT_CORE",
            "binding_rank": _BINDING_LEVEL_RANK["EXACT_CORE"],
            "region_id": region_id,
            "anchor_node_id": node_id,
            "path_node_ids": [node_id],
            "typed_edges": [],
        }
        for node_id in core if wanted(node_id)
    }

    boundary = region.get("boundary", {})
    boundary_edges = []
    for key in ("semantic_cut_edges", "expanded_cross_edges", "cross_edges"):
        boundary_edges.extend(
            item for item in boundary.get(key, []) if isinstance(item, dict)
        )
    for edge in boundary_edges:
        for endpoint in (edge.get("source"), edge.get("target")):
            node_id = _boundary_endpoint_node(endpoint)
            if not node_id or node_id in index or not wanted(node_id):
                continue
            index[node_id] = {
                "binding_level": "TYPED_BOUNDARY",
                "binding_rank": _BINDING_LEVEL_RANK["TYPED_BOUNDARY"],
                "region_id": region_id,
                "anchor_node_id": node_id,
                "path_node_ids": [node_id],
                "typed_edges": [{
                    key: deepcopy(edge.get(key))
                    for key in ("type", "source", "target", "evidence")
                }],
            }
    for direction in ("imported_signals", "exported_signals"):
        for signal in boundary.get(direction, []):
            node_id = f"signal:{module}.{signal}"
            if node_id in index or not wanted(node_id):
                continue
            index[node_id] = {
                "binding_level": "TYPED_BOUNDARY",
                "binding_rank": _BINDING_LEVEL_RANK["TYPED_BOUNDARY"],
                "region_id": region_id,
                "anchor_node_id": node_id,
                "path_node_ids": [node_id],
                "typed_edges": [],
                "boundary_signal_role": direction,
            }

    coi = region.get("coi", {})
    coi_nodes = {str(item) for item in coi.get("node_ids", [])}
    coi_nodes.update(
        str(item.get("id")) for item in coi.get("nodes", []) if item.get("id")
    )
    allowed_types = {"DATA", "CONTROL", "SEQUENTIAL"}
    adjacency: dict[str, list[tuple[str, dict[str, Any]]]] = defaultdict(list)
    for edge in coi.get("edges", []):
        edge_type = str(edge.get("type", "")).upper()
        source, target = str(edge.get("source", "")), str(edge.get("target", ""))
        if edge_type not in allowed_types or not source or not target:
            continue
        if source not in coi_nodes or target not in coi_nodes:
            continue
        compact = {key: deepcopy(edge.get(key)) for key in ("type", "source", "target", "evidence")}
        adjacency[source].append((target, compact))
        adjacency[target].append((source, compact))

    queue = deque((node_id, [node_id], []) for node_id in sorted(core & coi_nodes))
    best_depth = {node_id: 0 for node_id in core & coi_nodes}
    while queue:
        node_id, core_to_node, path_edges = queue.popleft()
        if len(path_edges) >= maximum_path_edges:
            continue
        for neighbor, edge in adjacency.get(node_id, []):
            depth = len(path_edges) + 1
            if depth >= best_depth.get(neighbor, maximum_path_edges + 1):
                continue
            best_depth[neighbor] = depth
            next_nodes = core_to_node + [neighbor]
            next_edges = path_edges + [edge]
            queue.append((neighbor, next_nodes, next_edges))
            if neighbor in index or not wanted(neighbor):
                continue
            index[neighbor] = {
                "binding_level": "TYPED_COI_PATH",
                "binding_rank": _BINDING_LEVEL_RANK["TYPED_COI_PATH"],
                "region_id": region_id,
                "anchor_node_id": neighbor,
                "path_node_ids": list(reversed(next_nodes)),
                "typed_edges": list(reversed(next_edges)),
                "path_edge_count": depth,
            }
    return index


def enumerate_local_candidate_bindings(
    candidates: list[PortfolioCandidate], region_inventory: dict[str, Any],
    design: RTLDesign, reset_asserted: str, *, recall_mode: bool = False,
) -> list[LocalCandidateBinding]:
    functional = region_inventory.get("regions", [])
    binding_index_by_region: dict[str, dict[str, dict[str, Any]]] = {}
    regions_by_module: dict[str, list[str]] = defaultdict(list)
    requested_by_module: dict[str, set[str]] = defaultdict(set)
    for candidate in candidates:
        if candidate.scope != "LOCAL" or candidate.primitive not in GENERIC_PRIMITIVES:
            continue
        assignment_ids = _candidate_assignment_ids(candidate)
        target = str(candidate.rtl_relation.get("lhs", ""))
        if assignment_ids:
            requested_by_module[candidate.module].update(assignment_ids)
        elif target and candidate.primitive == "HOLD":
            requested_by_module[candidate.module].add(f"signal:{candidate.module}.{target}")
    for region in functional:
        region_id = str(region["region_id"])
        module = str(region["module"])
        regions_by_module[module].append(region_id)
        binding_index_by_region[region_id] = _region_binding_evidence_index(
            region, requested_node_ids=requested_by_module.get(module, set()),
        )
    result = []
    for candidate in candidates:
        if candidate.scope != "LOCAL" or candidate.primitive not in GENERIC_PRIMITIVES:
            continue
        assignment_id = _candidate_assignment_id(candidate)
        target = str(candidate.rtl_relation.get("lhs", ""))
        if not assignment_id and candidate.primitive == "HOLD":
            assignment_id = f"signal:{candidate.module}.{target}" if target else ""
        anchors = _candidate_assignment_ids(candidate) or [assignment_id]
        evidence_by_region: dict[str, dict[str, Any]] = {}
        for region_id in regions_by_module.get(candidate.module, []):
            options = []
            region_index = binding_index_by_region[region_id]
            for anchor in dict.fromkeys(item for item in anchors if item):
                if anchor in region_index:
                    options.append({**deepcopy(region_index[anchor]), "candidate_anchor_node_id": anchor})
            if options:
                evidence_by_region[region_id] = max(
                    options,
                    key=lambda item: (
                        int(item["binding_rank"]),
                        -int(item.get("path_edge_count", 0)),
                        item["candidate_anchor_node_id"] == assignment_id,
                    ),
                )
        compatible = sorted(
            evidence_by_region,
            key=lambda region_id: (
                -int(evidence_by_region[region_id]["binding_rank"]), region_id,
            ),
        )
        if not compatible:
            continue
        # Earlier experiments intentionally kept the local portfolio bounded
        # and proof-oriented. Req10 is a recall experiment: once a candidate
        # has survived deterministic grounding/static validation and has a
        # literal typed-graph binding, estimated cost/risk must not silently
        # remove it before Formal sees it.
        if not recall_mode:
            if candidate.proofability_score < 0.50 or candidate.vacuity_risk > 0.72:
                continue
            relation = candidate.rtl_relation
            if len(str(relation.get("guard", ""))) > 260 or len(str(relation.get("rhs", ""))) > 260:
                continue
        probe_properties, probe_bindings = bind_extension_primitives(
            [candidate.contract],
            {module: set(values) for module, values in design.module_signals.items()},
            reset_asserted,
        )
        if not probe_properties or any(item.status != "BOUND" for item in probe_bindings):
            continue
        result.append(LocalCandidateBinding(
            candidate, compatible, binding_evidence_by_region=evidence_by_region,
        ))
    return result


def select_local_candidate_bindings(
    bindings: list[LocalCandidateBinding], *, budget: int,
    primitive_caps: dict[str, int] | None = None,
    minimum_count: int = 0,
    selection_policy: str = "primary_region_marginal",
) -> tuple[list[LocalCandidateBinding], list[dict[str, Any]]]:
    """Coverage-aware greedy selection over concrete Region binding choices.

    Compatibility is deliberately not treated as coverage: one generated
    property is bound to one primary Region, so selecting a candidate may only
    close that Region/obligation pair.  This prevents a broad reset/control
    relation from claiming dozens of merely compatible Regions at once.
    """

    if selection_policy == "all_grounded_exact_sva":
        return _select_all_grounded_candidate_bindings(bindings)
    if selection_policy == "compatible_region_saturation":
        return _select_compatible_region_saturation(
            bindings,
            budget=budget,
            primitive_caps=primitive_caps,
            minimum_count=minimum_count,
        )
    if selection_policy != "primary_region_marginal":
        raise ValueError(f"unsupported local candidate selection policy: {selection_policy}")

    caps = {str(key).upper(): int(value) for key, value in (primitive_caps or {}).items()}
    selected: list[LocalCandidateBinding] = []
    remaining = list(bindings)
    covered_regions: set[str] = set()
    covered_pairs: set[tuple[str, str]] = set()
    covered_scope: set[str] = set()
    selected_relations: set[tuple[str, str, str]] = set()
    primitive_counts: Counter[str] = Counter()
    obligation_counts: Counter[str] = Counter()
    module_counts: Counter[str] = Counter()
    target_counts: Counter[tuple[str, str]] = Counter()
    audit = []
    while remaining and len(selected) < budget:
        ranked = []
        for item in remaining:
            candidate = item.candidate
            primitive = candidate.primitive
            relation_key = _candidate_relation_key(candidate)
            if relation_key in selected_relations:
                continue
            if primitive_counts[primitive] >= caps.get(primitive, budget):
                continue
            target = str(candidate.rtl_relation.get("lhs", ""))
            obligation = candidate.obligation or candidate.primitive
            scope = set(candidate.structural_scope)
            new_scope = scope - covered_scope
            max_overlap = max(
                (
                    len(scope & set(other.candidate.structural_scope))
                    / max(1, len(scope | set(other.candidate.structural_scope)))
                    for other in selected
                ),
                default=0.0,
            )
            relation = candidate.rtl_relation
            expression_size = len(str(relation.get("guard", ""))) + len(str(relation.get("rhs", "")))
            formal_cost = (
                18.0 * (1.0 - candidate.proofability_score)
                + 22.0 * candidate.vacuity_risk
                + min(12.0, expression_size / 80.0)
                + 3.0 * len(candidate.semantic_path)
            )
            redundancy = (
                22.0 * max_overlap
                + 4.0 * target_counts[(candidate.module, target)]
                + 2.0 * obligation_counts[obligation]
                + 1.2 * sqrt(module_counts[candidate.module])
            )
            semantic_importance = min(28.0, max(0.0, candidate.static_coverage_score / 3.0))
            for region_id in item.compatible_region_ids:
                binding_rank = int(item.binding_evidence_by_region[region_id]["binding_rank"])
                components = {
                    "uncovered_region": 34.0 if region_id not in covered_regions else 0.0,
                    "uncovered_obligation": 28.0 if (region_id, obligation) not in covered_pairs else 0.0,
                    "new_rtl_scope": min(30.0, 6.0 * sqrt(len(new_scope))),
                    "semantic_importance": semantic_importance,
                    "binding_confidence": 4.0 * binding_rank,
                    "redundancy_penalty": -redundancy,
                    "formal_cost_penalty": -formal_cost,
                }
                score = round(sum(components.values()), 6)
                ranked.append((
                    score, candidate.proofability_score, candidate.candidate_id,
                    region_id, item, components, len(new_scope),
                ))
        if not ranked:
            break
        score, _proof, _identifier, primary_region, best, components, new_scope_count = max(ranked)
        candidate = best.candidate
        best.selected = True
        best.selection_rank = len(selected) + 1
        best.selection_score = score
        best.primary_region_id = primary_region
        best.selection_reason = (
            "coverage-aware marginal utility: uncovered Region + uncovered semantic obligation "
            "+ new RTL scope + semantic importance - redundancy - Formal/vacuity cost"
        )
        setattr(best, "selection_components", {key: round(value, 6) for key, value in components.items()})
        setattr(best, "new_rtl_scope_items", new_scope_count)
        selected.append(best)
        covered_regions.add(primary_region)
        covered_pairs.add((primary_region, candidate.obligation or candidate.primitive))
        covered_scope.update(candidate.structural_scope)
        primitive_counts[candidate.primitive] += 1
        obligation_counts[candidate.obligation or candidate.primitive] += 1
        module_counts[candidate.module] += 1
        selected_relations.add(_candidate_relation_key(candidate))
        target_counts[(candidate.module, str(candidate.rtl_relation.get("lhs", "")))] += 1
        remaining.remove(best)
    selected_ids = {item.candidate.candidate_id for item in selected}
    for item in bindings:
        audit.append({
            "candidate_id": item.candidate.candidate_id,
            "module": item.candidate.module,
            "primitive": item.candidate.primitive,
            "obligation": item.candidate.primitive,
            "semantic_obligation": item.candidate.obligation,
            "compatible_region_ids": item.compatible_region_ids,
            "binding_evidence_by_region": item.binding_evidence_by_region,
            "binding_levels": dict(Counter(
                value["binding_level"] for value in item.binding_evidence_by_region.values()
            )),
            "selected": item.candidate.candidate_id in selected_ids,
            "selection_rank": item.selection_rank,
            "selection_score": item.selection_score,
            "selection_components": getattr(item, "selection_components", {}),
            "new_rtl_scope_items": getattr(item, "new_rtl_scope_items", None),
            "selection_reason": item.selection_reason or (
                "BUDGET_OR_REDUNDANCY_FILTERED" if item.candidate.candidate_id not in selected_ids else ""
            ),
            "proofability_score": item.candidate.proofability_score,
            "vacuity_risk": item.candidate.vacuity_risk,
            "rtl_relation": item.candidate.rtl_relation,
        })
    return selected, audit


def _select_all_grounded_candidate_bindings(
    bindings: list[LocalCandidateBinding],
) -> tuple[list[LocalCandidateBinding], list[dict[str, Any]]]:
    """Retain every grounded Region binding for Req10 recall evaluation.

    This stage performs no semantic, overlap, set-cover, score, family-cap, or
    budget filtering. Exact SVA duplicates can only be identified after the
    fixed primitive compiler has emitted a PropertyIR body, so that one narrow
    operation is deliberately deferred to :func:`deduplicate_exact_properties`.
    """

    selected = sorted(bindings, key=lambda item: item.candidate.candidate_id)
    audit: list[dict[str, Any]] = []
    for rank, item in enumerate(selected, 1):
        candidate = item.candidate
        preferred = (
            candidate.region_id
            if candidate.region_id in item.compatible_region_ids else None
        )
        item.primary_region_id = preferred or item.compatible_region_ids[0]
        item.selected = True
        item.selection_rank = rank
        item.selection_score = None
        item.selection_reason = (
            "REQ10_RECALL_ALL_GROUNDED; no budget, cap, overlap, set-cover, "
            "proofability, or vacuity-risk filtering"
        )
        audit.append({
            "candidate_id": candidate.candidate_id,
            "module": candidate.module,
            "primitive": candidate.primitive,
            "obligation": candidate.primitive,
            "semantic_obligation": candidate.obligation,
            "compatible_region_ids": item.compatible_region_ids,
            "primary_region_id": item.primary_region_id,
            "binding_evidence_by_region": item.binding_evidence_by_region,
            "binding_levels": dict(Counter(
                value["binding_level"]
                for value in item.binding_evidence_by_region.values()
            )),
            "selected": True,
            "selection_rank": rank,
            "selection_score": None,
            "selection_components": {},
            "new_rtl_scope_items": None,
            "selection_reason": item.selection_reason,
            "proofability_score": candidate.proofability_score,
            "vacuity_risk": candidate.vacuity_risk,
            "rtl_relation": candidate.rtl_relation,
        })
    return selected, audit


def _select_compatible_region_saturation(
    bindings: list[LocalCandidateBinding], *, budget: int,
    primitive_caps: dict[str, int] | None = None,
    minimum_count: int = 0,
) -> tuple[list[LocalCandidateBinding], list[dict[str, Any]]]:
    """Historical G3 selector retained for a reproducible stage ablation.

    G3 treated every Region compatible with one selected relation as covered.
    G4 replaced this optimistic set-cover approximation with concrete primary
    Region marginal coverage.  Keeping the old policy behind an explicit
    configuration value lets the mandatory G3 and G4 full regressions compare
    one optimization at a time without reverting source files.
    """

    caps = {str(key).upper(): int(value) for key, value in (primitive_caps or {}).items()}
    selected: list[LocalCandidateBinding] = []
    remaining = list(bindings)
    covered_regions: set[str] = set()
    covered_pairs: set[tuple[str, str]] = set()
    primitive_counts: Counter[str] = Counter()
    target_counts: Counter[tuple[str, str]] = Counter()
    audit: list[dict[str, Any]] = []
    while remaining and len(selected) < budget:
        ranked = []
        for item in remaining:
            candidate = item.candidate
            primitive = candidate.primitive
            if primitive_counts[primitive] >= caps.get(primitive, budget):
                continue
            new_regions = set(item.compatible_region_ids) - covered_regions
            pairs = {
                (region_id, primitive) for region_id in item.compatible_region_ids
            }
            new_pairs = pairs - covered_pairs
            target = str(candidate.rtl_relation.get("lhs", ""))
            score = (
                80.0 * len(new_regions)
                + 18.0 * len(new_pairs)
                + 12.0 * candidate.proofability_score
                - 10.0 * candidate.vacuity_risk
                - 4.0 * target_counts[(candidate.module, target)]
                + min(6.0, len(candidate.structural_scope) / 8.0)
            )
            ranked.append((
                round(score, 6), candidate.proofability_score,
                candidate.candidate_id, item, new_regions, new_pairs,
            ))
        if not ranked:
            break
        score, _proof, _identifier, best, new_regions, new_pairs = max(ranked)
        candidate = best.candidate
        if (
            not new_regions
            and not new_pairs
            and len(selected) >= min(budget, max(1, minimum_count))
        ):
            break
        best.selected = True
        best.selection_rank = len(selected) + 1
        best.selection_score = score
        best.primary_region_id = min(
            best.compatible_region_ids,
            key=lambda region_id: (
                (region_id, candidate.primitive) in covered_pairs,
                region_id in covered_regions,
                region_id,
            ),
        )
        best.selection_reason = (
            "typed graph core membership + new Region/obligation coverage + proofability"
        )
        selected.append(best)
        covered_regions.update(best.compatible_region_ids)
        covered_pairs.update(
            (region_id, candidate.primitive)
            for region_id in best.compatible_region_ids
        )
        primitive_counts[candidate.primitive] += 1
        target_counts[(
            candidate.module, str(candidate.rtl_relation.get("lhs", "")),
        )] += 1
        remaining.remove(best)

    selected_ids = {item.candidate.candidate_id for item in selected}
    for item in bindings:
        audit.append({
            "candidate_id": item.candidate.candidate_id,
            "module": item.candidate.module,
            "primitive": item.candidate.primitive,
            "obligation": item.candidate.primitive,
            "semantic_obligation": item.candidate.obligation,
            "compatible_region_ids": item.compatible_region_ids,
            "binding_evidence_by_region": item.binding_evidence_by_region,
            "binding_levels": dict(Counter(
                value["binding_level"]
                for value in item.binding_evidence_by_region.values()
            )),
            "selected": item.candidate.candidate_id in selected_ids,
            "selection_rank": item.selection_rank,
            "selection_score": item.selection_score,
            "selection_components": {},
            "new_rtl_scope_items": None,
            "selection_reason": item.selection_reason or (
                "BUDGET_OR_REDUNDANCY_FILTERED"
                if item.candidate.candidate_id not in selected_ids else ""
            ),
            "proofability_score": item.candidate.proofability_score,
            "vacuity_risk": item.candidate.vacuity_risk,
            "rtl_relation": item.candidate.rtl_relation,
        })
    return selected, audit


def compile_rtl_properties(
    selected: list[LocalCandidateBinding], design: RTLDesign, reset_asserted: str,
) -> tuple[list[PropertyIR], list[TemplateBindingIR], dict[str, dict[str, Any]]]:
    contracts: list[ContractIR] = []
    by_contract_region: dict[str, LocalCandidateBinding] = {}
    for serial, item in enumerate(selected, start=1):
        contract = deepcopy(item.candidate.contract)
        unique_region = f"local_rtl_{serial:03d}_{_safe_id(item.primary_region_id)}"
        contract.contract_id = f"contract_{unique_region}"
        contract.region = unique_region
        contract.object_type = item.candidate.region_kind
        contract.ontology_classification = "NEW_OBJECT_CANDIDATE"
        for field in RULE_FIELD.values():
            for rule in getattr(contract, field):
                rule["provenance"] = "REQ8_7_TYPED_GRAPH_LOCAL_RTL"
                rule["region_flow_scope"] = "LOCAL"
        contracts.append(contract)
        by_contract_region[unique_region] = item
    properties, template_bindings = bind_extension_primitives(
        contracts,
        {module: set(values) for module, values in design.module_signals.items()},
        reset_asserted,
    )
    metadata: dict[str, dict[str, Any]] = {}
    binding_by_old_id = {item.property_id: item for item in template_bindings if item.property_id}
    for serial, prop in enumerate(properties, start=1):
        selected_item = by_contract_region[prop.region_id]
        candidate = selected_item.candidate
        old_id = prop.property_id
        property_id = f"local_rtl_{serial:03d}_{candidate.primitive.lower()}"
        prop.property_id = property_id
        prop.region_id = selected_item.primary_region_id
        if prop.template == "RESET":
            # A reset obligation must be sampled while reset is asserted; the
            # common operational disable condition would otherwise make the
            # property vacuous by construction.
            prop.disable_iff = ""
        prop.source = "typed-semantic-graph+three-level-binding-evidence+fixed-primitive"
        prop.source_classification = "RTL_STRUCTURAL"
        prop.llm_confidence = 1.0
        prop.description = (
            f"[LOCAL RTL_STRUCTURAL] {candidate.functional_meaning}; typed-graph-anchored in "
            f"{len(selected_item.compatible_region_ids)} Region(s), primary evidence "
            f"{selected_item.binding_evidence_by_region[selected_item.primary_region_id]['binding_level']}."
        )
        binding = binding_by_old_id.get(old_id)
        if binding:
            binding.property_id = property_id
            binding.region_id = selected_item.primary_region_id
        metadata[property_id] = {
            "property_id": property_id,
            "origin": "RTL_ONLY",
            "source_classification": "RTL_STRUCTURAL",
            "module": candidate.module,
            "region_id": selected_item.primary_region_id,
            "region_ids": selected_item.compatible_region_ids,
            "obligation": candidate.primitive,
            "semantic_obligation": candidate.obligation,
            "family": prop.family,
            "primitive": candidate.primitive,
            "candidate_id": candidate.candidate_id,
            "assignment_id": _candidate_assignment_id(candidate),
            "selection_rank": selected_item.selection_rank,
            "selection_score": selected_item.selection_score,
            "primary_binding_evidence": selected_item.binding_evidence_by_region[
                selected_item.primary_region_id
            ],
            "binding_evidence_by_region": selected_item.binding_evidence_by_region,
            "rtl_evidence": candidate.rtl_evidence,
        }
    return properties, template_bindings, metadata


def deduplicate_exact_properties(
    properties: list[PropertyIR], bindings: list[TemplateBindingIR],
    metadata: dict[str, dict[str, Any]],
) -> tuple[
    list[PropertyIR], list[TemplateBindingIR], dict[str, dict[str, Any]],
    list[dict[str, Any]],
]:
    """Remove only byte-normalized, module-local duplicate SVA semantics.

    Property labels and comments are excluded from the identity because they
    do not change the asserted behavior. Provenance from a removed duplicate
    is merged into the retained metadata so Region/obligation traceability is
    not lost.
    """

    kept: list[PropertyIR] = []
    kept_metadata: dict[str, dict[str, Any]] = {}
    retained_by_signature: dict[tuple[str, str, str], PropertyIR] = {}
    duplicate_to_retained: dict[str, str] = {}
    audit: list[dict[str, Any]] = []
    for prop in properties:
        signature = (
            str(prop.target_module),
            re.sub(r"\s+", "", str(prop.disable_iff or "")),
            re.sub(r"\s+", "", prop.body),
        )
        prior = retained_by_signature.get(signature)
        if prior is None:
            retained_by_signature[signature] = prop
            kept.append(prop)
            copied = deepcopy(metadata[prop.property_id])
            copied["exact_duplicate_property_ids"] = []
            copied["exact_duplicate_candidate_ids"] = []
            kept_metadata[prop.property_id] = copied
            audit.append({
                "property_id": prop.property_id,
                "disposition": "RETAINED_UNIQUE_SVA",
                "retained_property_id": prop.property_id,
                "target_module": prop.target_module,
                "body": prop.body,
            })
            continue
        duplicate_to_retained[prop.property_id] = prior.property_id
        prior_meta = kept_metadata[prior.property_id]
        duplicate_meta = metadata[prop.property_id]
        prior_meta["region_ids"] = sorted(set(
            prior_meta.get("region_ids", [prior_meta.get("region_id")])
        ) | set(
            duplicate_meta.get("region_ids", [duplicate_meta.get("region_id")])
        ) - {None, ""})
        prior_meta["exact_duplicate_property_ids"].append(prop.property_id)
        candidate_id = duplicate_meta.get("candidate_id")
        if candidate_id:
            prior_meta["exact_duplicate_candidate_ids"].append(candidate_id)
        audit.append({
            "property_id": prop.property_id,
            "disposition": "REMOVED_EXACT_DUPLICATE_SVA",
            "retained_property_id": prior.property_id,
            "target_module": prop.target_module,
            "body": prop.body,
        })
    kept_ids = {item.property_id for item in kept}
    kept_bindings: list[TemplateBindingIR] = []
    for binding in bindings:
        if binding.property_id in kept_ids:
            kept_bindings.append(binding)
        elif binding.property_id in duplicate_to_retained:
            audit.append({
                "binding_id": binding.binding_id,
                "disposition": "BINDING_MERGED_INTO_EXACT_DUPLICATE",
                "retained_property_id": duplicate_to_retained[binding.property_id],
            })
    return kept, kept_bindings, kept_metadata, audit


def expand_spec_behavior_obligations(
    spec_doc: dict[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Expand one validated SPEC fact into every directly grounded obligation.

    Safe one-to-many cases are an explicit STABILITY fact naming several
    design-owned signals and a DATA_INTEGRITY fact naming equally-sized,
    comma-separated SOURCE/TARGET lists.  Each signal (or source/target pair)
    gets an independently provable obligation. No new signal, timing,
    condition, or semantic claim is inferred.
    """

    def split_top_level_commas(value: Any) -> list[str]:
        if not isinstance(value, str):
            return []
        parts: list[str] = []
        start = 0
        depth = 0
        for index, char in enumerate(value):
            if char in "({[":
                depth += 1
            elif char in ")}]":
                depth = max(0, depth - 1)
            elif char == "," and depth == 0:
                parts.append(value[start:index].strip())
                start = index + 1
        parts.append(value[start:].strip())
        return [part for part in parts if part]

    output = deepcopy(spec_doc)
    expanded: list[dict[str, Any]] = []
    audit: list[dict[str, Any]] = []
    for behavior in output.get("behaviors", []):
        signals = behavior.get("roles", {}).get("SIGNALS", [])
        if (
            behavior.get("compilable")
            and str(behavior.get("primitive", "")).upper() == "STABILITY"
            and isinstance(signals, list) and len(signals) > 1
        ):
            for index, signal in enumerate(signals, 1):
                item = deepcopy(behavior)
                item["behavior_id"] = f"{behavior['behavior_id']}__signal_{index:02d}"
                item["parent_behavior_id"] = behavior["behavior_id"]
                item["roles"]["SIGNALS"] = [signal]
                item["functional_meaning"] = (
                    f"{behavior.get('functional_meaning', '')} "
                    f"(independent grounded stability obligation for {signal})"
                ).strip()
                expanded.append(item)
                audit.append({
                    "parent_behavior_id": behavior["behavior_id"],
                    "expanded_behavior_id": item["behavior_id"],
                    "primitive": "STABILITY",
                    "grounded_signal": signal,
                    "evidence": deepcopy(behavior.get("evidence", {})),
                })
            continue
        roles = behavior.get("roles", {})
        sources = split_top_level_commas(roles.get("SOURCE"))
        targets = split_top_level_commas(roles.get("TARGET"))
        if (
            behavior.get("compilable")
            and str(behavior.get("primitive", "")).upper() == "DATA_INTEGRITY"
            and len(sources) == len(targets) > 1
        ):
            for index, (source, target) in enumerate(zip(sources, targets), 1):
                item = deepcopy(behavior)
                item["behavior_id"] = f"{behavior['behavior_id']}__pair_{index:02d}"
                item["parent_behavior_id"] = behavior["behavior_id"]
                item["roles"]["SOURCE"] = source
                item["roles"]["TARGET"] = target
                item["functional_meaning"] = (
                    f"{behavior.get('functional_meaning', '')} "
                    f"(independent grounded data-integrity obligation for {source} -> {target})"
                ).strip()
                expanded.append(item)
                audit.append({
                    "parent_behavior_id": behavior["behavior_id"],
                    "expanded_behavior_id": item["behavior_id"],
                    "primitive": "DATA_INTEGRITY",
                    "grounded_source": source,
                    "grounded_target": target,
                    "evidence": deepcopy(behavior.get("evidence", {})),
                })
            continue
        expanded.append(behavior)
    output["behaviors"] = expanded
    return output, audit


def _normalized_words(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def validate_spec_response(
    response: dict[str, Any], lines: list[dict[str, Any]], design: RTLDesign, module: str,
) -> dict[str, Any]:
    """Fail closed unless every behavior is backed by an exact supplied quote."""

    if not isinstance(response, dict) or not isinstance(response.get("behaviors"), list):
        raise Requirement87ValidationError("SPEC response must contain a behaviors array")
    if _forbidden_generated_text(response):
        raise Requirement87ValidationError("SPEC extraction response attempted to provide SVA/assertion text")
    by_line = {int(item["line"]): str(item["text"]) for item in lines}
    known = set(design.module_signals.get(module, {}))
    output: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for raw in response["behaviors"]:
        if not isinstance(raw, dict):
            raise Requirement87ValidationError("each SPEC behavior must be an object")
        behavior_id = str(raw.get("behavior_id", "")).strip()
        if not behavior_id or behavior_id in seen_ids:
            raise Requirement87ValidationError("SPEC behavior_id must be non-empty and unique")
        seen_ids.add(behavior_id)
        evidence = raw.get("evidence", {})
        start, end = int(evidence.get("line_start", 0)), int(evidence.get("line_end", 0))
        quote = _normalized_words(str(evidence.get("quote", "")))
        if not quote or start not in by_line or end not in by_line or end < start:
            raise Requirement87ValidationError(f"{behavior_id}: invalid SPEC evidence range/quote")
        supplied = _normalized_words(" ".join(by_line.get(number, "") for number in range(start, end + 1)))
        if quote not in supplied:
            raise Requirement87ValidationError(f"{behavior_id}: evidence quote is not exact supplied SPEC text")
        confidence = raw.get("confidence")
        if not isinstance(confidence, (int, float)) or not 0 <= float(confidence) <= 1:
            raise Requirement87ValidationError(f"{behavior_id}: confidence must be in [0, 1]")
        primitive = raw.get("primitive")
        roles = deepcopy(raw.get("roles", {}))
        compilable = primitive is not None
        rejection_reason = ""
        if compilable:
            primitive = str(primitive).upper()
            if primitive not in GENERIC_PRIMITIVES or primitive not in _PRIMITIVE_ROLES:
                raise Requirement87ValidationError(f"{behavior_id}: unsupported primitive {primitive!r}")
            if not isinstance(roles, dict) or set(roles) != _PRIMITIVE_ROLES[primitive]:
                raise Requirement87ValidationError(f"{behavior_id}: roles do not match {primitive} signature")
            role_text = " ".join(_all_strings(roles))
            if "`" in role_text:
                raise Requirement87ValidationError(
                    f"{behavior_id}: preprocessor macros are not legal in the standalone checker context"
                )
            if "<=" in role_text or re.search(r"(?<![=!<>])=(?!=)", role_text):
                raise Requirement87ValidationError(
                    f"{behavior_id}: primitive roles must be expressions, not Verilog assignments"
                )
            # SIGNALS is a collection role. Some otherwise valid structured
            # responses encode it as a comma-separated JSON string. Normalize
            # that representation before the fixed compiler sees it; otherwise
            # it becomes an illegal multi-argument $stable() call.
            if primitive == "STABILITY" and isinstance(roles.get("SIGNALS"), str):
                roles["SIGNALS"] = [
                    item.strip() for item in roles["SIGNALS"].split(",") if item.strip()
                ]
            rule = {"primitive": primitive, "roles": roles}
            if _compile(primitive, rule) is None:
                raise Requirement87ValidationError(f"{behavior_id}: roles cannot compile with fixed primitive")
            referenced = set().union(*(expression_signals(item) for item in _all_strings(roles)))
            unknown = referenced - known
            if unknown:
                raise Requirement87ValidationError(f"{behavior_id}: roles reference unknown RTL signals {sorted(unknown)}")
            observed_roles = {
                "PERSISTENCE": ["START"], "STABILITY": ["SIGNALS"],
                "UPDATE": ["TARGET"], "DATA_INTEGRITY": ["TARGET"],
                "CAUSALITY": ["EFFECT"], "ORDERING": ["SECOND"],
                "PROGRESS": ["END"], "RESET": ["TARGET"], "HOLD": ["TARGET"],
                "CONTROL_ASSERT": ["TARGET"], "CONTROL_DEASSERT": ["TARGET"],
            }[primitive]
            observed = set()
            for role in observed_roles:
                observed.update(expression_signals(" ".join(_all_strings(roles.get(role)))))
            if not observed:
                rejection_reason = "NO_OBSERVED_RTL_SIGNAL"
            elif any(design.module_signals[module][name].direction == "input" for name in observed):
                rejection_reason = "ENVIRONMENT_BEHAVIOR_NOT_DESIGN_ASSERTION"
        else:
            primitive = None
            roles = {}
            rejection_reason = "NO_APPLICABLE_GENERIC_PROPERTY"
        copied = deepcopy(raw)
        copied.update({
            "primitive": primitive,
            "roles": roles,
            "spec_evidence_validated": True,
            "compilable": bool(compilable and not rejection_reason),
            "not_compiled_reason": rejection_reason,
        })
        output.append(copied)
    return {"schema": "region_flow.7-spec-behaviors.v1", "behaviors": output}


def map_spec_behaviors_to_regions(
    spec_doc: dict[str, Any], region_inventory: dict[str, Any], module: str,
) -> tuple[list[dict[str, Any]], dict[str, set[str]]]:
    regions = [item for item in region_inventory.get("regions", []) if item.get("module") == module]
    mapped = []
    overlays: dict[str, set[str]] = defaultdict(set)
    for behavior in spec_doc.get("behaviors", []):
        copied = deepcopy(behavior)
        if not behavior.get("compilable"):
            copied["rtl_mapping"] = {"status": "NOT_COMPILED", "region_ids": [], "signal_nodes": []}
            mapped.append(copied)
            continue
        referenced = set().union(*(expression_signals(item) for item in _all_strings(behavior.get("roles", {}))))
        scored = []
        for region in regions:
            if region.get("ontology_classification") != "CORE_REGION":
                continue
            core_names = {
                node.rsplit(".", 1)[-1] for node in region.get("core_node_ids", [])
                if str(node).startswith(f"signal:{module}.")
            }
            local_names = set(region.get("signals", []))
            score = 5 * len(referenced & core_names) + len(referenced & local_names)
            if score:
                scored.append((score, region["region_id"]))
        scored.sort(key=lambda item: (-item[0], item[1]))
        region_ids = [item[1] for item in scored[:3]]
        status = "MAPPED" if region_ids and referenced else "NO_RTL_REGION_MATCH"
        copied["rtl_mapping"] = {
            "status": status,
            "region_ids": region_ids,
            "signal_nodes": [f"signal:{module}.{name}" for name in sorted(referenced)],
            "mapping_basis": "typed semantic graph signal membership",
        }
        hint = str(behavior.get("core_region_hint", "")).upper()
        if status == "MAPPED" and hint in CORE_REGION_TYPES:
            overlays[region_ids[0]].add(hint)
        if status != "MAPPED":
            copied["compilable"] = False
            copied["not_compiled_reason"] = status
        mapped.append(copied)
    return mapped, overlays


def compile_spec_properties(
    behaviors: list[dict[str, Any]], design: RTLDesign, module: str, reset_asserted: str,
    spec_path: str | Path,
) -> tuple[list[PropertyIR], list[TemplateBindingIR], dict[str, dict[str, Any]]]:
    contracts = []
    behavior_by_contract_region = {}
    for serial, behavior in enumerate((item for item in behaviors if item.get("compilable")), start=1):
        primitive = str(behavior["primitive"])
        # ContractIR stores primitives without a dedicated semantic field
        # (currently PERSISTENCE/PROGRESS) in its generic invariants list. The
        # fixed compiler still dispatches on rule["primitive"].
        field = RULE_FIELD.get(primitive, "invariants")
        contract_region = f"local_spec_{serial:03d}_{_safe_id(str(behavior['behavior_id']))}"
        fields = {name: [] for name in RULE_FIELD.values()}
        fields[field] = [{
            "primitive": primitive,
            "roles": deepcopy(behavior["roles"]),
            "semantics": str(behavior.get("functional_meaning", "")),
            "confidence": float(behavior.get("confidence", 0.0)),
            "region_flow_scope": "LOCAL",
            "provenance": "REQ8_7_VALIDATED_SPEC_EVIDENCE",
        }]
        evidence = behavior["evidence"]
        contract = ContractIR(
            contract_id=f"contract_{contract_region}",
            object_type=str(behavior.get("core_region_hint") or "SPEC_BEHAVIOR"),
            ontology_classification="NEW_OBJECT_CANDIDATE",
            region=contract_region,
            module=module,
            evidence=[{
                "files": [str(Path(spec_path).resolve())],
                "line_start": int(evidence["line_start"]),
                "line_end": int(evidence["line_end"]),
                "snippet": str(evidence["quote"]),
                "source_kind": "SPEC",
                "region_flow_scope": "LOCAL",
            }],
            reused_primitives=[primitive],
            **fields,
        )
        contracts.append(contract)
        behavior_by_contract_region[contract_region] = behavior
    properties, bindings = bind_extension_primitives(
        contracts,
        {name: set(values) for name, values in design.module_signals.items()},
        reset_asserted,
    )
    metadata = {}
    binding_by_old = {item.property_id: item for item in bindings if item.property_id}
    for serial, prop in enumerate(properties, start=1):
        behavior = behavior_by_contract_region[prop.region_id]
        old_id = prop.property_id
        prop.property_id = f"local_spec_{serial:03d}_{str(behavior['primitive']).lower()}"
        mapped_regions = behavior["rtl_mapping"]["region_ids"]
        prop.region_id = mapped_regions[0]
        prop.source = "validated-spec-evidence+rtl-graph-mapping+fixed-primitive"
        prop.source_classification = "SPEC_CONFORMANCE"
        prop.llm_confidence = float(behavior["confidence"])
        prop.description = f"[LOCAL SPEC_CONFORMANCE] {behavior.get('functional_meaning', '')}"
        if prop.template == "RESET":
            prop.disable_iff = ""
        binding = binding_by_old.get(old_id)
        if binding:
            binding.property_id = prop.property_id
            binding.region_id = prop.region_id
        metadata[prop.property_id] = {
            "property_id": prop.property_id,
            "origin": "SPEC+RTL",
            "source_classification": "SPEC_CONFORMANCE",
            "module": module,
            "region_id": prop.region_id,
            "region_ids": mapped_regions,
            "obligation": str(behavior["primitive"]),
            "family": prop.family,
            "primitive": str(behavior["primitive"]),
            "behavior_id": behavior["behavior_id"],
            "spec_evidence": behavior["evidence"],
            "rtl_mapping": behavior["rtl_mapping"],
        }
    return properties, bindings, metadata


def result_counts(properties: list[PropertyIR], results: list[FormalPropertyResult]) -> dict[str, Any]:
    by_id = {item.property_id: item for item in results}
    selected = [by_id[item.property_id] for item in properties if item.property_id in by_id]
    counts = Counter(item.result for item in selected)
    accepted_correct = counts["PASS"] + counts["TIMEOUT_ACCEPTED"]
    return {
        "generated": len(properties),
        "pass": counts["PASS"],
        "cex": counts["FAIL"],
        "timeout_accepted": counts["TIMEOUT_ACCEPTED"],
        "not_evaluated": counts["NOT_EVALUATED"] + counts["ERROR"],
        "accepted_correct": accepted_correct,
        "vacuous": sum(item.vacuity == "VACUOUS" for item in selected),
        "non_vacuous": sum(item.vacuity == "NON_VACUOUS" for item in selected),
        "trusted": sum(item.result == "PASS" and item.vacuity == "NON_VACUOUS" for item in selected),
        "proven_rate_percent": round(100 * counts["PASS"] / len(selected), 2) if selected else 0.0,
        "accepted_correct_rate_percent": round(
            100 * accepted_correct / len(selected), 2
        ) if selected else 0.0,
        "trusted_rate_percent": round(
            100 * sum(item.result == "PASS" and item.vacuity == "NON_VACUOUS" for item in selected) / len(selected), 2
        ) if selected else 0.0,
    }


def build_obligation_funnel(
    region_inventory: dict[str, Any],
    bindings: list[LocalCandidateBinding],
    properties: list[PropertyIR],
    metadata: dict[str, dict[str, Any]],
    candidate_results: list[FormalPropertyResult],
    trusted_ids: set[str],
) -> dict[str, Any]:
    """Build the Req10 Region→obligation→SVA→Trust funnel.

    Counts at Region/type/module level are participation counts, so one
    assertion traced to multiple compatible Regions appears in each of those
    Region rows. Global assertion outcome counts remain unique by property ID.
    """

    regions = {
        str(item["region_id"]): item
        for item in region_inventory.get("regions", [])
        if item.get("kind") != "MODULE"
    }
    applicable_by_region: dict[str, set[tuple[str, str]]] = defaultdict(set)
    grounded_by_region: dict[str, set[str]] = defaultdict(set)
    for binding in bindings:
        candidate = binding.candidate
        obligation = str(candidate.obligation or candidate.primitive)
        for region_id in binding.compatible_region_ids:
            if region_id not in regions:
                continue
            applicable_by_region[region_id].add((candidate.candidate_id, obligation))
            grounded_by_region[region_id].add(candidate.candidate_id)

    properties_by_region: dict[str, set[str]] = defaultdict(set)
    obligations_by_region: dict[str, set[str]] = defaultdict(set)
    for prop in properties:
        item = metadata.get(prop.property_id, {})
        region_ids = item.get("region_ids") or [item.get("region_id") or prop.region_id]
        obligation = str(item.get("semantic_obligation") or item.get("obligation") or prop.template)
        source_key = str(item.get("candidate_id") or item.get("behavior_id") or prop.property_id)
        for region_id in region_ids:
            if region_id not in regions:
                continue
            applicable_by_region[region_id].add((source_key, obligation))
            grounded_by_region[region_id].add(source_key)
            properties_by_region[region_id].add(prop.property_id)
            obligations_by_region[region_id].add(obligation)

    result_by_id = {item.property_id: item for item in candidate_results}
    rows: list[dict[str, Any]] = []
    for region_id, region in sorted(regions.items()):
        property_ids = sorted(properties_by_region.get(region_id, set()))
        formal = [result_by_id[item] for item in property_ids if item in result_by_id]
        row = {
            "region_id": region_id,
            "region_kind": str(region.get("kind", "UNKNOWN")),
            "functional_area": str(region.get("module", "UNKNOWN")),
            "applicable_obligations": len(applicable_by_region.get(region_id, set())),
            "applicable_obligation_families": sorted({
                obligation for _source, obligation in applicable_by_region.get(region_id, set())
            }),
            "grounded_obligations": len(grounded_by_region.get(region_id, set())),
            "generated_sva": len(property_ids),
            "generated_property_ids": property_ids,
            "proven": sum(item.result == "PASS" for item in formal),
            "cex": sum(item.result == "FAIL" for item in formal),
            "timeout": sum(item.result == "TIMEOUT_ACCEPTED" for item in formal),
            "not_evaluated": sum(item.result in {"NOT_EVALUATED", "ERROR"} for item in formal),
            "non_vacuous": sum(item.vacuity == "NON_VACUOUS" for item in formal),
            "vacuous": sum(item.vacuity == "VACUOUS" for item in formal),
            "trusted": sum(item in trusted_ids for item in property_ids),
        }
        rows.append(row)

    def aggregate(selected: list[dict[str, Any]], key: str, value: str) -> dict[str, Any]:
        property_ids = {
            property_id for row in selected for property_id in row["generated_property_ids"]
        }
        selected_results = [result_by_id[item] for item in property_ids if item in result_by_id]
        return {
            key: value,
            "regions": len(selected),
            "regions_with_applicable_obligation": sum(row["applicable_obligations"] > 0 for row in selected),
            "applicable_obligations": sum(row["applicable_obligations"] for row in selected),
            "grounded_obligations": sum(row["grounded_obligations"] for row in selected),
            "generated_sva": len(property_ids),
            "regions_with_generated_sva": sum(row["generated_sva"] > 0 for row in selected),
            "proven": sum(item.result == "PASS" for item in selected_results),
            "cex": sum(item.result == "FAIL" for item in selected_results),
            "timeout": sum(item.result == "TIMEOUT_ACCEPTED" for item in selected_results),
            "not_evaluated": sum(item.result in {"NOT_EVALUATED", "ERROR"} for item in selected_results),
            "non_vacuous": sum(item.vacuity == "NON_VACUOUS" for item in selected_results),
            "vacuous": sum(item.vacuity == "VACUOUS" for item in selected_results),
            "trusted": len(property_ids & trusted_ids),
            "regions_with_trusted_obligation": sum(row["trusted"] > 0 for row in selected),
        }

    by_kind = [
        aggregate([row for row in rows if row["region_kind"] == kind], "region_kind", kind)
        for kind in sorted({row["region_kind"] for row in rows})
    ]
    by_area = [
        aggregate([row for row in rows if row["functional_area"] == area], "functional_area", area)
        for area in sorted({row["functional_area"] for row in rows})
    ]
    summary = aggregate(rows, "scope", "ALL_FUNCTIONAL_REGIONS")
    global_obligations = {
        (binding.candidate.candidate_id, str(
            binding.candidate.obligation or binding.candidate.primitive
        ))
        for binding in bindings
    }
    global_grounded = {binding.candidate.candidate_id for binding in bindings}
    for prop in properties:
        item = metadata.get(prop.property_id, {})
        source_key = str(item.get("candidate_id") or item.get("behavior_id") or prop.property_id)
        obligation = str(item.get("semantic_obligation") or item.get("obligation") or prop.template)
        global_obligations.add((source_key, obligation))
        global_grounded.add(source_key)
    summary["region_participating_applicable_obligations"] = summary["applicable_obligations"]
    summary["region_participating_grounded_obligations"] = summary["grounded_obligations"]
    summary["applicable_obligations"] = len(global_obligations)
    summary["grounded_obligations"] = len(global_grounded)
    summary["generated_local_assertions_per_region"] = round(
        len(properties) / len(rows), 4,
    ) if rows else 0.0
    return {
        "schema": "obligation_expansion-obligation-funnel.v1",
        "counting_policy": {
            "applicable": "evidence-supported candidate/Region bindings after deterministic static validation",
            "grounded": "candidate has literal typed-graph Region binding and fixed-primitive roles compile",
            "generated": "unique module+disable+PropertyIR-body after exact-SVA-only deduplication",
            "trusted": "PROVEN + NON_VACUOUS + no unproven assumption",
            "region_participation": "one assertion may participate in every explicitly recorded compatible Region",
        },
        "summary": summary,
        "by_region_type": by_kind,
        "by_functional_area": by_area,
        "regions": rows,
    }


def build_local_obligation_matrix(
    region_inventory: dict[str, Any], applicability_pairs: set[tuple[str, str]],
    properties: list[PropertyIR], metadata: dict[str, dict[str, Any]],
    results: list[FormalPropertyResult], trusted_ids: set[str],
) -> tuple[dict[str, Any], dict[str, Any]]:
    result_by_id = {item.property_id: item for item in results}
    property_by_pair: dict[tuple[str, str], list[str]] = defaultdict(list)
    origins_by_pair: dict[tuple[str, str], set[str]] = defaultdict(set)
    evidence_by_pair: dict[tuple[str, str], list[Any]] = defaultdict(list)
    for prop in properties:
        meta = metadata[prop.property_id]
        for region_id in meta.get("region_ids", [meta["region_id"]]):
            pair = (region_id, str(meta["obligation"]))
            property_by_pair[pair].append(prop.property_id)
            origins_by_pair[pair].add(str(meta["origin"]))
            evidence_by_pair[pair].append(meta.get("spec_evidence") or meta.get("rtl_evidence"))
    rows = []
    counts: Counter[str] = Counter()
    applicable = generated = trusted = 0
    for region in sorted(region_inventory.get("regions", []), key=lambda item: item["region_id"]):
        region_id = region["region_id"]
        names = sorted({obligation for rid, obligation in applicability_pairs if rid == region_id})
        cells = []
        for obligation in GENERIC_PRIMITIVES:
            pair = (region_id, obligation)
            property_ids = sorted(property_by_pair.get(pair, []))
            detail = ""
            if obligation not in names:
                status = "NOT_APPLICABLE"
            else:
                applicable += 1
                values = [result_by_id[item] for item in property_ids if item in result_by_id]
                if any(item in trusted_ids for item in property_ids):
                    status = "TRUSTED"
                    trusted += 1
                elif not property_ids:
                    status = "UNKNOWN"
                    detail = "APPLICABLE_NOT_GENERATED"
                elif any(item.result == "FAIL" for item in values):
                    status = "CEX"
                elif any(item.vacuity == "VACUOUS" for item in values):
                    status = "VACUOUS"
                elif any(item.result in {"UNKNOWN", "ERROR"} for item in values) or not values:
                    status = "UNKNOWN"
                else:
                    status = "GENERATED"
                if property_ids:
                    generated += 1
            counts[status] += 1
            cells.append({
                "obligation": obligation,
                "status": status,
                "detail": detail,
                "source": sorted(origins_by_pair.get(pair, [])),
                "property_ids": property_ids,
                "evidence": evidence_by_pair.get(pair, []),
            })
        rows.append({
            "region_id": region_id,
            "region_kind": region.get("kind"),
            "ontology_classification": region.get("ontology_classification"),
            "module": region.get("module"),
            "obligations": cells,
        })
    coverage = {
        "definition": "Trusted evidence-backed Region/obligation pairs / all applicable evidence-backed pairs",
        "applicable_obligations": applicable,
        "generated_obligations": generated,
        "trusted_obligations": trusted,
        "generated_coverage_percent": round(100 * generated / applicable, 2) if applicable else 0.0,
        "trusted_coverage_percent": round(100 * trusted / applicable, 2) if applicable else 0.0,
    }
    return {
        "schema": "region_flow.7-local-obligation-matrix.v1",
        "status_definitions": {
            "GENERATED": "generated but not yet classified by Formal",
            "TRUSTED": "PASS for every elaborated target and NON_VACUOUS",
            "CEX": "Formal counterexample",
            "UNKNOWN": "Formal unknown/error or missing elaborated target",
            "VACUOUS": "antecedent/precondition is unreachable",
            "NOT_APPLICABLE": "no evidence-backed candidate for this Region/obligation",
        },
        "counts": dict(counts),
        "regions": rows,
    }, coverage


def region_participation(
    region_inventory: dict[str, Any], metadata: dict[str, dict[str, Any]], trusted_ids: set[str],
) -> dict[str, Any]:
    all_regions = {item["region_id"] for item in region_inventory.get("regions", [])}
    participating = {
        region_id for property_id, meta in metadata.items() if property_id in trusted_ids
        for region_id in meta.get("region_ids", [meta["region_id"]])
    } & all_regions
    return {
        "definition": "Region has at least one graph-anchored Trusted local assertion",
        "total_regions": len(all_regions),
        "regions_with_trusted_assertion": len(participating),
        "coverage_percent": round(100 * len(participating) / len(all_regions), 2) if all_regions else 0.0,
        "participating_region_ids": sorted(participating),
    }


def candidate_inventory(bindings: list[LocalCandidateBinding]) -> list[dict[str, Any]]:
    result = []
    for item in bindings:
        candidate = item.candidate
        result.append({
            "candidate_id": candidate.candidate_id,
            "module": candidate.module,
            "primitive": candidate.primitive,
            "obligation": candidate.primitive,
            "semantic_obligation": candidate.obligation,
            "rtl_relation": candidate.rtl_relation,
            "rtl_evidence": candidate.rtl_evidence,
            "compatible_region_ids": item.compatible_region_ids,
            "binding_evidence_by_region": item.binding_evidence_by_region,
            "binding_levels": dict(Counter(
                value["binding_level"] for value in item.binding_evidence_by_region.values()
            )),
            "primary_region_id": item.primary_region_id,
            "selected": item.selected,
            "selection_rank": item.selection_rank,
            "selection_score": item.selection_score,
            "selection_reason": item.selection_reason,
            "proofability_score": candidate.proofability_score,
            "vacuity_risk": candidate.vacuity_risk,
        })
    return result
