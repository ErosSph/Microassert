"""Requirement 12: resumable, evidence-preserving ten-round feedback.

This module deliberately starts *after* a completed no-feedback Req8.10
Local+Composition run.  It does not reintroduce historical experimental arms
and it never turns a desired Local/Composite ratio into a quota.  A round is
always driven by the exact previous cumulative proof-core coverage:

``coverage -> typed gap localisation -> Region/Local delta -> Contract delta
-> SPEC+RTL constrained composition delta -> probes -> exact full portfolio``.

The implementation is intentionally usable independently of the command-line
driver so a design worker can call :func:`run_feedback` directly.
"""

from __future__ import annotations

from collections import Counter
from copy import deepcopy
import hashlib
import json
from math import ceil
from pathlib import Path
from typing import Any

from dateassertion.coverage_analysis.proof_core import CoverItem, parse_coverage_items
from dateassertion.ir.schema import FormalPropertyResult, FormalRunResult, PropertyIR, dump_json, properties_from_dict
from dateassertion.llm.client import DeepSeekClient, LLMUnavailableError
from dateassertion.pipeline.contract_validation import _llm_config
from dateassertion.pipeline.feedback_work_selection import select_current_gap_work
from dateassertion.pipeline.composition_expansion import expand_initial_composition
from dateassertion.pipeline.feedback_regions import (
    compile_refinement_properties,
    discover_refinement_candidates,
    interpret_refinements,
    localize_refinement_gaps,
)
from dateassertion.pipeline.formal_gap_semantics import (
    coverage_by_type,
    gap_summary,
    property_from_assignment,
    select_contract_gap_assignments,
    stable_cover_item_id,
)
from dateassertion.pipeline.local_contract_composition import (
    _relation,
    build_contract_graph,
    build_local_contracts,
    compile_composition_properties,
    generate_composition_candidates,
    select_composition_portfolio,
)
from dateassertion.pipeline.local_region_assertions import result_counts
from dateassertion.pipeline.property_portfolio_planner import build_property_candidate_pool
from dateassertion.pipeline.spec_composition import _validated_llm_constraints
from dateassertion.pipeline.design_flow import (
    PROJECT_ROOT,
    _filter_renderable_properties,
    _formal,
    _formal_config,
    _resolve,
    _stable_formal,
)
from dateassertion.rtl_frontend.hierarchical_design import build_hierarchical_design_map
from dateassertion.rtl_frontend.parser import RTLDesign, parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph


SCHEMA = "feedback-feedback-rounds.v1"


def _read(path: Path, default: Any = None) -> Any:
    return json.loads(path.read_text(encoding="utf-8")) if path.is_file() else deepcopy(default)


def _sha(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, sort_keys=True, default=str).encode("utf-8")
    ).hexdigest()


def _file_sha(path: Path) -> str:
    if not path.is_file():
        raise RuntimeError(f"required identity artifact is missing: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _algorithm_identity() -> dict[str, str]:
    """Resume must not silently mix results across feedback implementation drift."""

    files = (
        Path(__file__),
        PROJECT_ROOT / "pipeline" / "feedback_regions.py",
        PROJECT_ROOT / "pipeline" / "feedback_work_selection.py",
        PROJECT_ROOT / "pipeline" / "formal_gap_semantics.py",
        PROJECT_ROOT / "pipeline" / "local_contract_composition.py",
        PROJECT_ROOT / "pipeline" / "local_region_assertions.py",
        PROJECT_ROOT / "pipeline" / "composition_expansion.py",
        PROJECT_ROOT / "pipeline" / "design_flow.py",
        PROJECT_ROOT / "formal" / "jaspergold.py",
        PROJECT_ROOT / "formal" / "result_parser.py",
        PROJECT_ROOT / "llm" / "client.py",
    )
    return {str(path.relative_to(PROJECT_ROOT)): _file_sha(path) for path in files}


def _property_key(prop: PropertyIR) -> str:
    """Exact compiled-SVA identity used for deduplication and no-retry history."""

    return _sha({
        "module": prop.target_module,
        "disable_iff": "".join((prop.disable_iff or "").split()),
        "body": "".join(prop.body.split()),
    })


def _region_key(region: dict[str, Any]) -> str:
    return _sha({
        "module": region.get("module", ""),
        "core": sorted(map(str, region.get("core_node_ids", []))),
        "assignments": sorted(map(str, region.get("assignment_node_ids", []))),
    })


def _is_composite(prop: PropertyIR) -> bool:
    return (
        prop.source_classification == "COMPOSITIONAL_CONTRACT"
        or prop.template.startswith("COMPOSITE_")
        or prop.family.startswith("COMPOSITE_")
    )


def _result_doc(path: Path) -> FormalRunResult:
    raw = _read(path)
    if not raw:
        raise RuntimeError(f"missing Formal result artifact: {path}")
    return FormalRunResult(
        status=raw["status"], tool=raw.get("tool", "jaspergold"),
        runtime_seconds=float(raw.get("runtime_seconds", 0.0)),
        log_path=str(raw.get("log_path", "")),
        results=[FormalPropertyResult(**item) for item in raw.get("results", [])],
        summary=raw.get("summary", {}), coverage=raw.get("coverage", {}),
        notes=raw.get("notes", []),
    )


def _initial_formal_root(initial_root: Path) -> Path:
    """Locate the exact final no-feedback portfolio, never a candidate probe."""

    for root in (
        initial_root / "formal" / "without_feedback",
        initial_root / "formal" / "with_feedback",
        initial_root / "formal",
    ):
        if (root / "formal" / "formal_results.json").is_file() and (
            root / "formal" / "coverage_items.tsv"
        ).is_file():
            return root
    raise RuntimeError(
        "initial_root has no completed full Local+Composition proof-core run; "
        "expected formal/{without_feedback,with_feedback}/formal/{formal_results.json,coverage_items.tsv}"
    )


def _require_initial_portfolio(initial_root: Path) -> tuple[list[PropertyIR], FormalRunResult, list[CoverItem], Path]:
    """Load only an exact, non-empty completed Local+Composition baseline."""

    required = (
        initial_root / "regions.json",
        initial_root / "local_contracts.json",
        initial_root / "local_candidates.json",
        initial_root / "composition_properties.json",
        initial_root / "partial_order_constraints.json",
    )
    missing_artifacts = [str(path) for path in required if not path.is_file()]
    if missing_artifacts:
        raise RuntimeError(f"initial run is incomplete; missing artifacts: {missing_artifacts}")
    props_file = initial_root / "final" / "trusted_properties.json"
    if not props_file.is_file():
        raise RuntimeError(f"initial_root lacks exact trusted portfolio: {props_file}")
    props = properties_from_dict(_read(props_file, []))
    if not props:
        raise RuntimeError("initial Local+Composition portfolio is empty")
    if len({prop.property_id for prop in props}) != len(props):
        raise RuntimeError("initial trusted portfolio has duplicate property IDs")
    if not _read(initial_root / "local_candidates.json", []):
        raise RuntimeError("initial Local candidate artifact is empty; this is not a completed full flow")
    if not _read(initial_root / "regions.json", {}).get("regions", []):
        raise RuntimeError("initial Region inventory is empty")
    if not _read(initial_root / "local_contracts.json", {}).get("contracts", []):
        raise RuntimeError("initial Local Contract inventory is empty")
    formal_root = _initial_formal_root(initial_root)
    sva_path = formal_root / "assertions.sv"
    if not sva_path.is_file() or not sva_path.read_text(encoding="utf-8", errors="replace").strip():
        raise RuntimeError("initial full portfolio has no rendered assertion file")
    result = _result_doc(formal_root / "formal" / "formal_results.json")
    by_id = {item.property_id: item for item in result.results}
    missing = [prop.property_id for prop in props if prop.property_id not in by_id]
    non_strict = [
        prop.property_id for prop in props
        if prop.property_id in by_id
        and not (by_id[prop.property_id].result == "PASS" and by_id[prop.property_id].vacuity == "NON_VACUOUS")
    ]
    extra = sorted(set(by_id) - {prop.property_id for prop in props})
    if missing or extra or non_strict:
        raise RuntimeError(
            "initial portfolio is not a completed strict Local+Composition baseline: "
            f"missing={missing[:8]}, extra={extra[:8]}, non_strict={non_strict[:8]}"
        )
    items = parse_coverage_items(formal_root / "formal" / "coverage_items.tsv")
    if not items:
        raise RuntimeError("initial full portfolio exported an empty proof-core coverage universe")
    return props, result, items, formal_root


def _metadata_for(properties: list[PropertyIR]) -> dict[str, dict[str, Any]]:
    """Build the minimal complete Region attribution expected by Local Contracts."""

    return {
        prop.property_id: {
            "property_id": prop.property_id,
            "region_ids": [prop.region_id],
            "region_id": prop.region_id,
            "source_classification": prop.source_classification,
        }
        for prop in properties
        if not _is_composite(prop)
    }


def _initial_metadata(initial_root: Path, properties: list[PropertyIR]) -> dict[str, dict[str, Any]]:
    """Preserve initial multi-Region attribution instead of collapsing to display Region."""

    metadata = _metadata_for(properties)
    final_ids = {item.property_id for item in properties}
    trace = _read(initial_root / "assertion_spec_traceability.json", {}).get("records", [])
    for row in trace:
        property_id = str(row.get("property_id", ""))
        if property_id not in metadata or property_id not in final_ids:
            continue
        region_ids = [str(item) for item in row.get("region_ids", []) if item]
        if region_ids:
            metadata[property_id]["region_ids"] = sorted(set(region_ids))
        metadata[property_id]["spec_evidence"] = deepcopy(row.get("spec_evidence", []))
        metadata[property_id]["spec_behavior_ids"] = deepcopy(row.get("spec_behavior_ids", []))
        metadata[property_id]["traceability_source"] = "assertion_spec_traceability"
    bindings = _read(initial_root / "template_bindings.json", [])
    grouped: dict[str, set[str]] = {}
    for row in bindings:
        property_id, region_id = str(row.get("property_id", "")), str(row.get("region_id", ""))
        if property_id in metadata and region_id:
            grouped.setdefault(property_id, set()).add(region_id)
    for property_id, region_ids in grouped.items():
        # Traceability contains the complete multi-Region provenance where
        # available; template bindings are a sound fallback/augmentation.
        metadata[property_id]["region_ids"] = sorted(
            set(metadata[property_id].get("region_ids", [])) | region_ids
        )
    return metadata


def _contract_fingerprint(contract: dict[str, Any]) -> str:
    return _sha({
        "region_id": contract.get("region_id"),
        "module": contract.get("module"),
        "interface": contract.get("interface", {}),
        "obligations": contract.get("trusted_local_obligations", []),
        "readiness": contract.get("readiness_level"),
    })


def _active_constraints(doc: dict[str, Any], contracts: list[dict[str, Any]]) -> dict[str, Any]:
    """Retain only prior constraints whose exact contract/event endpoints remain real."""

    events = {
        (str(contract["contract_id"]), str(event["event_id"]))
        for contract in contracts for event in contract.get("interface", {}).get("events", [])
    }
    constraints = [
        deepcopy(item) for item in doc.get("constraints", [])
        if (str(item.get("source_contract_id")), str(item.get("source_event_id"))) in events
        and (str(item.get("target_contract_id")), str(item.get("target_event_id"))) in events
    ]
    ids = {item["constraint_id"] for item in constraints}
    chains = [
        deepcopy(item) for item in doc.get("lifecycle_chains", [])
        if item.get("constraint_ids") and all(cid in ids for cid in item["constraint_ids"])
    ]
    return {
        "schema": "feedback-active-constraints.v1",
        "constraints": constraints,
        "lifecycle_chains": chains,
        "dropped_stale_constraints": len(doc.get("constraints", [])) - len(constraints),
    }


def _merge_delta_constraints(
    existing: dict[str, Any], delta: dict[str, Any], *, round_index: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Merge a bounded composition delta without breaking an old/new chain.

    A compact composition request may intentionally use an already-retained
    relation as the first link of a *new* continuous chain, for example
    ``A--B`` (old) followed by ``B--C`` (new).  Therefore a semantically
    duplicate delta relation must map its transient LLM ID to the retained
    ID; simply dropping it would leave the new chain with an unresolved link.
    """

    def semantic_key(item: dict[str, Any]) -> str:
        return _sha({key: item.get(key) for key in (
            "source_contract_id", "source_event_id", "target_contract_id", "target_event_id",
            "relation_type", "min_delay", "max_delay", "source_predicate", "target_predicate", "evidence",
        )})

    values = [deepcopy(item) for item in existing.get("constraints", [])]
    known_semantics = {semantic_key(item): str(item["constraint_id"]) for item in values}
    by_id = {str(item["constraint_id"]): item for item in values}
    used_ids = {str(item["constraint_id"]) for item in values}
    id_map: dict[str, str] = {}
    retained_delta: list[dict[str, Any]] = []
    duplicate_semantics = 0
    duplicate_evidence_merged = 0
    for raw in delta.get("constraints", []):
        item = deepcopy(raw)
        old = str(item["constraint_id"])
        semantic = semantic_key(item)
        existing_id = known_semantics.get(semantic)
        if existing_id is not None:
            duplicate_semantics += 1
            # Preserve the link ID for a delta chain.  The semantic key
            # deliberately includes exact SPEC evidence, but keep a defensive
            # evidence merge for schema-compatible callers that supply a
            # supplemental evidence list.
            id_map[old] = existing_id
            prior = by_id[existing_id]
            incoming_evidence = item.get("evidence")
            if incoming_evidence is not None and incoming_evidence != prior.get("evidence"):
                supplements = prior.setdefault("supplemental_evidence", [])
                if incoming_evidence not in supplements:
                    supplements.append(deepcopy(incoming_evidence))
                    duplicate_evidence_merged += 1
            continue
        new = f"feedback_r{round_index:02d}_{old}"
        serial = 2
        while new in used_ids:
            new = f"feedback_r{round_index:02d}_{old}_{serial}"
            serial += 1
        item["constraint_id"] = new
        id_map[old] = new
        used_ids.add(new)
        known_semantics[semantic] = new
        values.append(item)
        by_id[new] = item
        retained_delta.append(item)
    chains = [deepcopy(item) for item in existing.get("lifecycle_chains", [])]
    used_chain_ids = {str(item.get("chain_id", "")) for item in chains}
    known_chain_paths = {tuple(str(cid) for cid in item.get("constraint_ids", [])) for item in chains}
    retained_chains: list[dict[str, Any]] = []
    duplicate_chains = 0
    for raw in delta.get("lifecycle_chains", []):
        mapped = [id_map.get(str(cid)) for cid in raw.get("constraint_ids", [])]
        if len(mapped) < 2 or any(item is None for item in mapped):
            continue
        path = tuple(str(item) for item in mapped)
        if path in known_chain_paths:
            duplicate_chains += 1
            continue
        item = deepcopy(raw)
        base_chain_id = f"feedback_r{round_index:02d}_{raw.get('chain_id', 'chain')}"
        chain_id = base_chain_id
        serial = 2
        while chain_id in used_chain_ids:
            chain_id = f"{base_chain_id}_{serial}"
            serial += 1
        item["chain_id"] = chain_id
        item["constraint_ids"] = mapped
        chains.append(item)
        used_chain_ids.add(chain_id)
        known_chain_paths.add(path)
        retained_chains.append(item)
    return ({"constraints": values, "lifecycle_chains": chains}, {
        "added_constraints": len(retained_delta), "duplicate_semantic_constraints": duplicate_semantics,
        "duplicate_evidence_merged": duplicate_evidence_merged,
        "added_lifecycle_chains": len(retained_chains), "duplicate_lifecycle_chains": duplicate_chains,
        "delta_constraint_ids": [item["constraint_id"] for item in retained_delta],
        "delta_chain_ids": [item["chain_id"] for item in retained_chains],
    })


def _incremental_composition_input(
    active_constraints: dict[str, Any], merge_audit: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Build the minimal constraint closure needed for an incremental chain.

    ``generate_composition_candidates`` indexes every constraint referenced by
    a lifecycle chain.  Passing only fresh edges would make an old ``A->B`` +
    new ``B->C`` chain invalid.  This helper includes that necessary old edge
    in the input, but records it as *closure only*.  The caller subsequently
    removes closure-only adjacent candidates, so this is not a whole-graph
    re-enumeration of previous compositions.
    """

    by_id = {str(item["constraint_id"]): item for item in active_constraints.get("constraints", [])}
    delta_constraint_ids = {str(item) for item in merge_audit.get("delta_constraint_ids", [])}
    delta_chain_ids = {str(item) for item in merge_audit.get("delta_chain_ids", [])}
    selected_chains = [
        deepcopy(item) for item in active_constraints.get("lifecycle_chains", [])
        if str(item.get("chain_id", "")) in delta_chain_ids
        or any(str(cid) in delta_constraint_ids for cid in item.get("constraint_ids", []))
    ]
    closure_ids = set(delta_constraint_ids)
    for chain in selected_chains:
        closure_ids.update(str(cid) for cid in chain.get("constraint_ids", []))
    missing = sorted(closure_ids - set(by_id))
    if missing:
        # Active constraints are supposed to have already removed stale
        # chains; retain a concrete audit rather than risk a KeyError deeper
        # in the shared composition candidate generator.
        selected_chains = [
            item for item in selected_chains
            if all(str(cid) in by_id for cid in item.get("constraint_ids", []))
        ]
        closure_ids = set(delta_constraint_ids)
        for chain in selected_chains:
            closure_ids.update(str(cid) for cid in chain.get("constraint_ids", []))
    selected_constraints = [
        deepcopy(item) for item in active_constraints.get("constraints", [])
        if str(item["constraint_id"]) in closure_ids
    ]
    return ({
        "constraints": selected_constraints,
        "lifecycle_chains": selected_chains,
    }, {
        "delta_constraint_ids": sorted(delta_constraint_ids),
        "delta_chain_ids": sorted(delta_chain_ids),
        "selected_chain_ids": [str(item.get("chain_id", "")) for item in selected_chains],
        "selected_chain_paths": [
            [str(cid) for cid in item.get("constraint_ids", [])] for item in selected_chains
        ],
        "closure_constraint_ids": sorted(closure_ids),
        "closure_only_constraint_ids": sorted(closure_ids - delta_constraint_ids),
        "missing_constraint_ids": missing,
    })


def _retain_incremental_composition_candidates(
    candidate_doc: dict[str, Any], incremental_audit: dict[str, Any],
) -> dict[str, Any]:
    """Keep direct fresh relations and candidates induced by a fresh chain.

    Old links included solely to close a new chain are necessary for semantic
    continuity, but their one-edge assertions were already considered in an
    earlier portfolio.  A multi-edge candidate is retained only when it is a
    prefix of one of the selected delta chains; this also admits a *new* chain
    composed entirely of retained edges.
    """

    fresh_edges = set(incremental_audit.get("delta_constraint_ids", []))
    # Preserve the exact delta-chain paths supplied by the selection helper;
    # do not rediscover paths from the whole graph.
    selected_paths = {
        tuple(str(cid) for cid in path)
        for path in incremental_audit.get("selected_chain_paths", [])
    }

    def is_incremental(candidate: dict[str, Any]) -> bool:
        ids = tuple(str(cid) for cid in candidate.get("constraint_ids", []))
        if any(cid in fresh_edges for cid in ids):
            return True
        return len(ids) >= 2 and any(path[:len(ids)] == ids for path in selected_paths)

    values = [deepcopy(item) for item in candidate_doc.get("candidates", []) if is_incremental(item)]
    removed = len(candidate_doc.get("candidates", [])) - len(values)
    rejected = dict(candidate_doc.get("rejections", {}))
    if removed:
        rejected["CLOSURE_ONLY_ADJACENT_EXCLUDED"] = rejected.get("CLOSURE_ONLY_ADJACENT_EXCLUDED", 0) + removed
    return {
        **{key: deepcopy(value) for key, value in candidate_doc.items() if key not in {"candidates", "rejections", "summary"}},
        "candidates": values,
        "rejections": rejected,
        "summary": {
            "candidates": len(values),
            "by_level": dict(Counter(item["level"] for item in values)),
            "regions_participating": len({region for item in values for region in item["region_ids"]}),
            "relations_participating": len({edge for item in values for edge in item["edge_ids"]}),
            "closure_only_candidates_excluded": removed,
        },
    }


def incremental_contract_graph(
    previous_graph: dict[str, Any], contracts: list[dict[str, Any]],
    constraints: dict[str, Any], changed_contract_ids: set[str],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Update only graph edges touching a new *or revised* Local Contract.

    The older helper handles only fresh IDs.  Feedback revisions may keep a
    Region's stable contract ID while its events/readiness change, so both new
    and changed endpoints must invalidate their incident edges.  Unaffected
    edges are copied verbatim and never re-scored.
    """

    by_id = {str(item["contract_id"]): item for item in contracts}
    changed = set(changed_contract_ids) & set(by_id)
    retained = [
        deepcopy(edge) for edge in previous_graph.get("edges", [])
        if edge.get("source_contract_id") in by_id
        and edge.get("target_contract_id") in by_id
        and edge.get("source_contract_id") not in changed
        and edge.get("target_contract_id") not in changed
    ]
    recomputed: dict[str, dict[str, Any]] = {}
    pair_evaluations = 0
    for source in contracts:
        if source.get("readiness_level", 0) < 1:
            continue
        for target in contracts:
            if target.get("readiness_level", 0) < 1:
                continue
            if source["contract_id"] not in changed and target["contract_id"] not in changed:
                continue
            pair_evaluations += 1
            edge = _relation(source, target)
            if edge:
                recomputed[edge["edge_id"]] = edge
    for constraint in constraints.get("constraints", []):
        source_id, target_id = str(constraint["source_contract_id"]), str(constraint["target_contract_id"])
        if source_id not in changed and target_id not in changed:
            continue
        if source_id not in by_id or target_id not in by_id:
            continue
        edge = _relation(by_id[source_id], by_id[target_id], spec_constraint=constraint)
        if edge:
            recomputed[edge["edge_id"]] = edge
    edges = {item["edge_id"]: item for item in retained}
    edges.update(recomputed)
    values = sorted(edges.values(), key=lambda item: item["edge_id"])
    graph = {
        "schema": "feedback-incremental-contract-graph.v1",
        "nodes": deepcopy(contracts), "edges": values,
        "summary": {
            "nodes": len(contracts), "edges": len(values),
            "by_relation": dict(Counter(item["relation_type"] for item in values)),
            "by_context": dict(Counter(item["execution_context_status"] for item in values)),
            "spec_constrained_edges": sum(bool(item.get("spec_constraint_id")) for item in values),
            "incremental": True,
        },
    }
    audit = {
        "schema": "feedback-incremental-contract-edge-update.v1",
        "changed_contract_ids": sorted(changed),
        "retained_unaffected_edges": len(retained),
        "recomputed_edges_touching_changed_contract": len(recomputed),
        "full_directed_pair_space": len(contracts) * max(0, len(contracts) - 1),
        "evaluated_directed_pair_space": pair_evaluations,
        "unaffected_edges_recomputed": 0,
    }
    return graph, audit


def _interface_neighbours(contracts: list[dict[str, Any]], changed: set[str], limit: int) -> list[dict[str, Any]]:
    """Bound LLM input to delta contracts and typed-interface neighbours."""

    by_id = {str(item["contract_id"]): item for item in contracts}
    selected = [by_id[item] for item in sorted(changed) if item in by_id]
    selected_ids = {item["contract_id"] for item in selected}
    scored: list[tuple[int, dict[str, Any]]] = []
    for candidate in contracts:
        if candidate["contract_id"] in selected_ids or candidate.get("readiness_level", 0) < 1:
            continue
        score = 0
        for delta in selected:
            if candidate.get("module") != delta.get("module"):
                continue
            delta_out = set(delta.get("interface", {}).get("outputs", [])) | set(delta.get("interface", {}).get("state", []))
            cand_out = set(candidate.get("interface", {}).get("outputs", [])) | set(candidate.get("interface", {}).get("state", []))
            delta_in = set(delta.get("interface", {}).get("inputs", [])) | set(delta.get("interface", {}).get("state", []))
            cand_in = set(candidate.get("interface", {}).get("inputs", [])) | set(candidate.get("interface", {}).get("state", []))
            score = max(score, len(delta_out & cand_in), len(cand_out & delta_in))
        if score:
            scored.append((score, candidate))
    for _, candidate in sorted(scored, key=lambda row: (-row[0], row[1]["contract_id"])):
        if len(selected) >= limit:
            break
        selected.append(candidate)
    return selected


def _compact_contract(contract: dict[str, Any]) -> dict[str, Any]:
    """The only RTL summary exposed to the SPEC relation interpreter."""

    interface = contract.get("interface", {})
    return {
        "contract_id": contract["contract_id"], "region_id": contract["region_id"],
        "module": contract["module"], "region_kind": contract.get("region_kind", "UNKNOWN"),
        "readiness_level": contract.get("readiness_level", 0),
        "inputs": interface.get("inputs", []), "outputs": interface.get("outputs", []),
        "state": interface.get("state", []),
        "events": [{key: event.get(key) for key in (
            "event_id", "predicate", "semantic_role", "event_kind", "signals", "source",
        )} for event in interface.get("events", [])],
        "trusted_local_obligations": contract.get("trusted_local_obligations", []),
    }


def _delta_composition_context(spec_lines: list[dict[str, Any]], contracts: list[dict[str, Any]], changed: set[str], limit: int) -> dict[str, Any]:
    selected = _interface_neighbours(contracts, changed, limit)
    return {
        "schema": "feedback-delta-spec-composition-context.v1",
        "whole_design_rtl_supplied": False,
        "incremental_scope": {
            "changed_contract_ids": sorted(changed),
            "selection": "changed contracts plus same-module typed-interface neighbours",
            "selected_contracts": [item["contract_id"] for item in selected],
        },
        "spec_lines": deepcopy(spec_lines),
        "allowed_relation_types": ["CAUSALITY", "ORDERING", "DATA_TRANSFER", "STATE_CONTROL"],
        "allowed_contract_ids": [item["contract_id"] for item in selected],
        "contracts": [_compact_contract(item) for item in selected],
        "prohibited_outputs": ["SVA", "SystemVerilog", "assert property", "assume property"],
    }


def _composition_context_key(source: dict[str, Any], target: dict[str, Any], relation: dict[str, Any]) -> str:
    """Identity of a real interface context, not a signal-name keyword match."""

    return _sha({
        "source": source["contract_id"], "target": target["contract_id"],
        "shared_interface_signals": relation.get("shared_interface_signals", []),
        "source_events": [item.get("event_id") for item in source.get("interface", {}).get("events", [])],
        "target_events": [item.get("event_id") for item in target.get("interface", {}).get("events", [])],
    })


def _typed_interface_pair_queue(
    contracts: list[dict[str, Any]], constraints: dict[str, Any], history: dict[str, Any],
) -> list[dict[str, Any]]:
    """Enumerate unvisited trusted Contract pairs with an actual typed RTL edge.

    This queue is deliberately narrower than arbitrary graph-path enumeration:
    both endpoints already have strict Local evidence, must belong to the same
    RTL module, must share a source-output -> target-input/state edge, and
    must expose real Contract events.  SPEC interpretation can select event
    ordering *only* inside such a context; it cannot invent an interface.
    """

    constrained_pairs = {
        (str(item.get("source_contract_id")), str(item.get("target_contract_id")))
        for item in constraints.get("constraints", [])
    }
    values: list[dict[str, Any]] = []
    for source in contracts:
        if int(source.get("readiness_level", 0)) < 2 or not source.get("interface", {}).get("events"):
            continue
        for target in contracts:
            if int(target.get("readiness_level", 0)) < 2 or not target.get("interface", {}).get("events"):
                continue
            relation = _relation(source, target)
            if not relation or not relation.get("shared_interface_signals"):
                continue
            pair = (str(source["contract_id"]), str(target["contract_id"]))
            key = _composition_context_key(source, target, relation)
            if pair in constrained_pairs or key in history:
                continue
            values.append({
                "context_key": key, "source_contract_id": pair[0], "target_contract_id": pair[1],
                "shared_interface_signals": relation["shared_interface_signals"],
                "execution_context_status": relation["execution_context_status"],
                "source": source, "target": target,
            })
    return sorted(
        values,
        key=lambda item: (-len(item["shared_interface_signals"]),
                          -int(item["source"].get("readiness_level", 0)),
                          -int(item["target"].get("readiness_level", 0)),
                          item["source_contract_id"], item["target_contract_id"]),
    )


def _pair_composition_context(spec_lines: list[dict[str, Any]], item: dict[str, Any]) -> dict[str, Any]:
    """Give the LLM one SPEC-grounded, interface-proven directional context."""

    source, target = item["source"], item["target"]
    return {
        "schema": "feedback-interface-pair-composition-context.v1",
        "whole_design_rtl_supplied": False,
        "incremental_scope": {
            "selection": "unvisited strict Local Contract pair with typed RTL output-to-input/state edge",
            "context_key": item["context_key"],
            "source_contract_id": source["contract_id"], "target_contract_id": target["contract_id"],
            "shared_interface_signals": item["shared_interface_signals"],
            "execution_context_status": item["execution_context_status"],
        },
        "spec_lines": deepcopy(spec_lines),
        "allowed_relation_types": ["CAUSALITY", "ORDERING", "DATA_TRANSFER", "STATE_CONTROL"],
        "allowed_contract_ids": [source["contract_id"], target["contract_id"]],
        "contracts": [_compact_contract(source), _compact_contract(target)],
        "prohibited_outputs": ["SVA", "SystemVerilog", "assert property", "assume property"],
    }


def _rename_properties(
    properties: list[PropertyIR], metadata: dict[str, dict[str, Any]], *, round_index: int, kind: str,
) -> tuple[list[PropertyIR], dict[str, dict[str, Any]]]:
    renamed: dict[str, dict[str, Any]] = {}
    for index, prop in enumerate(properties, 1):
        old = prop.property_id
        prop.property_id = f"feedback_r{round_index:02d}_{kind}_{index:04d}"
        prop.iteration_added = round_index
        record = deepcopy(metadata.get(old, {}))
        record.update(property_id=prop.property_id, original_property_id=old, iteration_added=round_index)
        renamed[prop.property_id] = record
    return properties, renamed


def _deduplicate_new(
    properties: list[PropertyIR], *, active: list[PropertyIR], history: dict[str, Any],
) -> tuple[list[PropertyIR], list[dict[str, Any]]]:
    active_keys = {_property_key(item) for item in active}
    selected: list[PropertyIR] = []
    rejected: list[dict[str, Any]] = []
    for prop in properties:
        signature = _property_key(prop)
        if signature in active_keys:
            rejected.append({"property_id": prop.property_id, "signature": signature, "reason": "EXACT_ACTIVE_SVA_DUPLICATE"})
            continue
        prior = history.get(signature)
        if prior and prior.get("terminal", False):
            rejected.append({
                "property_id": prop.property_id, "signature": signature,
                "reason": "IDENTICAL_PRIOR_TERMINAL_OUTCOME", "prior": prior,
            })
            continue
        active_keys.add(signature)
        selected.append(prop)
    return selected, rejected


def _record_probe_history(
    history: dict[str, Any], properties: list[PropertyIR], result: FormalRunResult | None,
    *, round_index: int, kind: str,
) -> None:
    by_id = {item.property_id: item for item in (result.results if result else [])}
    for prop in properties:
        item = by_id.get(prop.property_id)
        if item is None:
            status, terminal = "NOT_EVALUATED", False
        elif item.result == "FAIL":
            status, terminal = "FAILED_CEX", True
        elif item.result == "TIMEOUT_ACCEPTED":
            # It is an accepted budget outcome in the user-facing metrics, but
            # lacks the strict PASS+NON_VACUOUS evidence required to expand a
            # Contract or cause new cross-Region SVA.
            status, terminal = "TIMEOUT_ACCEPTED_NOT_STRICT", True
        elif item.result == "PASS" and item.vacuity == "VACUOUS":
            status, terminal = "VACUOUS", True
        elif item.result == "PASS" and item.vacuity == "NON_VACUOUS":
            status, terminal = "PASS_NON_VACUOUS", False
        else:
            status, terminal = f"{item.result}_{item.vacuity or 'NO_VACUITY'}", False
        history[_property_key(prop)] = {
            "round": round_index, "kind": kind, "property_id": prop.property_id,
            "status": status, "terminal": terminal,
            **_policy_fields(item),
        }


def _policy_fields(item: FormalPropertyResult | None) -> dict[str, Any]:
    """Record raw tool outcome separately from the configured budget policy."""

    result = item.result if item is not None else "NOT_EVALUATED"
    vacuity = item.vacuity if item is not None else "NOT_EVALUATED"
    if result == "PASS":
        policy_classification, accepted = "TOOL_PASS", True
    elif result == "TIMEOUT_ACCEPTED":
        # JasperGold's parser emits this only for an elaborated target that
        # exhausted the configured budget.  Req12 reports it as policy-accepted
        # at the configured 600 s limit, while keeping it out of strict
        # Contract growth because it is not proof+non-vacuity evidence.
        policy_classification, accepted = "TIMEOUT_ACCEPTED_AS_PROVEN_POLICY", True
    elif result == "FAIL":
        policy_classification, accepted = "FAILED_CEX", False
    else:
        policy_classification, accepted = f"{result}_NOT_ACCEPTED", False
    return {
        "tool_result": result, "tool_vacuity": vacuity,
        "policy_classification": policy_classification,
        "policy_accepted_proven": accepted,
    }


def _record_strict_rejections(
    history: dict[str, Any], attempted: list[PropertyIR], strict: list[PropertyIR],
    *, round_index: int, kind: str,
) -> None:
    """Do not re-probe a body rejected by the exact strict portfolio gate."""

    retained = {item.property_id for item in strict}
    for prop in attempted:
        if prop.property_id in retained:
            continue
        key = _property_key(prop)
        prior = history.get(key, {})
        if prior.get("status") == "PASS_NON_VACUOUS":
            history[key] = {
                "round": round_index, "kind": kind, "property_id": prop.property_id,
                "status": "STRICT_PORTFOLIO_REJECTED", "terminal": True,
                **{key: prior[key] for key in ("tool_result", "tool_vacuity", "policy_classification", "policy_accepted_proven")
                   if key in prior},
            }


def _seed_initial_attempt_history(initial_root: Path, active_properties: list[PropertyIR]) -> dict[str, Any]:
    """Do not re-run a rejected initial candidate merely because feedback sees it again."""

    active_ids = {item.property_id for item in active_properties}
    history: dict[str, Any] = {}
    sources = (
        (initial_root / "local_candidates.json", initial_root / "formal" / "rtl_only_probe" / "formal" / "formal_results.json", "INITIAL_LOCAL"),
        (initial_root / "local_candidates.json", initial_root / "formal" / "rtl_only" / "formal" / "formal_results.json", "INITIAL_LOCAL_STRICT"),
        (initial_root / "local_candidates.json", initial_root / "formal" / "spec_plus_rtl_local" / "formal" / "formal_results.json", "INITIAL_SPEC"),
        (initial_root / "composition_properties.json", initial_root / "formal" / "composition_probe" / "formal" / "formal_results.json", "INITIAL_COMPOSITION"),
    )
    for props_path, results_path, kind in sources:
        if not props_path.is_file() or not results_path.is_file():
            continue
        candidates = properties_from_dict(_read(props_path, []))
        result = _result_doc(results_path)
        by_id = {item.property_id: item for item in result.results}
        for prop in candidates:
            if prop.property_id in active_ids:
                continue
            item = by_id.get(prop.property_id)
            if item is None:
                # A candidate omitted by the initial probe is not a valid
                # fresh feedback candidate; retain the omission as terminal.
                status = "INITIAL_NOT_EVALUATED_OR_NOT_SELECTED"
            elif item.result == "FAIL":
                status = "INITIAL_FAILED_CEX"
            elif item.result == "TIMEOUT_ACCEPTED":
                status = "INITIAL_TIMEOUT_ACCEPTED_NOT_STRICT"
            elif item.result == "PASS" and item.vacuity == "VACUOUS":
                status = "INITIAL_VACUOUS"
            else:
                status = "INITIAL_NOT_IN_EXACT_TRUSTED_PORTFOLIO"
            history[_property_key(prop)] = {
                "round": 0, "kind": kind, "property_id": prop.property_id,
                "status": status, "terminal": True,
                **_policy_fields(item),
            }
    # A candidate absent from every archived initial probe was not part of the
    # exact trusted portfolio either.  Recording that omission closes the
    # retry loophole without claiming it was formally disproved.
    for path, _result_path, kind in sources:
        if not path.is_file():
            continue
        for prop in properties_from_dict(_read(path, [])):
            if prop.property_id not in active_ids:
                history.setdefault(_property_key(prop), {
                    "round": 0, "kind": kind, "property_id": prop.property_id,
                    "status": "INITIAL_NOT_EVALUATED_OR_NOT_SELECTED", "terminal": True,
                    **_policy_fields(None),
                })
    return history


def _seed_initial_composition_context_history(initial_root: Path, constraints: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Carry exact compact-context outcomes into feedback's no-retry queue.

    Legacy initial runs have only relation endpoints, which remain useful as a
    coarse compatibility marker.  Balanced initial runs additionally persist
    exact event-context keys, including rejected/empty calls; those keys must
    be retained so feedback does not pay for the same LLM failure again.
    """

    history = {
        _sha({"source": item.get("source_contract_id"), "target": item.get("target_contract_id")}): {
            "round": 0, "status": "INITIAL_SPEC_CONSTRAINT", "source": item.get("source_contract_id"),
            "target": item.get("target_contract_id"), "kind": "LEGACY_CONTRACT_PAIR",
        }
        for item in constraints.get("constraints", [])
    }
    audit_paths = (
        initial_root / "composition_expansion" / "composition_context_audit.json",
        initial_root / "balanced_composition" / "composition_context_audit.json",
        initial_root / "composition_context_audit.json",
    )
    for path in audit_paths:
        audit = _read(path, {})
        if not isinstance(audit, dict):
            continue
        for call in audit.get("calls", []):
            if not isinstance(call, dict) or not call.get("context_key"):
                continue
            key = str(call["context_key"])
            history[key] = {
                "round": 0, "status": str(call.get("status", "INITIAL_CONTEXT_NOT_EVALUATED")),
                "source": "INITIAL_COMPACT_CONTEXT_AUDIT", "target": None,
                "kind": "EXACT_EVENT_CONTEXT", "audit_path": str(path),
            }
    return history


def _strict_probe(
    design: RTLDesign, properties: list[PropertyIR], top: str, root: Path, config: dict[str, Any], graph: dict[str, Any],
) -> tuple[list[PropertyIR], FormalRunResult | None, list[dict[str, Any]], FormalRunResult | None]:
    """Persist an isolated probe then establish strict, non-vacuous evidence.

    A timeout accepted by the reporting policy is deliberately *not* a
    strict-proof candidate.  It is therefore possible for a nonempty probe to
    yield an empty strict portfolio.  Invoking JasperGold on an assertion file
    containing only the generated comment produces ``no_properties`` rather
    than a proof result; that is a normal, auditable feedback outcome, not a
    tool failure and not a synthetic PASS.
    """

    if not properties:
        return [], None, [], None
    probe = _formal(design, properties, top, root / "probe", config, measure_proof_coverage=False)
    by_id = {item.property_id: item for item in probe.results}
    expected_ids = {item.property_id for item in properties}
    observed_ids = set(by_id)
    result_id_counts = Counter(item.property_id for item in probe.results)
    duplicate_ids = sorted(
        identifier for identifier, count in result_id_counts.items() if count > 1
    )
    missing_ids = sorted(expected_ids - observed_ids)
    extra_ids = sorted(observed_ids - expected_ids)
    invalid_results = sorted(
        item.property_id for item in probe.results
        if item.result in {"ERROR", "NOT_EVALUATED"}
    )
    if (
        probe.status in {"ERROR", "NOT_EVALUATED"}
        or missing_ids or extra_ids or duplicate_ids or invalid_results
    ):
        raise RuntimeError(
            "candidate probe did not complete an exact property portfolio: "
            f"status={probe.status}, missing={missing_ids[:8]}, extra={extra_ids[:8]}, "
            f"duplicate={duplicate_ids[:8]}, invalid={invalid_results[:8]}"
        )
    tool_pass = [
        prop for prop in properties
        if by_id.get(prop.property_id) is not None
        and by_id[prop.property_id].result == "PASS"
    ]
    possibly_strict = [
        prop for prop in tool_pass
        if by_id[prop.property_id].vacuity != "VACUOUS"
    ]

    def skip(reason: str, *, detail: str = "") -> tuple[
        list[PropertyIR], FormalRunResult, list[dict[str, Any]], None,
    ]:
        result_counts_by_status = Counter(
            f"{item.result}:{item.vacuity}" for item in probe.results
        )
        audit = [{
            "phase": "strict_skipped",
            "status": "SKIPPED_NO_STRICT_PORTFOLIO",
            "reason": reason,
            "detail": detail,
            "candidate_input": len(properties),
            "probe_results": len(probe.results),
            "tool_pass_candidates": len(tool_pass),
            "possibly_strict_candidates": len(possibly_strict),
            "probe_result_counts": dict(sorted(result_counts_by_status.items())),
            "property_ids": [item.property_id for item in properties],
            "policy": (
                "Probe artifacts are retained. TIMEOUT_ACCEPTED is never promoted "
                "to a strict PASS or used for Contract growth."
            ),
        }]
        strict_root = root / "strict"
        dump_json(strict_root / "stabilization" / "audit.json", audit)
        dump_json(strict_root / "skipped_no_strict_portfolio.json", audit[0])
        return [], probe, audit, None

    if not tool_pass:
        return skip("NO_TOOL_PASS_CANDIDATES")
    if not possibly_strict:
        return skip("ALL_TOOL_PASS_CANDIDATES_VACUOUS")

    strict, exact, audit = _stable_formal(
        design, [], properties, top, root / "strict", config,
        candidate_probe=probe, graph=graph, allow_empty=True,
    )
    return strict, probe, audit, exact


def _coverage_item_source(item: CoverItem) -> dict[str, Any]:
    """Literal RTL identity retained alongside a stable proof-core item ID."""

    return {
        "file": item.file, "line_start": item.line_start, "column_start": item.column_start,
        "line_end": item.line_end, "column_end": item.column_end,
        "cover_item_type": item.cover_item_type, "module": item.module,
        "instance": item.instance, "description": item.description, "expression": item.expression,
    }


def _coverage_identity(items: list[CoverItem]) -> dict[str, dict[str, Any]]:
    """Stable item ID -> source identity; reject an ambiguous export eagerly."""

    result: dict[str, dict[str, Any]] = {}
    for item in items:
        item_id = stable_cover_item_id(item)
        source = _coverage_item_source(item)
        if item_id in result and result[item_id] != source:
            raise RuntimeError(f"ambiguous stable proof-core item identity: {item_id}")
        result[item_id] = source
    return result


def _coverage_delta(previous: list[CoverItem], current: list[CoverItem]) -> dict[str, Any]:
    old, new = {stable_cover_item_id(item) for item in previous if item.status == "covered_and_checked"}, {
        stable_cover_item_id(item) for item in current if item.status == "covered_and_checked"
    }
    old_by_id = {stable_cover_item_id(item): item for item in previous}
    new_by_id = {stable_cover_item_id(item): item for item in current}
    old_universe, new_universe = set(old_by_id), set(new_by_id)
    old_sources, new_sources = _coverage_identity(previous), _coverage_identity(current)
    transitions = [
        {
            "rtl_item_id": item_id,
            "before_status": old_by_id[item_id].status,
            "after_status": new_by_id[item_id].status,
            "before_formal_status": old_by_id[item_id].formal_status,
            "after_formal_status": new_by_id[item_id].formal_status,
            "before_checker_status": old_by_id[item_id].checker_status,
            "after_checker_status": new_by_id[item_id].checker_status,
            "source": new_sources[item_id],
        }
        for item_id in sorted(old_universe & new_universe)
        if old_by_id[item_id].status != new_by_id[item_id].status
        or old_by_id[item_id].formal_status != new_by_id[item_id].formal_status
        or old_by_id[item_id].checker_status != new_by_id[item_id].checker_status
    ]
    transition_counts = Counter(
        f"{item['before_status']}->{item['after_status']}" for item in transitions
    )
    before, after = coverage_by_type(previous)["all"], coverage_by_type(current)["all"]
    return {
        "new_checked_items": len(new - old), "lost_checked_items": len(old - new),
        "net_checked_items": len(new) - len(old),
        "item_universe_constant": old_universe == new_universe,
        "source_identity_constant": old_sources == new_sources,
        "item_ids_added": sorted(new_universe - old_universe),
        "item_ids_removed": sorted(old_universe - new_universe),
        "status_transitions": transitions,
        "status_transition_counts": dict(sorted(transition_counts.items())),
        "effective_denominator_transition": {
            "before": before["effective_reachable_denominator"],
            "after": after["effective_reachable_denominator"],
            "changed": before["effective_reachable_denominator"] != after["effective_reachable_denominator"],
            "accounting": "reported from exact item-status transitions; never treated as a coverage gain by itself",
        },
        "effective_denominator_before": before["effective_reachable_denominator"],
        "effective_denominator_after": after["effective_reachable_denominator"],
        "effective_denominator_constant": before["effective_reachable_denominator"] == after["effective_reachable_denominator"],
        "effective_coverage_before_percent": before["effective_percent"],
        "effective_coverage_after_percent": after["effective_percent"],
        "effective_coverage_delta_percentage_points": round(after["effective_percent"] - before["effective_percent"], 2),
        "checked_gain_accounting": "new/lost/net are computed only from stable IDs with status covered_and_checked; denominator changes without a checked-status transition contribute zero",
    }


def _rtl_coverage_identity_is_stable(
    gain: dict[str, Any], current_sources: dict[str, dict[str, Any]],
    initial_sources: dict[str, dict[str, Any]],
) -> bool:
    """The hard coverage gate: exact RTL item IDs/sources, never status class."""

    return bool(
        gain.get("item_universe_constant")
        and gain.get("source_identity_constant")
        and current_sources == initial_sources
    )


def _scope_modules(target: dict[str, Any], design_map: dict[str, Any]) -> set[str]:
    reachable = {str(item["module"]) for item in design_map.get("instances", []) if item.get("module")} or {str(target["top"])}
    return reachable if target.get("validation_scope") == "full_cpu" else {str(target["top"])}


def _assignment_count(graph: dict[str, Any]) -> int:
    return sum(item.get("kind") == "assignment" for item in graph.get("nodes", []))


def _pending_local_entries(state: dict[str, Any]) -> list[dict[str, Any]]:
    """Hydrate persisted, compiled-but-not-yet-probed Local SVA work items."""

    entries = []
    for raw in state.get("pending_local_candidates", []):
        item = deepcopy(raw)
        prop = item.get("property")
        if isinstance(prop, dict):
            item["property"] = properties_from_dict([prop])[0]
        if isinstance(item.get("property"), PropertyIR):
            entries.append(item)
    return entries


def _record_generation(
    state: dict[str, Any], properties: list[PropertyIR], *, round_index: int, kind: str,
) -> None:
    history = state.setdefault("generation_history", {})
    for prop in properties:
        history.setdefault(_property_key(prop), {
            "round_compiled": round_index, "kind": kind, "property_id": prop.property_id,
            "target_module": prop.target_module, "family": prop.family,
        })


def _pending_motifs(state: dict[str, Any]) -> list[dict[str, Any]]:
    return [deepcopy(item) for item in state.get("pending_region_motifs", []) if isinstance(item, dict)]


def _region_worklist(
    state: dict[str, Any], motifs: list[dict[str, Any]], *, budget: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    """Merge newly localised motifs with deferred work without starvation."""

    merged: dict[str, dict[str, Any]] = {}
    for motif in [*_pending_motifs(state), *motifs]:
        key = _region_key(motif)
        if key not in state.get("region_history", {}):
            merged.setdefault(key, motif)
    ordered = sorted(merged.values(), key=lambda item: (-float(item.get("selection_score", 0.0)), item["region_id"]))
    selected = ordered[:max(0, budget)]
    deferred = ordered[len(selected):]
    rejected = [
        {"region_id": item["region_id"], "reason": "PREVIOUS_REGION_MOTIF"}
        for item in motifs if _region_key(item) in state.get("region_history", {})
    ]
    return selected, deferred, rejected


def _exact_universe(items: list[CoverItem]) -> set[str]:
    return {stable_cover_item_id(item) for item in items}


def _composition_context_budget(state: dict[str, Any], feedback: dict[str, Any], rounds: int) -> dict[str, Any]:
    """Size the semantic-search work budget from the initial Local inventory.

    The calculation is a resource budget for SPEC+typed-interface contexts,
    not a target number of accepted SVA.  A context may yield no relation or
    several fixed-template candidates; every candidate still faces strict
    Formal proof.  The cap protects long designs from an unbounded LLM batch.
    """

    generated = list(state.get("generation_history", {}).values())
    initial_local = sum(
        item.get("kind") == "LOCAL" and int(item.get("round_compiled", 0)) == 0
        for item in generated
    )
    desired = float(feedback.get("desired_composition_fraction", 0.20))
    cap = max(0, int(feedback.get("composition_contexts_per_round", 4)))
    floor = max(0, int(feedback.get("composition_min_contexts_per_round", 4)))
    adaptive = bool(feedback.get("composition_size_adaptive_budget", True))
    required_total = 0
    if 0.0 < desired < 1.0 and rounds > 0:
        required_total = ceil(initial_local * desired / (1.0 - desired))
    adaptive_budget = ceil(required_total / rounds) if rounds else 0
    requested = max(floor, adaptive_budget) if adaptive else floor
    return {
        "initial_generated_local_sva": initial_local,
        "desired_composition_fraction": desired,
        "contexts_required_for_desired_ratio_if_one_property_per_context": required_total,
        "adaptive_contexts_per_round": adaptive_budget,
        "min_contexts_per_round": floor,
        "cap_contexts_per_round": cap,
        "configured_adaptive": adaptive,
        "effective_contexts_per_round": min(cap, requested),
        "policy": "resource budget only, not a target number of accepted assertions; no assertion-count or acceptance quota",
    }


def _generated_policy_summary(state: dict[str, Any]) -> dict[str, Any]:
    """Outcome accounting over every unique compiled SVA, including rejects."""

    generated = state.get("generation_history", {})
    attempts = state.get("attempt_history", {})
    rows = [(key, value, attempts.get(key, {})) for key, value in generated.items()]
    tool_counts = Counter(str(attempt.get("tool_result", "NOT_EVALUATED")) for _, _, attempt in rows)
    accepted = [key for key, _generated, attempt in rows if attempt.get("policy_accepted_proven", False)]
    failures = [
        {"property_id": generated[key].get("property_id"), "signature": key,
         "status": attempt.get("status"), "tool_result": attempt.get("tool_result")}
        for key, _generated, attempt in rows if attempt.get("tool_result") == "FAIL"
    ]
    total = len(rows)
    return {
        "unique_generated_sva": total,
        "tool_results": dict(sorted(tool_counts.items())),
        "tool_pass": tool_counts["PASS"],
        "timeout_accepted": tool_counts["TIMEOUT_ACCEPTED"],
        "counterexamples_retained": len(failures),
        "counterexample_records": failures,
        "policy_accepted_proven": len(accepted),
        "policy_accepted_proven_rate_percent": round(100.0 * len(accepted) / total, 2) if total else 0.0,
        "denominator": "all unique generated exact-SVA bodies, including failed, vacuous, timeout, and not-evaluated candidates",
        "policy": "PASS or TIMEOUT_ACCEPTED is accepted for the configured Formal time-budget metric; strict Contract growth remains PASS+NON_VACUOUS only.",
    }


def _persist_state(root: Path, state: dict[str, Any]) -> None:
    dump_json(root / "state.json", state)
    dump_json(root / "active_properties.json", state["properties"])
    dump_json(root / "active_regions.json", {"regions": state["regions"]})
    dump_json(root / "active_local_contracts.json", {"contracts": state["contracts"]})
    dump_json(root / "active_constraints.json", state["constraints"])


def _fail_round(round_root: Path, index: int, reason: str, **details: Any) -> None:
    """Leave an explicit failure artifact; never present an invalid run as COMPLETE."""

    record = {"schema": SCHEMA, "round": index, "status": "FAILED", "reason": reason, **details}
    dump_json(round_root / "round_failure.json", record)
    dump_json(round_root / "round_status.json", record)
    raise RuntimeError(f"Req12 round {index} failed integrity check: {reason}")


def _state_from_initial(initial_root: Path, target: dict[str, Any], design: RTLDesign, graph: dict[str, Any]) -> tuple[dict[str, Any], list[CoverItem], FormalRunResult, Path]:
    properties, result, items, formal_root = _require_initial_portfolio(initial_root)
    initial_summary = _read(initial_root / "design_flow_design_summary.json", {})
    if not initial_summary:
        raise RuntimeError("initial run lacks design_flow_design_summary.json")
    if initial_summary.get("design_id") != target.get("design_id"):
        raise RuntimeError("initial result design_id does not match feedback target")
    if initial_summary.get("source_digest") != design.source_digest:
        raise RuntimeError("initial RTL digest does not match feedback RTL inputs")
    regions = _read(initial_root / "regions.json", {}).get("regions", [])
    if not regions:
        raise RuntimeError("initial_root lacks Region inventory")
    contracts = _read(initial_root / "local_contracts.json", {}).get("contracts", [])
    if not contracts:
        # This is deterministic reconstruction, not an LLM replacement.
        contracts = build_local_contracts(
            {"regions": regions}, [item for item in properties if not _is_composite(item)],
            _metadata_for(properties), graph, design,
        )["contracts"]
    constraints = _read(initial_root / "partial_order_constraints.json", {"constraints": [], "lifecycle_chains": []})
    constraints = _active_constraints(constraints, contracts)
    previous_graph = _read(initial_root / "contract_graph.json", {})
    if not previous_graph:
        previous_graph = build_contract_graph({"contracts": contracts}, constraints)
    metadata = _initial_metadata(initial_root, properties)
    initial_attempts = _seed_initial_attempt_history(initial_root, properties)
    composition_history = {
        _sha({"source": item.get("source_contract_id"), "target": item.get("target_contract_id")}): {
            "round": 0, "status": "INITIAL_SPEC_CONSTRAINT",
        }
        for item in constraints.get("constraints", [])
    }
    initial_generated: list[PropertyIR] = []
    for path in (initial_root / "local_candidates.json", initial_root / "composition_properties.json"):
        if path.is_file():
            initial_generated.extend(properties_from_dict(_read(path, [])))
    generation_history: dict[str, dict[str, Any]] = {}
    for item in initial_generated or properties:
        generation_history.setdefault(_property_key(item), {
            "round_compiled": 0,
            "kind": "COMPOSITION" if _is_composite(item) else "LOCAL",
            "property_id": item.property_id, "target_module": item.target_module, "family": item.family,
        })
    return ({
        "schema": SCHEMA, "design_id": str(target["design_id"]), "round": 0,
        "properties": properties, "regions": regions, "contracts": contracts,
        "constraints": constraints, "contract_graph": previous_graph,
        "property_metadata": metadata, "attempt_history": initial_attempts,
        "region_history": {_region_key(item): {"round": 0, "status": "INITIAL"} for item in regions},
        "initial_coverage_universe": sorted(stable_cover_item_id(item) for item in items),
        "initial_coverage_sources": _coverage_identity(items),
        "pending_region_motifs": [], "pending_extension_regions": {}, "pending_local_candidates": [],
        "composition_context_history": composition_history,
        "generation_history": generation_history,
    }, items, result, formal_root)


def _json_state(state: dict[str, Any]) -> dict[str, Any]:
    return {
        **{key: deepcopy(value) for key, value in state.items()
           if key not in {"properties"}},
        "properties": [deepcopy(prop) for prop in state["properties"]],
    }


def _load_completed_round(round_root: Path) -> dict[str, Any]:
    raw = _read(round_root / "state.json")
    if not raw or raw.get("schema") != SCHEMA:
        raise RuntimeError(f"completed round has no valid state: {round_root}")
    raw["properties"] = properties_from_dict(raw.get("properties", []))
    return raw


def _formal_items(round_root: Path) -> tuple[list[CoverItem], FormalRunResult]:
    formal = round_root / "formal" / "cumulative" / "formal"
    return parse_coverage_items(formal / "coverage_items.tsv"), _result_doc(formal / "formal_results.json")


def run_feedback(
    target: dict[str, Any], cfg: dict[str, Any], initial_root: str | Path,
    output_root: str | Path, rounds: int = 10, *,
    checkpoint_root: str | Path | None = None, checkpoint_round: int = 0,
) -> dict[str, Any]:
    """Run or resume exactly ``rounds`` feedback iterations for one design.

    ``initial_root`` is the direct per-design directory produced by the
    completed initial Local+Composition run; ``output_root`` is the direct
    feedback directory.  Every completed round stores enough state to resume
    without recomputing a past Formal run or retrying an identical failed SVA.
    """

    if rounds < 1:
        raise ValueError("rounds must be positive")
    initial_root, output_root = Path(initial_root).resolve(), Path(output_root).resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    req = cfg.get("design_flow", {})
    feedback = cfg.get("feedback", {})
    files = [str(_resolve(item)) for item in target.get("rtl_files", [])]
    include_dirs = [str(_resolve(item)) for item in target.get("include_dirs", [])]
    design = parse_rtl(files, include_dirs=include_dirs)
    graph = build_semantic_graph(design)
    design_map = _read(initial_root / "design_map.json") or build_hierarchical_design_map(
        design, graph, str(target["top"]), include_dirs=include_dirs,
    )
    scope_modules = _scope_modules(target, design_map)
    reset_asserted = f"!{target['reset']}" if target.get("reset_active_low", True) else str(target["reset"])
    local_config = _formal_config(cfg, target)
    selected_spec = _read(initial_root / "spec" / "selected_evidence.json", [])
    if not isinstance(selected_spec, list):
        raise RuntimeError("initial selected SPEC evidence is malformed")

    initial_formal_for_manifest = _initial_formal_root(initial_root)
    req_cfg = {key: deepcopy(value) for key, value in req.items() if key != "designs"}
    initial_identity = {
        "trusted_properties_sha256": _file_sha(initial_root / "final" / "trusted_properties.json"),
        "rendered_sva_sha256": _file_sha(initial_formal_for_manifest / "assertions.sv"),
        "formal_results_sha256": _file_sha(initial_formal_for_manifest / "formal" / "formal_results.json"),
        "coverage_items_sha256": _file_sha(initial_formal_for_manifest / "formal" / "coverage_items.tsv"),
        "formal_input_identity_sha256": _file_sha(initial_formal_for_manifest / "formal" / "input_identity.json"),
        "rtl_structure_sha256": _file_sha(initial_root / "rtl_structure.json"),
        "design_map_sha256": _file_sha(initial_root / "design_map.json"),
        "selected_spec_sha256": _file_sha(initial_root / "spec" / "selected_evidence.json"),
        "initial_manifest_sha256": _file_sha(initial_root / "feedback_initial_manifest.json"),
        "summary_sha256": _file_sha(initial_root / "design_flow_design_summary.json"),
    }
    manifest = {
        "schema": SCHEMA, "design_id": target["design_id"], "rounds": rounds,
        "initial_root": str(initial_root), "source_digest": design.source_digest,
        "target_sha256": _sha(target),
        "config_sha256": _sha({"formal": cfg.get("formal", {}), "llm": cfg.get("llm", {}), "feedback": feedback, "design_flow": req_cfg}),
        "algorithm_sha256": _sha(_algorithm_identity()),
        "initial_artifact_identity": initial_identity,
        "initial_portfolio": str(initial_root / "final" / "trusted_properties.json"),
        "initial_is_full_local_plus_composition": True,
    }
    checkpoint = None
    if checkpoint_root is not None:
        if not 0 < checkpoint_round < rounds:
            raise ValueError("checkpoint_round must be between zero and requested final round")
        checkpoint = Path(checkpoint_root).resolve()
        if checkpoint == output_root:
            raise ValueError("checkpoint fork requires a distinct output root")
        old_manifest = _read(checkpoint / "manifest.json", {})
        for key in ("design_id", "source_digest", "target_sha256", "initial_root", "initial_artifact_identity"):
            if old_manifest.get(key) != manifest[key]:
                raise RuntimeError(f"Checkpoint input mismatch: {key}")
        checkpoint_files = {}
        for previous_round in range(1, checkpoint_round + 1):
            directory = checkpoint / "rounds" / f"round_{previous_round:02d}"
            summary = _read(directory / "round_summary.json", {})
            if summary.get("status") != "COMPLETE" or summary.get("round") != previous_round:
                raise RuntimeError(f"Incomplete checkpoint prefix: {directory}")
            for name in ("round_summary.json", "state.json", "formal/cumulative/formal/formal_results.json", "formal/cumulative/formal/coverage_items.tsv", "composition/generated_properties.json"):
                path = directory / name
                if not path.is_file():
                    raise RuntimeError(f"Missing checkpoint evidence: {path}")
                checkpoint_files[str(path)] = _file_sha(path)
        manifest["checkpoint"] = {"root": str(checkpoint), "round": checkpoint_round,
                                  "files_sha256": checkpoint_files,
                                  "inherited_algorithm_sha256": old_manifest.get("algorithm_sha256"),
                                  "comparison": "inherited prefix; only suffix uses revised algorithm"}
    elif checkpoint_round:
        raise ValueError("checkpoint_round requires checkpoint_root")
    prior_manifest = _read(output_root / "manifest.json")
    if prior_manifest:
        for key in (
            "design_id", "source_digest", "target_sha256", "config_sha256", "initial_root",
            "algorithm_sha256", "initial_artifact_identity", "checkpoint",
        ):
            if prior_manifest.get(key) != manifest.get(key):
                raise RuntimeError(f"Req12 feedback resume mismatch for {key}; use a clean output root")
    else:
        dump_json(output_root / "manifest.json", manifest)

    state, previous_items, initial_result, initial_formal_root = _state_from_initial(
        initial_root, target, design, graph,
    )
    rounds_root = output_root / "rounds"
    if checkpoint is not None:
        checkpoint_directory = checkpoint / "rounds" / f"round_{checkpoint_round:02d}"
        state = _load_completed_round(checkpoint_directory)
        if state.get("round") != checkpoint_round or state.get("design_id") != target["design_id"]:
            raise RuntimeError("Checkpoint state identity mismatch")
        previous_items, _ = _formal_items(checkpoint_directory)
        # Older state snapshots omitted feedback Composite generation entries.
        # Recover only from saved, hash-audited selected records, not counts.
        for previous_round in range(1, checkpoint_round + 1):
            directory = checkpoint / "rounds" / f"round_{previous_round:02d}"
            saved = _read(directory / "composition" / "generated_properties.json", [])
            _record_generation(state, properties_from_dict(saved), round_index=previous_round, kind="COMPOSITION")
    for index in range(checkpoint_round + 1, rounds + 1):
        round_root = rounds_root / f"round_{index:02d}"
        summary_path = round_root / "round_summary.json"
        if summary_path.is_file() and _read(summary_path).get("status") == "COMPLETE":
            state = _load_completed_round(round_root)
            previous_items, _previous_result = _formal_items(round_root)
            continue

        round_root.mkdir(parents=True, exist_ok=True)
        dump_json(round_root / "round_status.json", {"round": index, "status": "RUNNING"})
        gap_records = localize_refinement_gaps(previous_items, graph, state["regions"], design_map=design_map)
        dump_json(round_root / "gap_mapping.json", gap_records)

        # Enumerate all currently eligible bounded producer-family motifs
        # before applying the per-round LLM/Formal work budget.  Asking the
        # matcher for only the first six/forty-eight would permanently starve
        # later motifs after the first batch was recorded in history.
        motifs = discover_refinement_candidates(
            gap_records, graph, state["regions"],
            max_regions=max(1, _assignment_count(graph)),
            max_assignments=int(req.get("refinement_max_assignments", 16)),
            depth=int(req.get("refinement_graph_depth", 2)),
        )
        new_motifs, deferred_motifs, motif_rejections = _region_worklist(
            state, motifs,
            budget=int(feedback.get("region_work_budget", req.get("refinement_region_limit", 48))),
        )
        dump_json(round_root / "refinement_candidates.json", motifs)
        dump_json(round_root / "refinement_candidate_rejections.json", motif_rejections)
        dump_json(round_root / "deferred_region_motifs.json", deferred_motifs)

        extension_regions: list[dict[str, Any]] = []
        llm_region_audit: list[dict[str, Any]] = []
        if new_motifs:
            client = DeepSeekClient(_llm_config(cfg["llm"]))
            # Interpret one bounded motif per call so a malformed LLM response
            # cannot discard all unrelated coverage evidence in this round.
            for motif in new_motifs:
                try:
                    extensions, audit = interpret_refinements(
                        [motif], state["regions"], selected_spec, client,
                        round_root / "llm" / "regions" / motif["region_id"],
                        attempts=int(req.get("llm_validation_attempts", 4)),
                    )
                    extension_regions.extend(extensions)
                    llm_region_audit.append({"region_id": motif["region_id"], "status": "VALIDATED", "audit": audit})
                except LLMUnavailableError as exc:
                    record = {
                        "region_id": motif["region_id"], "status": "INTERRUPTED_EXTERNAL_SERVICE",
                        "error": f"{type(exc).__name__}: {exc}",
                    }
                    llm_region_audit.append(record)
                    # Do not put this motif in region_history: no semantic
                    # judgement was made, so a later authenticated run may
                    # legitimately revisit it.
                    dump_json(round_root / "llm_region_interpretation.json", llm_region_audit)
                    dump_json(round_root / "external_service_failure.json", {
                        "schema": SCHEMA, "round": index, "status": "INTERRUPTED_EXTERNAL_SERVICE",
                        "stage": "REGION_INTERPRETATION", **record,
                    })
                    _fail_round(
                        round_root, index, "LLM_UNAVAILABLE_EXTERNAL_SERVICE",
                        stage="REGION_INTERPRETATION", error=record["error"],
                    )
                except Exception as exc:  # a failed interpretation is visible, never guessed
                    llm_region_audit.append({"region_id": motif["region_id"], "status": "REJECTED", "error": f"{type(exc).__name__}: {exc}"})
                finally:
                    if llm_region_audit[-1]["status"] != "INTERRUPTED_EXTERNAL_SERVICE":
                        state["region_history"][_region_key(motif)] = {"round": index, "status": llm_region_audit[-1]["status"]}
        dump_json(round_root / "llm_region_interpretation.json", llm_region_audit)
        existing_region_ids = {item["region_id"] for item in state["regions"]}
        extension_regions = [item for item in extension_regions if item["region_id"] not in existing_region_ids]
        # A Region inferred this round is not promoted merely because its LLM
        # interpretation was valid.  Preserve it only while one of its own
        # compiled Local obligations is waiting in the bounded Formal queue.
        # This prevents a deferred Local SVA from losing its Region boundary.
        available_extensions = {
            str(key): deepcopy(value)
            for key, value in state.get("pending_extension_regions", {}).items()
            if isinstance(value, dict) and str(key) not in existing_region_ids
        }
        available_extensions.update({item["region_id"]: deepcopy(item) for item in extension_regions})

        # Rebuild a deterministic candidate pool over current Regions.  This is
        # static RTL analysis only; it neither re-parses the original pipeline
        # nor invents a Contract from an LLM answer.
        pool, pool_rejections, pool_summary = build_property_candidate_pool(
            design, graph, design_map, {"regions": state["regions"] + extension_regions},
            {"reset": target["reset"], "reset_active_low": bool(target.get("reset_active_low", True))},
        )
        refinement_props, refinement_metadata = compile_refinement_properties(
            pool, extension_regions, design, reset_asserted, round_root / "local" / "refinement",
            deduplicate=bool(feedback.get("deduplicate_sva", True)),
        ) if extension_regions else ([], {})

        # Existing-region Contract gaps are a different legitimate Local delta.
        # Like Region motifs, discover all typed B-gap assignment rows first;
        # history filtering and the explicit work queue decide this round's
        # Formal work.  A fixed first-five slice would never reach later rows.
        contract_rows = select_contract_gap_assignments(
            gap_records, graph, focus_modules=sorted(scope_modules),
            limit=max(1, _assignment_count(graph)),
        )
        contract_props = [
            property_from_assignment(node, region_ids[0], f"contract_gap_{serial:04d}", index,
                                     reset_asserted=reset_asserted)
            for serial, (node, region_ids, _cids) in enumerate(contract_rows, 1) if region_ids
        ]
        compiled_local_props = refinement_props + contract_props
        compiled_local_metadata = {**refinement_metadata, **_metadata_for(contract_props)}
        compiled_local_props, compiled_local_metadata = _rename_properties(
            compiled_local_props, compiled_local_metadata, round_index=index, kind="local",
        )
        compiled_local_props, local_exact_rejections = _deduplicate_new(
            compiled_local_props, active=state["properties"], history=state["attempt_history"],
        ) if feedback.get("deduplicate_sva", True) else (compiled_local_props, [])
        compiled_local_props, local_render_rejections = _filter_renderable_properties(compiled_local_props, design)
        for prop in compiled_local_props:
            compiled_local_metadata.setdefault(prop.property_id, _metadata_for([prop])[prop.property_id])
        # A per-round Contract-gap *work* bound keeps one very large COI
        # family from consuming every Formal probe.  It is not a hidden
        # acceptance/ratio quota: rows beyond the bound remain unvisited and
        # are deterministically reconsidered after earlier rows become active
        # or terminal in subsequent rounds.
        contract_work_budget = max(0, int(feedback.get("contract_gap_work_budget", len(compiled_local_props))))
        selected_contract_work = 0
        bounded_compiled_props: list[PropertyIR] = []
        deferred_contract_work: list[dict[str, Any]] = []
        for prop in compiled_local_props:
            original = str(compiled_local_metadata.get(prop.property_id, {}).get("original_property_id", ""))
            if original.startswith("contract_gap_"):
                if selected_contract_work >= contract_work_budget:
                    deferred_contract_work.append({
                        "property_id": prop.property_id, "signature": _property_key(prop),
                        "reason": "CONTRACT_GAP_WORK_BUDGET", "original_property_id": original,
                    })
                    continue
                selected_contract_work += 1
            bounded_compiled_props.append(prop)
        compiled_local_props = bounded_compiled_props
        _record_generation(state, compiled_local_props, round_index=index, kind="LOCAL")
        pending_entries = _pending_local_entries(state)
        pending_signatures = {_property_key(item["property"]) for item in pending_entries}
        fresh_entries = []
        pending_duplicates = []
        for prop in compiled_local_props:
            signature = _property_key(prop)
            if feedback.get("deduplicate_sva", True) and signature in pending_signatures:
                pending_duplicates.append({"property_id": prop.property_id, "reason": "ALREADY_DEFERRED"})
                continue
            pending_signatures.add(signature)
            fresh_entries.append({
                "property": prop, "metadata": compiled_local_metadata[prop.property_id], "enqueued_round": index,
                "extension_region_id": prop.region_id if prop.region_id in {item["region_id"] for item in extension_regions} else None,
            })
        worklist = [*pending_entries, *fresh_entries]
        local_budget = int(feedback.get("local_property_work_budget", req.get("feedback_property_budget", 100000)))
        selected_entries = worklist[:max(0, local_budget)]
        deferred_local_entries = worklist[len(selected_entries):]
        if feedback.get("local_work_selection") == "current_gap":
            selected_entries, deferred_local_entries, selection_audit = select_current_gap_work(worklist, gap_records, local_budget)
            dump_json(round_root / "local" / "current_gap_selection.json", selection_audit)
        local_props = [item["property"] for item in selected_entries]
        local_metadata = {item["property"].property_id: item.get("metadata", {}) for item in selected_entries}
        dump_json(round_root / "local" / "candidate_pool_summary.json", pool_summary)
        dump_json(round_root / "local" / "candidate_pool_rejections.json", pool_rejections)
        dump_json(round_root / "local" / "all_contract_gap_rows.json", [
            {"node_id": node["id"], "region_ids": region_ids, "cover_item_ids": cids}
            for node, region_ids, cids in contract_rows
        ])
        dump_json(round_root / "local" / "compiled_properties.json", compiled_local_props)
        dump_json(round_root / "local" / "generated_properties.json", local_props)
        dump_json(round_root / "local" / "dedup_rejections.json", local_exact_rejections)
        dump_json(round_root / "local" / "render_rejections.json", local_render_rejections)
        dump_json(round_root / "local" / "pending_duplicate_rejections.json", pending_duplicates)
        dump_json(round_root / "local" / "deferred_contract_gap_work.json", deferred_contract_work)
        dump_json(round_root / "local" / "deferred_candidates.json", deferred_local_entries)

        strict_local, local_probe, local_stable_audit, _local_strict_result = _strict_probe(
            design, local_props, str(target["top"]), round_root / "formal" / "local", local_config, graph,
        )
        _record_probe_history(state["attempt_history"], local_props, local_probe, round_index=index, kind="LOCAL")
        _record_strict_rejections(
            state["attempt_history"], local_props, strict_local, round_index=index, kind="LOCAL",
        )

        # A discovered Region is promoted only when at least one of its own
        # Local obligations survives the strict gate.  Merely being adjacent to
        # an uncovered item must not create a readiness-1 Contract that can
        # later manufacture a composition edge.
        strict_local_region_ids = {item.region_id for item in strict_local}
        promoted_extensions = [
            item for region_id, item in available_extensions.items()
            if region_id in strict_local_region_ids
        ]
        candidate_regions = state["regions"] + promoted_extensions
        candidate_properties = state["properties"] + strict_local
        candidate_metadata = {**state["property_metadata"], **local_metadata}
        candidate_contracts_doc = build_local_contracts(
            {"regions": candidate_regions},
            [item for item in candidate_properties if not _is_composite(item)],
            candidate_metadata, graph, design,
        )
        candidate_contracts = candidate_contracts_doc["contracts"]
        old_contracts = {item["contract_id"]: _contract_fingerprint(item) for item in state["contracts"]}
        changed_contract_ids = {
            item["contract_id"] for item in candidate_contracts
            if old_contracts.get(item["contract_id"]) != _contract_fingerprint(item)
        }

        # SPEC relation extraction is a bounded *typed-interface queue*, not
        # all-pairs path enumeration.  It first admits Contract deltas, then
        # consumes unvisited strict-Local source->target contexts that have a
        # real same-module output-to-input/state edge.  The LLM sees only the
        # two Contract event summaries and supplied SPEC snippets; it returns
        # relation IR, never SVA.  This is the legitimate way feedback can
        # broaden cross-Region coverage even in a round with no new Local SVA.
        delta_constraints = {"constraints": [], "lifecycle_chains": []}
        composition_calls: list[dict[str, Any]] = []
        composition_contexts: list[dict[str, Any]] = []
        composition_budget = _composition_context_budget(state, feedback, rounds)
        max_contexts = composition_budget["effective_contexts_per_round"]
        changed_context_consumed = 0
        prompt = (PROJECT_ROOT / "llm" / "prompts" / "composition_constraints.txt").read_text(encoding="utf-8")
        client: DeepSeekClient | None = None
        compact_context_audit: dict[str, Any] | None = None
        compact_event_context_enabled = bool(feedback.get("composition_event_context_enabled", False))

        if compact_event_context_enabled:
            # The compact helper retains only signal-anchored original event
            # IDs and hard-bounds every prompt.  Feed it the round's adaptive
            # *context work budget* (not a desired number of Composite SVA),
            # and exclude already visited/interface-constrained pairs so an
            # identical failure cannot be sent to the LLM again.
            compact_cfg = deepcopy(cfg)
            compact_req = compact_cfg.setdefault("feedback", {})
            compact_req.update({
                "initial_composition_context_budget": max_contexts,
                "initial_composition_min_contexts": max_contexts,
                "runtime_excluded_composition_context_keys": sorted(state.get("composition_context_history", {})),
                "runtime_excluded_event_pairs": [
                    [item.get("source_contract_id"), item.get("source_event_id"),
                     item.get("target_contract_id"), item.get("target_event_id")]
                    for item in state["constraints"].get("constraints", [])
                ],
            })
            try:
                client = DeepSeekClient(_llm_config(cfg["llm"]))
                delta_constraints, compact_context_audit = expand_initial_composition(
                    client, prompt, selected_spec, {"contracts": candidate_contracts}, design,
                    round_root / "llm" / "compact_composition", compact_cfg,
                )
                composition_calls = deepcopy(compact_context_audit.get("calls", []))
                for record in composition_calls:
                    key = record.get("context_key")
                    if key:
                        state.setdefault("composition_context_history", {})[str(key)] = {
                            "round": index, "status": record.get("status", "NOT_EVALUATED"),
                            "source": "COMPACT_EVENT_CONTEXT", "target": None,
                        }
            except LLMUnavailableError as exc:
                compact_context_audit = {
                    "status": "INTERRUPTED_EXTERNAL_SERVICE",
                    "error": f"{type(exc).__name__}: {exc}",
                }
                composition_calls.append({
                    "name": "compact_event_context", "status": "INTERRUPTED_EXTERNAL_SERVICE",
                    "error": compact_context_audit["error"],
                })
                dump_json(round_root / "llm" / "composition_audit.json", {
                    "status": "INTERRUPTED_EXTERNAL_SERVICE", "calls": composition_calls,
                    "compact_event_context_audit": compact_context_audit,
                })
                dump_json(round_root / "external_service_failure.json", {
                    "schema": SCHEMA, "round": index, "status": "INTERRUPTED_EXTERNAL_SERVICE",
                    "stage": "COMPACT_COMPOSITION", "error": compact_context_audit["error"],
                })
                _fail_round(
                    round_root, index, "LLM_UNAVAILABLE_EXTERNAL_SERVICE",
                    stage="COMPACT_COMPOSITION", error=compact_context_audit["error"],
                )
            except Exception as exc:
                compact_context_audit = {"status": "REJECTED", "error": f"{type(exc).__name__}: {exc}"}
                composition_calls.append({"name": "compact_event_context", "status": "REJECTED", "error": compact_context_audit["error"]})

        def request_constraints(context_doc: dict[str, Any], call_name: str, *, pair_key: str | None = None,
                                required_pair: tuple[str, str] | None = None) -> None:
            nonlocal client
            composition_contexts.append(context_doc)
            record: dict[str, Any] = {"name": call_name, "context_key": pair_key, "status": "NOT_REQUESTED"}
            try:
                client = client or DeepSeekClient(_llm_config(cfg["llm"]))
                proposed, audit = _validated_llm_constraints(
                    client, prompt, context_doc, round_root / "llm" / "composition_calls" / f"{call_name}.json",
                    attempts=int(req.get("llm_validation_attempts", 4)),
                    maximum_delay=int(req.get("maximum_composition_delay", 96)),
                )
                # Pair contexts are directional by construction.  Keep only a
                # relation proven by the exact queued output->input edge; a
                # reversed relation is a different queue context, not a free
                # LLM reinterpretation of this one.
                if required_pair is not None:
                    kept = [item for item in proposed.get("constraints", [])
                            if (str(item.get("source_contract_id")), str(item.get("target_contract_id"))) == required_pair]
                    kept_ids = {item["constraint_id"] for item in kept}
                    proposed = {
                        "constraints": kept,
                        "lifecycle_chains": [item for item in proposed.get("lifecycle_chains", [])
                                             if item.get("constraint_ids") and all(cid in kept_ids for cid in item["constraint_ids"])],
                    }
                    record["discarded_wrong_direction"] = len(audit.get("constraints", [])) - len(kept) if isinstance(audit, dict) else 0
                delta_constraints["constraints"].extend(proposed.get("constraints", []))
                delta_constraints["lifecycle_chains"].extend(proposed.get("lifecycle_chains", []))
                record.update(status="VALIDATED" if proposed.get("constraints") else "VALIDATED_EMPTY", audit=audit,
                              constraints=len(proposed.get("constraints", [])))
            except LLMUnavailableError as exc:
                record.update(status="INTERRUPTED_EXTERNAL_SERVICE", error=f"{type(exc).__name__}: {exc}")
                dump_json(round_root / "llm" / "composition_contexts.json", composition_contexts)
                dump_json(round_root / "llm" / "composition_audit.json", {
                    "status": "INTERRUPTED_EXTERNAL_SERVICE", "calls": composition_calls,
                    "error": record["error"],
                })
                dump_json(round_root / "external_service_failure.json", {
                    "schema": SCHEMA, "round": index, "status": "INTERRUPTED_EXTERNAL_SERVICE",
                    "stage": "PAIR_COMPOSITION", "error": record["error"],
                })
                _fail_round(
                    round_root, index, "LLM_UNAVAILABLE_EXTERNAL_SERVICE",
                    stage="PAIR_COMPOSITION", error=record["error"],
                )
            except Exception as exc:
                record.update(status="REJECTED", error=f"{type(exc).__name__}: {exc}")
            finally:
                if pair_key and record["status"] != "INTERRUPTED_EXTERNAL_SERVICE":
                    state.setdefault("composition_context_history", {})[pair_key] = {
                        "round": index, "status": record["status"], "source": required_pair[0] if required_pair else None,
                        "target": required_pair[1] if required_pair else None,
                    }
                composition_calls.append(record)

        if not compact_event_context_enabled and changed_contract_ids and max_contexts:
            changed_context = _delta_composition_context(
                selected_spec, candidate_contracts, changed_contract_ids,
                int(feedback.get("composition_context_contract_limit", 2)),
            )
            if len(changed_context["contracts"]) >= 2:
                request_constraints(changed_context, "changed_contract_delta")
                max_contexts -= 1
                changed_context_consumed = 1
            else:
                composition_calls.append({"name": "changed_contract_delta", "status": "NO_TYPED_INTERFACE_NEIGHBOUR"})

        queue = [] if compact_event_context_enabled else _typed_interface_pair_queue(
            candidate_contracts, state["constraints"], state.get("composition_context_history", {}),
        )
        if not compact_event_context_enabled:
            for serial, queued in enumerate(queue[:max_contexts], 1):
                context = _pair_composition_context(selected_spec, queued)
                request_constraints(
                    context, f"typed_interface_pair_{serial:02d}", pair_key=queued["context_key"],
                    required_pair=(queued["source_contract_id"], queued["target_contract_id"]),
                )
        composition_llm: dict[str, Any] = {
            "status": "NOT_REQUESTED" if not composition_calls else "COMPLETED",
            "calls": composition_calls,
            "context_budget": composition_budget,
            "queue_available": len(queue), "queue_consumed": min(len(queue), max_contexts),
            "changed_contract_context_consumed": changed_context_consumed,
            "compact_event_context_enabled": compact_event_context_enabled,
            "compact_event_context_audit": compact_context_audit,
            "policy": "strict Local Contracts + typed RTL interface + exact supplied SPEC evidence",
        }
        dump_json(round_root / "llm" / "composition_context.json", composition_contexts[0] if composition_contexts else {})
        dump_json(round_root / "llm" / "composition_contexts.json", composition_contexts)
        dump_json(round_root / "llm" / "composition_audit.json", composition_llm)

        merged_constraints, constraint_merge_audit = _merge_delta_constraints(
            state["constraints"], delta_constraints, round_index=index,
        )
        active_constraints = _active_constraints(merged_constraints, candidate_contracts)
        delta_constraint_ids = set(constraint_merge_audit["delta_constraint_ids"])
        # A fresh SPEC relation changes a pre-existing pair's graph edge even
        # if neither Local Contract's own fingerprint changed.
        graph_changed_contract_ids = set(changed_contract_ids)
        for item in active_constraints["constraints"]:
            if item["constraint_id"] in delta_constraint_ids:
                graph_changed_contract_ids.update((str(item["source_contract_id"]), str(item["target_contract_id"])))
        graph_doc, edge_audit = incremental_contract_graph(
            state["contract_graph"], candidate_contracts, active_constraints, graph_changed_contract_ids,
        )
        composition_input, incremental_composition_audit = _incremental_composition_input(
            active_constraints, constraint_merge_audit,
        )
        has_incremental_composition = bool(
            incremental_composition_audit["delta_constraint_ids"]
            or incremental_composition_audit["selected_chain_ids"]
        )
        if has_incremental_composition:
            comp_doc = _retain_incremental_composition_candidates(
                generate_composition_candidates(graph_doc, composition_input),
                incremental_composition_audit,
            )
        else:
            comp_doc = {
            "schema": "feedback-empty-composition-candidates.v1", "candidates": [],
            "rejections": {"NO_DELTA_SPEC_CONSTRAINT_OR_CHAIN": 1}, "summary": {"candidates": 0},
        }
        composition_selected, composition_portfolio = select_composition_portfolio(
            comp_doc, caps=req.get("composition_caps", {}),
        ) if comp_doc.get("candidates") else ([], {"selected": 0, "reason": "NO_DELTA_CANDIDATE"})
        composition_props, composition_metadata = compile_composition_properties(
            composition_selected, design, reset_asserted,
        ) if composition_selected else ([], {})
        composition_props, composition_metadata = _rename_properties(
            composition_props, composition_metadata, round_index=index, kind="composition",
        )
        composition_props, composition_exact_rejections = _deduplicate_new(
            composition_props, active=candidate_properties, history=state["attempt_history"],
        ) if feedback.get("deduplicate_sva", True) else (composition_props, [])
        composition_props, composition_render_rejections = _filter_renderable_properties(composition_props, design)
        _record_generation(state, composition_props, round_index=index, kind="COMPOSITION")
        dump_json(round_root / "contract_graph.json", graph_doc)
        dump_json(round_root / "incremental_edge_audit.json", edge_audit)
        dump_json(round_root / "active_constraints.json", active_constraints)
        dump_json(round_root / "constraint_merge_audit.json", constraint_merge_audit)
        dump_json(round_root / "incremental_composition_input.json", composition_input)
        dump_json(round_root / "incremental_composition_audit.json", incremental_composition_audit)
        dump_json(round_root / "composition_candidates.json", comp_doc)
        dump_json(round_root / "composition_portfolio.json", composition_portfolio)
        dump_json(round_root / "composition" / "generated_properties.json", composition_props)
        dump_json(round_root / "composition" / "dedup_rejections.json", composition_exact_rejections)
        dump_json(round_root / "composition" / "render_rejections.json", composition_render_rejections)

        strict_composition, composition_probe, composition_stable_audit, _composition_strict_result = _strict_probe(
            design, composition_props, str(target["top"]), round_root / "formal" / "composition", local_config, graph,
        )
        _record_probe_history(state["attempt_history"], composition_props, composition_probe, round_index=index, kind="COMPOSITION")
        _record_strict_rejections(
            state["attempt_history"], composition_props, strict_composition, round_index=index, kind="COMPOSITION",
        )

        promoted = strict_local + strict_composition
        if promoted:
            retained_promoted, final_result, final_stable_audit = _stable_formal(
                design, state["properties"], promoted, str(target["top"]),
                round_root / "formal" / "cumulative", local_config, graph=graph,
            )
            final_properties = [*state["properties"], *retained_promoted]
        else:
            # Zero-promotion does *not* reuse an old report: it performs the
            # same strict full-portfolio stability run.  Thus a CEX, timeout,
            # missing property result, or missing coverage export fails the
            # round rather than being silently called a completed zero-gain
            # iteration.
            retained_promoted, final_result, final_stable_audit = _stable_formal(
                design, state["properties"], [], str(target["top"]),
                round_root / "formal" / "cumulative", local_config, graph=graph,
            )
            if retained_promoted:
                raise RuntimeError("zero-candidate strict portfolio unexpectedly returned new properties")
            final_properties = list(state["properties"])
        # A composition requires the newly trusted Local interface that made
        # its Contract delta meaningful.  If scheduler-dependent remeasurement
        # drops any such Local property, conservatively remove the batch's
        # composition candidates and establish the reduced exact portfolio.
        final_ids_before_dependency_gate = {item.property_id for item in final_properties}
        retained_local_before_dependency_gate = [
            item for item in strict_local if item.property_id in final_ids_before_dependency_gate
        ]
        if strict_composition and len(retained_local_before_dependency_gate) != len(strict_local):
            retained_promoted, final_result, final_stable_audit = _stable_formal(
                design, state["properties"], retained_local_before_dependency_gate,
                str(target["top"]), round_root / "formal" / "cumulative", local_config, graph=graph,
            )
            final_properties = [*state["properties"], *retained_promoted]
            strict_composition = []
        coverage_export = round_root / "formal" / "cumulative" / "formal" / "coverage_items.tsv"
        if not coverage_export.is_file():
            _fail_round(round_root, index, "MISSING_COVERAGE_EXPORT", path=str(coverage_export))
        final_items = parse_coverage_items(coverage_export)
        if not final_items:
            _fail_round(round_root, index, "EMPTY_COVERAGE_EXPORT", path=str(coverage_export))
        final_by_id = {item.property_id: item for item in final_result.results}
        expected_final_ids = {item.property_id for item in final_properties}
        final_extra = sorted(set(final_by_id) - expected_final_ids)
        final_missing = sorted(expected_final_ids - set(final_by_id))
        final_not_pass = sorted(
            property_id for property_id in expected_final_ids
            if property_id in final_by_id and final_by_id[property_id].result != "PASS"
        )
        if final_extra or final_missing or final_not_pass:
            _fail_round(
                round_root, index, "EXACT_PORTFOLIO_RESULT_MISMATCH",
                extra=final_extra[:16], missing=final_missing[:16], not_pass=final_not_pass[:16],
            )
        initial_universe = set(state["initial_coverage_universe"])
        final_universe = _exact_universe(final_items)
        if final_universe != initial_universe:
            _fail_round(
                round_root, index, "PROOF_CORE_UNIVERSE_CHANGED",
                initial_count=len(initial_universe), final_count=len(final_universe),
                missing=sorted(initial_universe - final_universe)[:16],
                unexpected=sorted(final_universe - initial_universe)[:16],
            )

        # Only Contract/Region changes backed by a surviving strict Local SVA
        # become part of the next round's semantic state.
        retained_new_ids = {item.property_id for item in final_properties} - {item.property_id for item in state["properties"]}
        retained_local = [item for item in strict_local if item.property_id in retained_new_ids]
        retained_composition = [item for item in strict_composition if item.property_id in retained_new_ids]
        _record_strict_rejections(
            state["attempt_history"], promoted,
            [item for item in final_properties if item.property_id in retained_new_ids],
            round_index=index, kind="FINAL_PORTFOLIO",
        )
        # Reconstruct the next semantic state from *the exact retained
        # portfolio*.  In particular, do not retain a Region/Contract merely
        # because its probe passed before the full multi-target portfolio; do
        # not retain an LLM relation unless a composition using it survived.
        old_region_ids = {item["region_id"] for item in state["regions"]}
        actual_extensions = [
            available_extensions[region_id] for region_id in sorted({item.region_id for item in retained_local})
            if region_id in available_extensions and region_id not in old_region_ids
        ]
        actual_regions = [*state["regions"], *actual_extensions]
        actual_metadata = deepcopy(state["property_metadata"])
        actual_metadata.update({item.property_id: local_metadata[item.property_id]
                                for item in retained_local if item.property_id in local_metadata})
        actual_contracts = build_local_contracts(
            {"regions": actual_regions},
            [item for item in final_properties if not _is_composite(item)],
            actual_metadata, graph, design,
        )["contracts"]
        retained_constraint_ids = {
            constraint_id for item in retained_composition
            for constraint_id in composition_metadata.get(item.property_id, {}).get("constraint_ids", [])
        }
        prior_constraint_ids = {
            str(item.get("constraint_id")) for item in state["constraints"].get("constraints", [])
        }
        prior_chain_ids = {
            str(item.get("chain_id", "")) for item in state["constraints"].get("lifecycle_chains", [])
        }
        persisted_constraints = {
            "constraints": [
                item for item in state["constraints"].get("constraints", [])
                if item.get("constraint_id") not in delta_constraint_ids
            ] + [
                item for item in active_constraints.get("constraints", [])
                if item.get("constraint_id") in retained_constraint_ids
                and str(item.get("constraint_id")) not in prior_constraint_ids
            ],
            "lifecycle_chains": [
                item for item in state["constraints"].get("lifecycle_chains", [])
                if all(cid in {entry.get("constraint_id") for entry in state["constraints"].get("constraints", [])}
                       for cid in item.get("constraint_ids", []))
            ] + [
                item for item in active_constraints.get("lifecycle_chains", [])
                if item.get("constraint_ids")
                and all(cid in retained_constraint_ids for cid in item["constraint_ids"])
                and str(item.get("chain_id", "")) not in prior_chain_ids
            ],
        }
        actual_constraints = _active_constraints(persisted_constraints, actual_contracts)
        old_contracts = {item["contract_id"]: _contract_fingerprint(item) for item in state["contracts"]}
        actual_changed_contract_ids = {
            item["contract_id"] for item in actual_contracts
            if old_contracts.get(item["contract_id"]) != _contract_fingerprint(item)
        }
        for item in actual_constraints["constraints"]:
            if item["constraint_id"] in retained_constraint_ids:
                actual_changed_contract_ids.update((str(item["source_contract_id"]), str(item["target_contract_id"])))
        actual_graph, actual_edge_audit = incremental_contract_graph(
            state["contract_graph"], actual_contracts, actual_constraints, actual_changed_contract_ids,
        )
        state["regions"] = actual_regions
        state["contracts"] = actual_contracts
        state["constraints"] = actual_constraints
        state["contract_graph"] = actual_graph
        state["property_metadata"] = actual_metadata
        state["pending_region_motifs"] = deferred_motifs
        pending_extension_ids = {
            str(item.get("extension_region_id")) for item in deferred_local_entries
            if item.get("extension_region_id") in available_extensions
        }
        state["pending_extension_regions"] = {
            region_id: available_extensions[region_id] for region_id in sorted(pending_extension_ids)
        }
        state["pending_local_candidates"] = deferred_local_entries
        state["properties"] = final_properties
        state["round"] = index

        final_mapping = localize_refinement_gaps(final_items, graph, state["regions"], design_map=design_map)
        gain = _coverage_delta(previous_items, final_items)
        current_sources = _coverage_identity(final_items)
        if not _rtl_coverage_identity_is_stable(
            gain, current_sources, state["initial_coverage_sources"],
        ):
            _fail_round(
                round_root, index, "RTL_COVER_ITEM_UNIVERSE_OR_SOURCE_DRIFT", gain=gain,
                initial_source_identity_constant=current_sources == state["initial_coverage_sources"],
            )
        summary = {
            "schema": SCHEMA, "status": "COMPLETE", "round": index,
            "previous_effective_proof_core": coverage_by_type(previous_items)["all"],
            "effective_proof_core": coverage_by_type(final_items)["all"],
            "gain": gain, "initial_gap_summary": gap_summary(gap_records),
            "final_gap_summary": gap_summary(final_mapping),
            "regions": {
                "motifs_found": len(motifs), "new_motifs_considered": len(new_motifs),
                "llm_validated_extensions": len(extension_regions),
                "extensions_promoted": len(promoted_extensions) if retained_local else 0,
            },
            "local": {
                "generated": len(local_props), "strict_trusted": len(strict_local),
                "promoted": len(retained_local),
                "candidate_gate": result_counts(local_props, local_probe.results) if local_probe else result_counts([], []),
                "strict_audit": local_stable_audit,
            },
            "composition": {
                "changed_contract_ids": sorted(changed_contract_ids), "generated": len(composition_props),
                "strict_trusted": len(strict_composition), "promoted": len(retained_composition),
                "candidate_gate": result_counts(composition_props, composition_probe.results) if composition_probe else result_counts([], []),
                "strict_audit": composition_stable_audit,
                "llm": composition_llm, "incremental_edge_update_candidate": edge_audit,
                "incremental_edge_update_retained": actual_edge_audit,
                "constraint_merge": constraint_merge_audit,
            },
            "portfolio": {
                "properties": len(final_properties),
                "local": sum(not _is_composite(item) for item in final_properties),
                "composition": sum(_is_composite(item) for item in final_properties),
                "formal": result_counts(final_properties, final_result.results),
                "strict_audit": final_stable_audit,
            },
            "formal_cumulative": str(round_root / "formal" / "cumulative" / "formal" / "formal_results.json"),
            "feedback_is_real": True,
            "zero_property_growth": not bool(retained_new_ids),
            "zero_gain_round": gain["net_checked_items"] <= 0,
        }
        dump_json(round_root / "final_gap_mapping.json", final_mapping)
        dump_json(round_root / "round_summary.json", summary)
        _persist_state(round_root, _json_state(state))
        dump_json(round_root / "round_status.json", {"round": index, "status": "COMPLETE"})
        previous_items = final_items

    round_summaries = [_read((checkpoint / "rounds" if checkpoint is not None and index <= checkpoint_round else rounds_root) / f"round_{index:02d}" / "round_summary.json") for index in range(1, rounds + 1)]
    local_total = sum(not _is_composite(item) for item in state["properties"])
    composition_total = sum(_is_composite(item) for item in state["properties"])
    composition_fraction = composition_total / len(state["properties"]) if state["properties"] else 0.0
    generated_values = list(state.get("generation_history", {}).values())
    generated_local = sum(item.get("kind") == "LOCAL" for item in generated_values)
    generated_composition = sum(item.get("kind") == "COMPOSITION" for item in generated_values)
    generated_total = generated_local + generated_composition
    generated_composition_fraction = generated_composition / generated_total if generated_total else 0.0
    desired_fraction = float(feedback.get("desired_composition_fraction", 0.20))
    policy_summary = _generated_policy_summary(state)
    final_context_budget = _composition_context_budget(state, feedback, rounds)
    actual_context_calls = sum(len(row.get("composition", {}).get("llm", {}).get("calls", [])) for row in round_summaries)
    final_summary = {
        "schema": SCHEMA, "design_id": target["design_id"], "rounds_requested": rounds,
        "inherited_checkpoint": manifest.get("checkpoint"),
        "rounds_completed": len(round_summaries), "initial_formal_root": str(initial_formal_root),
        "initial_effective_proof_core": coverage_by_type(_require_initial_portfolio(initial_root)[2])["all"],
        "final_effective_proof_core": coverage_by_type(previous_items)["all"],
        "trend": [{
            "round": row["round"], "new_checked_items": row["gain"]["new_checked_items"],
            "net_checked_items": row["gain"]["net_checked_items"],
            "effective_coverage_percent": row["effective_proof_core"]["effective_percent"],
            "effective_coverage_delta_percentage_points": row["gain"]["effective_coverage_delta_percentage_points"],
            "zero_gain_round": row["zero_gain_round"],
        } for row in round_summaries],
        "final_portfolio": {
            "properties": len(state["properties"]), "local_sva": local_total,
            "composition_sva": composition_total,
            "trusted_composition_fraction": round(composition_fraction, 6),
            "composition_fraction": round(composition_fraction, 6),
            "generated": {
                "unique_exact_sva": generated_total, "local_sva": generated_local,
                "composition_sva": generated_composition,
                "composition_fraction": round(generated_composition_fraction, 6),
            },
            "desired_composition_fraction": desired_fraction,
            "desired_fraction_met_by_trusted_portfolio": composition_fraction >= desired_fraction,
            "desired_fraction_met_by_generated_candidates": generated_composition_fraction >= desired_fraction,
            "ratio_policy": "generated and strict-trusted fractions are both reported; no composition quota or relabelling was used",
            "semantic_search_budget": {
                **final_context_budget,
                "rounds": rounds,
                "upper_bound_new_contexts": final_context_budget["effective_contexts_per_round"] * rounds,
                "actual_context_calls": actual_context_calls,
                "pending_contexts_after_final_round": len(_typed_interface_pair_queue(
                    state["contracts"], state["constraints"], state.get("composition_context_history", {}),
                )),
                "bottleneck_note": "A low ratio is reported as a search/strict-trust outcome; the engine does not manufacture composites to meet 20%.",
            },
        },
        "generated_assertion_policy_results": {
            **policy_summary,
            "formal_prove_time_limit": str(cfg.get("formal", {}).get("prove_time_limit", "")),
            "timeout_policy": str(feedback.get("timeout_policy", "TIMEOUT_ACCEPTED_AS_PROVEN_POLICY")),
            "strict_contract_growth_policy": "PASS_AND_NON_VACUOUS",
        },
        "attempt_history": state["attempt_history"],
        "artifacts": {
            "rounds": str(rounds_root), "final_properties": str(rounds_root / f"round_{rounds:02d}" / "active_properties.json"),
            "final_regions": str(rounds_root / f"round_{rounds:02d}" / "active_regions.json"),
        },
    }
    dump_json(output_root / "feedback_summary.json", final_summary)
    return final_summary
