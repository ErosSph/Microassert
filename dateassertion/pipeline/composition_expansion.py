"""Compact, evidence-preserving initial Contract composition for Req12.

The legacy initial composition prompt packages a broad Contract inventory in a
single request.  Large designs can exceed the prompt character limit before
the LLM sees most valid interfaces.  This module instead enumerates only
real, same-module typed interface witnesses and issues compact requests for
one event-pair or one continuous three/four-Contract chain at a time.

The LLM binds supplied SPEC text to pre-existing Contract event IDs.  It does
not create signals, events, contracts, timing templates, or SVA.  The mature
Req8.8 validator remains the authority for ID existence, exact SPEC quotes,
predicate duplication, relation type, and bounded delay validation.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from copy import deepcopy
import hashlib
import json
from math import ceil
from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import dump_json
from dateassertion.llm.client import LLMUnavailableError
from dateassertion.pipeline.local_contract_composition import _relation
from dateassertion.pipeline.spec_composition import _validated_llm_constraints
from dateassertion.rtl_frontend.semantic_graph import width_bits


SCHEMA = "feedback-compact-initial-composition.v1"
_IDENTIFIER = re.compile(r"^[!~]?([A-Za-z_$][A-Za-z0-9_$]*)(\[[0-9]+\])?$")


def _sha(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, sort_keys=True, default=str).encode("utf-8")
    ).hexdigest()


def _serialized_size(value: Any) -> int:
    return len(json.dumps(value, ensure_ascii=False, separators=(",", ":")))


def _feedback(config: dict[str, Any]) -> dict[str, Any]:
    return config.get("feedback", {}) if isinstance(config, dict) else {}


def _formal_or_req(config: dict[str, Any], name: str, default: int) -> int:
    req = config.get("design_flow", {}) if isinstance(config, dict) else {}
    return int(req.get(name, _feedback(config).get(name, default)))


def _event_compact(event: dict[str, Any]) -> dict[str, Any]:
    """Retain original event predicates and provenance verbatim; never trim text."""

    return {key: deepcopy(event.get(key)) for key in (
        "event_id", "predicate", "semantic_role", "event_kind", "signals", "source",
    )}


def _contract_compact(contract: dict[str, Any], events: list[dict[str, Any]]) -> dict[str, Any]:
    interface = contract.get("interface", {})
    return {
        "contract_id": contract["contract_id"], "region_id": contract["region_id"],
        "module": contract["module"], "region_kind": contract.get("region_kind", "UNKNOWN"),
        "readiness_level": contract.get("readiness_level", 0),
        "inputs": deepcopy(interface.get("inputs", [])),
        "outputs": deepcopy(interface.get("outputs", [])),
        "state": deepcopy(interface.get("state", [])),
        "events": [_event_compact(item) for item in events],
        "trusted_local_obligations": deepcopy(contract.get("trusted_local_obligations", [])),
    }


def _bare_boolean_rejection_reason(event: dict[str, Any], contract: dict[str, Any], design: Any) -> str | None:
    """Reject ``some_32_bit_bus`` as a Boolean event without rewriting it.

    Predicates such as ``bus == 0``, ``bus[0]``, and ``!bus`` are already
    explicit RTL Boolean expressions and are retained.  We reject a whole
    multi-bit signal used by itself, or bitwise complement ``~bus`` used as a
    Boolean, because turning either into an equality would invent semantics.
    """

    predicate = str(event.get("predicate", "")).strip()
    while predicate.startswith("(") and predicate.endswith(")"):
        predicate = predicate[1:-1].strip()
    if predicate.startswith("!"):
        return None  # logical negation is an explicit zero-test in RTL.
    matched = _IDENTIFIER.fullmatch(predicate)
    if not matched or matched.group(2):
        return None
    signal = matched.group(1)
    info = getattr(design, "module_signals", {}).get(str(contract.get("module", "")), {}).get(signal)
    if info is None:
        return "BARE_UNKNOWN_WIDTH_BOOLEAN_PREDICATE"
    raw_width = getattr(info, "width", "")
    if isinstance(raw_width, int):
        bits = raw_width
    else:
        bits = width_bits(str(raw_width), getattr(design, "macros", {}))
    if bits is None:
        return "BARE_UNKNOWN_WIDTH_BOOLEAN_PREDICATE"
    return "BARE_MULTIBIT_BOOLEAN_PREDICATE" if bits > 1 else None


def _event_rank(event: dict[str, Any], shared: set[str], *, source: bool) -> int:
    signals = {str(item) for item in event.get("signals", [])}
    kind = str(event.get("event_kind", "")).upper()
    role = str(event.get("semantic_role", "")).upper()
    rank = 100 if signals & shared else 0
    if source:
        rank += 30 if kind in {"EFFECT", "STATE"} else 0
        rank += 10 if role in {"EFFECT", "STATE", "UPDATE"} else 0
    else:
        rank += 30 if kind == "TRIGGER" else 0
        rank += 15 if kind in {"EFFECT", "STATE"} else 0
        rank += 10 if role in {"TRIGGER", "GUARD", "STATE", "EFFECT"} else 0
    return rank


def _anchored_events(
    contract: dict[str, Any], shared: list[str], design: Any, *, source: bool,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    shared_set = set(shared)
    accepted, rejected = [], []
    for raw in contract.get("interface", {}).get("events", []):
        event = deepcopy(raw)
        rejection = _bare_boolean_rejection_reason(event, contract, design)
        if rejection:
            rejected.append({"event_id": event.get("event_id"), "reason": rejection})
            continue
        if not ({str(item) for item in event.get("signals", [])} & shared_set):
            rejected.append({"event_id": event.get("event_id"), "reason": "NOT_ANCHORED_TO_TYPED_INTERFACE_SIGNAL"})
            continue
        accepted.append(event)
    return (
        sorted(accepted, key=lambda item: (-_event_rank(item, shared_set, source=source), str(item.get("event_id", "")))),
        rejected,
    )


def _atomic_event_pairs(
    source: dict[str, Any], target: dict[str, Any], relation: dict[str, Any], design: Any,
    *, event_limit: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Return genuine event witnesses for an already-real output->input edge."""

    shared = list(relation.get("shared_interface_signals", []))
    source_events, source_rejected = _anchored_events(source, shared, design, source=True)
    target_events, target_rejected = _anchored_events(target, shared, design, source=False)
    if not source_events or not target_events:
        return [], [{
            "source_contract_id": source["contract_id"], "target_contract_id": target["contract_id"],
            "reason": "NO_SIGNAL_ANCHORED_EVENT_PAIR",
            "source_event_rejections": source_rejected, "target_event_rejections": target_rejected,
        }]
    pairs = []
    # This is a bounded witness list, not a Cartesian prompt dump.
    for source_event in source_events[:event_limit]:
        for target_event in target_events[:event_limit]:
            if "".join(str(source_event.get("predicate", "")).split()) == "".join(str(target_event.get("predicate", "")).split()):
                continue
            pairs.append({
                "source_contract_id": source["contract_id"], "source_event_id": source_event["event_id"],
                "target_contract_id": target["contract_id"], "target_event_id": target_event["event_id"],
                "source_event": source_event, "target_event": target_event,
                "shared_interface_signals": shared,
                "execution_context_status": relation.get("execution_context_status"),
            })
    return pairs[:event_limit], []


def typed_event_pair_queue(
    local_contracts: dict[str, Any], design: Any, *, event_limit: int = 3,
    max_pair_evaluations: int = 12_000,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Deterministically enumerate only strict Contracts with real typed event pairs."""

    values, rejected = [], []
    contracts = sorted(
        (item for item in local_contracts.get("contracts", []) if int(item.get("readiness_level", 0)) >= 2),
        key=lambda item: str(item["contract_id"]),
    )
    # Index by actual target input/state signal.  This avoids a blind O(N^2)
    # all-Contract scan while preserving every possible output->input/state
    # witness inside the explicit evaluation budget.
    target_index: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for target in contracts:
        interface = target.get("interface", {})
        for signal in sorted(set(interface.get("inputs", [])) | set(interface.get("state", []))):
            target_index[(str(target.get("module", "")), str(signal))].append(target)
    evaluated, exhausted = 0, False
    for source in contracts:
        source_outputs = sorted(set(source.get("interface", {}).get("outputs", [])))
        targets_by_id = {
            str(target["contract_id"]): target
            for signal in source_outputs
            for target in target_index.get((str(source.get("module", "")), str(signal)), [])
        }
        for target in sorted(targets_by_id.values(), key=lambda item: str(item["contract_id"])):
            if evaluated >= max(0, max_pair_evaluations):
                exhausted = True
                break
            evaluated += 1
            relation = _relation(source, target)
            if not relation or not relation.get("shared_interface_signals"):
                continue
            pairs, pair_rejections = _atomic_event_pairs(source, target, relation, design, event_limit=event_limit)
            rejected.extend(pair_rejections)
            if not pairs:
                continue
            # One exact source-event -> target-event witness per compact
            # context.  A prior A->B event relation must not suppress a
            # distinct, still-real A->B event relation merely because the
            # Contract pair is the same.
            for pair in pairs:
                signature = _sha({
                    "source": source["contract_id"], "target": target["contract_id"],
                    "signals": relation["shared_interface_signals"],
                    "source_event": pair["source_event_id"], "target_event": pair["target_event_id"],
                })
                values.append({
                    "context_key": signature, "kind": "EVENT_PAIR", "source": source, "target": target,
                    "relation": relation, "event_pairs": [pair],
                    "edge_key": (source["contract_id"], target["contract_id"], tuple(relation["shared_interface_signals"])),
                })
        if exhausted:
            break
    if exhausted:
        rejected.append({
            "reason": "TYPED_INTERFACE_PAIR_EVALUATION_BUDGET_EXHAUSTED",
            "evaluated_directed_pairs": evaluated, "max_pair_evaluations": max_pair_evaluations,
            "enumeration": "deterministic signal-indexed worklist; remaining compatible pairs were not claimed absent",
        })
    values.sort(key=lambda item: (
        -len(item["relation"]["shared_interface_signals"]), -len(item["event_pairs"]),
        item["source"]["contract_id"], item["target"]["contract_id"],
    ))
    return values, rejected


def _pair_context(candidate: dict[str, Any]) -> dict[str, Any]:
    source, target = candidate["source"], candidate["target"]
    by_source = {item["source_event_id"]: item["source_event"] for item in candidate["event_pairs"]}
    by_target = {item["target_event_id"]: item["target_event"] for item in candidate["event_pairs"]}
    return {
        "schema": SCHEMA,
        "whole_design_rtl_supplied": False,
        "context_kind": "TYPED_EVENT_PAIR",
        "incremental_scope": {
            "context_key": candidate["context_key"],
            "selection": "same-module typed source-output to target-input/state interface witness",
            "source_contract_id": source["contract_id"], "target_contract_id": target["contract_id"],
            "shared_interface_signals": candidate["relation"]["shared_interface_signals"],
            "execution_context_status": candidate["relation"]["execution_context_status"],
        },
        "allowed_relation_types": ["CAUSALITY", "ORDERING", "DATA_TRANSFER", "STATE_CONTROL"],
        "allowed_contract_ids": [source["contract_id"], target["contract_id"]],
        "allowed_event_pairs": [{key: item[key] for key in (
            "source_contract_id", "source_event_id", "target_contract_id", "target_event_id",
            "shared_interface_signals", "execution_context_status",
        )} for item in candidate["event_pairs"]],
        "contracts": [_contract_compact(source, list(by_source.values())), _contract_compact(target, list(by_target.values()))],
        "prohibited_outputs": ["SVA", "SystemVerilog", "assert property", "assume property"],
    }


def _chain_candidates(
    pair_candidates: list[dict[str, Any]], *, max_contracts: int = 4,
    max_seed_atoms: int = 4_000, max_expansions: int = 12_000,
    max_candidates: int = 1_024, audit: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Find only continuous chains: the intermediate Contract *event ID* is identical."""

    all_atoms = sorted(
        (atom for candidate in pair_candidates for atom in candidate["event_pairs"]),
        key=lambda item: (item["source_contract_id"], item["source_event_id"], item["target_contract_id"], item["target_event_id"]),
    )
    atoms = all_atoms[:max(0, max_seed_atoms)]
    next_by_source: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for atom in atoms:
        next_by_source[(atom["source_contract_id"], atom["source_event_id"])].append(atom)
    for key in next_by_source:
        next_by_source[key].sort(key=lambda item: (
            item["source_contract_id"], item["source_event_id"], item["target_contract_id"], item["target_event_id"],
        ))
    values, seen = [], set()
    # Breadth-first, deterministic worklist.  It deliberately samples many
    # short real chains before deepening any one dense subgraph, and records
    # every stopping limit so callers never mistake it for exhaustive search.
    worklist = deque([[atom] for atom in atoms])
    expansions = 0
    extension_budget_exhausted = False
    while worklist and len(values) < max(0, max_candidates):
        path = worklist.popleft()
        if len(path) >= 2:
            contracts = [path[0]["source_contract_id"]] + [item["target_contract_id"] for item in path]
            signature = tuple((item["source_contract_id"], item["source_event_id"], item["target_contract_id"], item["target_event_id"]) for item in path)
            if len(set(contracts)) == len(contracts) and signature not in seen:
                seen.add(signature)
                values.append({"kind": "CONTINUOUS_CHAIN", "atoms": deepcopy(path), "contract_ids": contracts,
                               "context_key": _sha({"chain": signature})})
        if len(path) >= max_contracts - 1:
            continue
        tail = path[-1]
        path_contracts = {item["source_contract_id"] for item in path} | {tail["target_contract_id"]}
        for next_atom in next_by_source.get((tail["target_contract_id"], tail["target_event_id"]), []):
            if next_atom["target_contract_id"] in path_contracts:
                continue
            if expansions >= max(0, max_expansions):
                extension_budget_exhausted = True
                break
            worklist.append([*path, next_atom])
            expansions += 1
    if audit is not None:
        audit.update({
            "enumeration": "deterministic bounded breadth-first continuous-event worklist; not exhaustive",
            "atoms_available": len(all_atoms), "seed_atoms_selected": len(atoms),
            "max_seed_atoms": max_seed_atoms, "chain_expansions": expansions,
            "max_expansions": max_expansions, "candidates": len(values), "max_candidates": max_candidates,
            "extension_budget_exhausted": extension_budget_exhausted,
            "truncated": len(all_atoms) > len(atoms) or bool(worklist) or extension_budget_exhausted,
            "remaining_worklist_paths": len(worklist),
        })
    return sorted(values, key=lambda item: (-len(item["atoms"]), item["context_key"]))


def _chain_context(candidate: dict[str, Any], contracts_by_id: dict[str, dict[str, Any]]) -> dict[str, Any]:
    used_events: dict[str, dict[str, dict[str, Any]]] = defaultdict(dict)
    pairs = []
    for atom in candidate["atoms"]:
        used_events[atom["source_contract_id"]][atom["source_event_id"]] = atom["source_event"]
        used_events[atom["target_contract_id"]][atom["target_event_id"]] = atom["target_event"]
        pairs.append({key: atom[key] for key in (
            "source_contract_id", "source_event_id", "target_contract_id", "target_event_id",
            "shared_interface_signals", "execution_context_status",
        )})
    selected = [contracts_by_id[item] for item in candidate["contract_ids"]]
    return {
        "schema": SCHEMA,
        "whole_design_rtl_supplied": False,
        "context_kind": "CONTINUOUS_TYPED_EVENT_CHAIN",
        "incremental_scope": {
            "context_key": candidate["context_key"],
            "selection": "continuous same-event-ID chain over real typed interface witnesses",
            "contract_ids": candidate["contract_ids"], "continuous_event_ids": [item["target_event_id"] for item in candidate["atoms"][:-1]],
        },
        "allowed_relation_types": ["CAUSALITY", "ORDERING", "DATA_TRANSFER", "STATE_CONTROL"],
        "allowed_contract_ids": candidate["contract_ids"], "allowed_event_pairs": pairs,
        "contracts": [_contract_compact(item, list(used_events[item["contract_id"]].values())) for item in selected],
        "prohibited_outputs": ["SVA", "SystemVerilog", "assert property", "assume property"],
    }


def _with_bounded_spec(context: dict[str, Any], selected_spec: list[dict[str, Any]], max_chars: int) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Pack complete SPEC lines only; nothing is truncated or paraphrased."""

    if not selected_spec:
        return None, {"reason": "NO_SELECTED_SPEC_EVIDENCE"}
    packed = deepcopy(context)
    packed["spec_lines"] = []
    kept, omitted = [], []
    for line in selected_spec:
        trial = [*kept, deepcopy(line)]
        packed["spec_lines"] = trial
        if _serialized_size(packed) <= max_chars:
            kept = trial
        else:
            omitted.append({"line": line.get("line"), "reason": "SPEC_LINE_EXCEEDS_CONTEXT_BUDGET"})
    packed["spec_lines"] = kept
    # Keep the potentially long omitted-line list in the persisted caller
    # audit, never inside the LLM payload.  Otherwise audit metadata itself
    # could violate the hard prompt budget it claims to measure.
    packaging = {
        "serialized_chars": _serialized_size(packed), "max_context_chars": max_chars,
        "spec_lines_supplied": len(kept), "spec_lines_omitted": omitted,
        "predicates_truncated": False,
    }
    if not kept:
        return None, {"reason": "NO_COMPLETE_SPEC_LINE_FITS_CONTEXT_BUDGET", **packaging}
    # This assertion protects future additions to the context schema too.
    if packaging["serialized_chars"] > max_chars:
        return None, {"reason": "CONTEXT_EXCEEDS_HARD_SERIALIZATION_BUDGET", **packaging}
    return packed, packaging


def _initial_context_budget(local_contracts: dict[str, Any], config: dict[str, Any]) -> dict[str, Any]:
    req = _feedback(config)
    obligation_ids = {
        str(property_id) for contract in local_contracts.get("contracts", [])
        for property_id in contract.get("trusted_local_obligations", [])
    }
    local_count = int(req.get("initial_generated_local_sva", len(obligation_ids)))
    desired = float(req.get("desired_composition_fraction", 0.20))
    needed = ceil(local_count * desired / (1.0 - desired)) if 0.0 < desired < 1.0 else 0
    floor = int(req.get("initial_composition_min_contexts", req.get("composition_min_contexts_per_round", 4)))
    cap = int(req.get("initial_composition_context_budget", req.get("composition_contexts_per_round", 64)))
    return {
        "initial_local_obligations": local_count, "desired_composition_fraction": desired,
        "contexts_required_if_one_candidate_per_context": needed,
        "min_contexts": floor, "max_contexts": cap,
        "effective_context_budget": min(cap, max(floor, needed)),
        "policy": "search work budget only; accepted composite count is determined by validator and Formal",
    }


def _select_contexts(pair_candidates: list[dict[str, Any]], chain_candidates: list[dict[str, Any]], budget: int) -> list[dict[str, Any]]:
    """Greedily cover novel typed edges; no category/count quota is imposed."""

    candidates = []
    for item in pair_candidates:
        candidates.append({"kind": "PAIR", "candidate": item, "edges": {item["edge_key"]}, "contracts": {item["source"]["contract_id"], item["target"]["contract_id"]}})
    for item in chain_candidates:
        edges = {(atom["source_contract_id"], atom["target_contract_id"], tuple(atom["shared_interface_signals"])) for atom in item["atoms"]}
        candidates.append({"kind": "CHAIN", "candidate": item, "edges": edges, "contracts": set(item["contract_ids"])})
    selected, covered_edges, covered_contracts = [], set(), set()
    remaining = list(candidates)
    while remaining and len(selected) < max(0, budget):
        def score(item: dict[str, Any]) -> tuple[int, int, str]:
            new_edges = len(item["edges"] - covered_edges)
            new_contracts = len(item["contracts"] - covered_contracts)
            return (20 * new_edges + 3 * new_contracts + len(item["edges"]), len(item["edges"]), item["candidate"]["context_key"])
        best = max(remaining, key=score)
        selected.append(best)
        covered_edges.update(best["edges"])
        covered_contracts.update(best["contracts"])
        remaining.remove(best)
    return selected


def _filter_validated_to_context(validated: dict[str, Any], context: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    allowed = {
        (str(item["source_contract_id"]), str(item["source_event_id"]), str(item["target_contract_id"]), str(item["target_event_id"]))
        for item in context.get("allowed_event_pairs", [])
    }
    values = [
        deepcopy(item) for item in validated.get("constraints", [])
        if (str(item.get("source_contract_id")), str(item.get("source_event_id")),
            str(item.get("target_contract_id")), str(item.get("target_event_id"))) in allowed
    ]
    kept_ids = {item["constraint_id"] for item in values}
    chains = []
    for raw in validated.get("lifecycle_chains", []):
        ids = [str(item) for item in raw.get("constraint_ids", [])]
        by_id = {item["constraint_id"]: item for item in values}
        relations = [by_id.get(item) for item in ids]
        continuous = bool(relations) and all(relations) and all(
            relations[index]["target_contract_id"] == relations[index + 1]["source_contract_id"]
            and relations[index]["target_event_id"] == relations[index + 1]["source_event_id"]
            for index in range(len(relations) - 1)
        )
        contract_ids = ([relations[0]["source_contract_id"]] + [item["target_contract_id"] for item in relations]) if continuous else []
        if len(relations) >= 2 and continuous and len(contract_ids) == len(set(contract_ids)) and all(item in kept_ids for item in ids):
            chains.append(deepcopy(raw))
    return {"constraints": values, "lifecycle_chains": chains}, {
        "validated_before_context_filter": len(validated.get("constraints", [])),
        "retained_exact_event_witnesses": len(values),
        "dropped_not_allowed_event_pair": len(validated.get("constraints", [])) - len(values),
        "retained_continuous_chains": len(chains),
    }


def _merge_calls(calls: list[dict[str, Any]]) -> tuple[dict[str, Any], dict[str, Any]]:
    """Namespace IDs and retain all exact SPEC evidence from duplicate calls."""

    values, chains, semantic_index = [], [], {}
    audit = {"added_constraints": 0, "duplicate_semantic_constraints": 0, "added_lifecycle_chains": 0, "evidence_merged": 0}
    for call_index, call in enumerate(calls, 1):
        id_map = {}
        for raw in call.get("validated", {}).get("constraints", []):
            item = deepcopy(raw)
            semantic = _sha({key: item.get(key) for key in (
                "source_contract_id", "source_event_id", "target_contract_id", "target_event_id",
                "relation_type", "min_delay", "max_delay", "source_predicate", "target_predicate",
            )})
            if semantic in semantic_index:
                existing = semantic_index[semantic]
                evidence = deepcopy(item.get("evidence", {}))
                all_evidence = existing.setdefault("supporting_spec_evidence", [deepcopy(existing.get("evidence", {}))])
                if evidence not in all_evidence:
                    all_evidence.append(evidence)
                    audit["evidence_merged"] += 1
                audit["duplicate_semantic_constraints"] += 1
                id_map[str(item["constraint_id"])] = str(existing["constraint_id"])
                continue
            old = str(item["constraint_id"])
            item["constraint_id"] = f"feedback_initial_c{call_index:03d}_{old}"
            item["supporting_spec_evidence"] = [deepcopy(item.get("evidence", {}))]
            values.append(item)
            semantic_index[semantic] = item
            id_map[old] = item["constraint_id"]
            audit["added_constraints"] += 1
        for raw in call.get("validated", {}).get("lifecycle_chains", []):
            ids = [id_map.get(str(item)) for item in raw.get("constraint_ids", [])]
            if len(ids) < 2 or any(item is None for item in ids):
                continue
            chains.append({**deepcopy(raw), "chain_id": f"feedback_initial_c{call_index:03d}_{raw.get('chain_id', 'chain')}", "constraint_ids": ids})
            audit["added_lifecycle_chains"] += 1
    return {"schema": SCHEMA, "constraints": values, "lifecycle_chains": chains, "llm_generated_sva": False}, audit


def expand_initial_composition(
    client: Any, prompt: str, selected_spec: list[dict[str, Any]], local_contracts: dict[str, Any],
    design: Any, output: str | Path, config: dict[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Broaden initial composition without broad/unbounded Contract prompting.

    Every LLM invocation is independently persisted.  Failed calls are kept
    in ``llm_audit`` and do not erase successful calls; the result is suitable
    for fixed-template composition compilation by the caller.
    """

    output = Path(output)
    req = _feedback(config)
    event_limit = max(1, int(req.get("compact_events_per_role", 3)))
    max_chars = max(1_024, int(req.get("compact_composition_context_chars", 16_000)))
    pair_candidates, pair_rejections = typed_event_pair_queue(
        local_contracts, design, event_limit=event_limit,
        max_pair_evaluations=max(0, int(req.get("compact_pair_evaluation_budget", 12_000))),
    )
    excluded_keys = {str(item) for item in req.get("runtime_excluded_composition_context_keys", [])}
    excluded_event_pairs = {
        (str(item[0]), str(item[1]), str(item[2]), str(item[3]))
        for item in req.get("runtime_excluded_event_pairs", [])
        if isinstance(item, (list, tuple)) and len(item) == 4
    }
    # Build chains on the complete bounded real event-pair pool first.  A
    # previously verified A->B edge may be valid context for a new B->C edge;
    # filtering it before chain construction would incorrectly destroy that
    # real lifecycle evidence.
    chain_audit: dict[str, Any] = {}
    chains = _chain_candidates(
        pair_candidates, max_contracts=min(4, max(3, int(req.get("compact_chain_max_contracts", 4)))),
        max_seed_atoms=max(0, int(req.get("compact_chain_seed_budget", 4_000))),
        max_expansions=max(0, int(req.get("compact_chain_expansion_budget", 12_000))),
        max_candidates=max(0, int(req.get("compact_chain_candidate_budget", 1_024))), audit=chain_audit,
    )
    if excluded_keys or excluded_event_pairs:
        pair_candidates = [
            item for item in pair_candidates
            if item["context_key"] not in excluded_keys
            and (str(item["source"]["contract_id"]), str(item["event_pairs"][0]["source_event_id"]),
                 str(item["target"]["contract_id"]), str(item["event_pairs"][0]["target_event_id"])) not in excluded_event_pairs
        ]
        chains = [item for item in chains if item["context_key"] not in excluded_keys]
    budget = _initial_context_budget(local_contracts, config)
    selected = _select_contexts(pair_candidates, chains, budget["effective_context_budget"])
    contracts_by_id = {item["contract_id"]: item for item in local_contracts.get("contracts", [])}
    calls, context_audit = [], []
    attempts = int(config.get("design_flow", {}).get("llm_validation_attempts", 4))
    maximum_delay = _formal_or_req(config, "maximum_composition_delay", 96)

    def write_audit(*, status: str | None = None, error: str | None = None) -> dict[str, Any]:
        llm_records = [item.get("llm", {}) for item in context_audit if isinstance(item.get("llm"), dict)]
        audit = {
            "schema": SCHEMA, "budget": budget,
            "pair_candidates": len(pair_candidates), "chain_candidates": len(chains), "contexts_selected": len(selected),
            "excluded_prior_context_keys": len(excluded_keys), "excluded_prior_event_pairs": len(excluded_event_pairs),
            "chain_enumeration": chain_audit,
            "pair_rejections": pair_rejections, "calls": context_audit,
            "call_statuses": dict(Counter(item["status"] for item in context_audit)), "merge": _merge_calls(calls)[1],
            "api_calls_this_run": sum(int(item.get("api_calls_this_run", 0)) for item in llm_records),
            "real_response_artifacts": sum(int(item.get("real_response_artifacts", 0)) for item in llm_records),
            "response_models": sorted({model for item in llm_records for model in item.get("response_models", [])}),
            "llm_generates_sva": False,
        }
        if status:
            audit["status"] = status
        if error:
            audit["error"] = error
        dump_json(output / "composition_context_audit.json", audit)
        return audit

    for index, selected_item in enumerate(selected, 1):
        context = _pair_context(selected_item["candidate"]) if selected_item["kind"] == "PAIR" else _chain_context(selected_item["candidate"], contracts_by_id)
        context, packaging = _with_bounded_spec(context, selected_spec, max_chars)
        record: dict[str, Any] = {
            "index": index, "kind": selected_item["kind"], "context_key": selected_item["candidate"]["context_key"],
            "status": "NOT_REQUESTED", "packaging": packaging,
        }
        if context is None:
            record["status"] = "EXCLUDED_OVERSIZED_OR_NO_SPEC"
            context_audit.append(record)
            continue
        dump_json(output / "contexts" / f"context_{index:03d}.json", context)
        try:
            validated, llm_record = _validated_llm_constraints(
                client, prompt, context, output / "calls" / f"call_{index:03d}.json",
                attempts=attempts, maximum_delay=maximum_delay,
            )
            filtered, filter_audit = _filter_validated_to_context(validated, context)
            record.update(status="VALIDATED" if filtered["constraints"] else "VALIDATED_EMPTY", llm=llm_record, filter=filter_audit)
            calls.append({"validated": filtered, "record": record})
        except LLMUnavailableError as exc:
            record.update(status="INTERRUPTED_EXTERNAL_SERVICE", error=f"{type(exc).__name__}: {exc}")
            context_audit.append(record)
            audit = write_audit(status="INTERRUPTED_EXTERNAL_SERVICE", error=record["error"])
            dump_json(output / "external_service_failure.json", {
                "schema": SCHEMA, "status": "INTERRUPTED_EXTERNAL_SERVICE",
                "context_key": record["context_key"], "error": record["error"], "audit": str(output / "composition_context_audit.json"),
            })
            raise
        except Exception as exc:
            record.update(status="REJECTED", error=f"{type(exc).__name__}: {exc}")
        context_audit.append(record)
    merged, merge_audit = _merge_calls(calls)
    audit = write_audit()
    # Avoid recomputing a different merge audit in a normal completion path.
    audit["merge"] = merge_audit
    dump_json(output / "composition_context_audit.json", audit)
    dump_json(output / "typed_event_pair_candidates.json", [{
        "context_key": item["context_key"], "source_contract_id": item["source"]["contract_id"],
        "target_contract_id": item["target"]["contract_id"], "shared_interface_signals": item["relation"]["shared_interface_signals"],
        "event_pairs": [{key: pair[key] for key in ("source_event_id", "target_event_id")} for pair in item["event_pairs"]],
    } for item in pair_candidates])
    dump_json(output / "validated_constraints.json", merged)
    return merged, audit
