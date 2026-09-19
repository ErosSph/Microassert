"""Generic execution-context and minimal-Formal machinery for Req. 8.6.

This module intentionally contains no design-name or signal-name policy.  It
operates on grounded region activations, typed semantic edges, recovered RTL
state/configuration facts, and optional SPEC phase annotations.  Static facts
may prune search; only Formal results can validate dynamic execution.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import json
import re
from typing import Any

from dateassertion.ir.schema import ObjectType, PropertyIR
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


CONTEXT_RESULTS = {"COMPATIBLE", "INCOMPATIBLE", "UNKNOWN"}
CONTEXT_STRENGTHS = {"STRONG", "COMPATIBLE", "WEAK", "UNKNOWN"}
_STATE_EQ = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_$]*)\s*==\?\s*"
    r"([A-Za-z_][A-Za-z0-9_$]*|(?:\d+)?'[bodh][0-9a-fA-F_xzXZ]+|\d+)"
)


def _digest(*parts: Any, length: int = 12) -> str:
    return hashlib.sha256("|".join(str(item) for item in parts).encode()).hexdigest()[:length]


def _norm(expression: str) -> str:
    return re.sub(r"\s+", "", expression or "")


def _state_atoms(expression: str) -> dict[str, list[str]]:
    values: dict[str, set[str]] = defaultdict(set)
    for signal, value in _STATE_EQ.findall(expression or ""):
        values[signal].add(value)
    return {key: sorted(items) for key, items in sorted(values.items())}


def _boolean_atoms(expression: str, names: set[str]) -> dict[str, list[bool]]:
    """Extract only unambiguous unary Boolean atoms.

    Compound Boolean reasoning is deliberately left UNKNOWN.  This prevents a
    weak textual parser from inventing an incompatibility.
    """

    result: dict[str, set[bool]] = defaultdict(set)
    for name in names:
        token = re.escape(name)
        if re.search(rf"(?<![A-Za-z0-9_$!]){token}(?![A-Za-z0-9_$])", expression or ""):
            result[name].add(True)
        if re.search(rf"!\s*{token}(?![A-Za-z0-9_$])", expression or ""):
            result[name].add(False)
    return {key: sorted(items) for key, items in sorted(result.items())}


def _assignment_evidence(design: RTLDesign, module: str, signals: set[str]) -> list[dict[str, Any]]:
    records = []
    for index, item in enumerate(design.assignments, start=1):
        if item.module != module:
            continue
        used = expression_signals(item.rhs) | expression_signals(item.guard) | {item.lhs}
        overlap = sorted(signals & used)
        if not overlap:
            continue
        records.append({
            "assignment_id": f"assignment:{index}", "kind": item.kind,
            "lhs": item.lhs, "rhs": item.rhs, "guard": item.guard,
            "signals": overlap, "file": item.file, "line": item.line,
        })
    return records


def build_execution_context_ir(
    annotated_graph: dict[str, Any], design: RTLDesign, *, reset: str = "resetn",
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Ground one lightweight execution context for every region event."""

    events = []
    contexts = []
    for region in annotated_graph.get("nodes", []):
        activation = region.get("activation", {})
        predicate = str(activation.get("predicate", ""))
        module = region["module"]
        table = design.module_signals.get(module, {})
        runtime = {
            name for name in expression_signals(predicate)
            if name != reset and name in table and table[name].direction != "constant"
        }
        boundary = {name for name in region.get("boundary_signals", []) if name in table}
        relevant = runtime | boundary | ({activation.get("target")} - {None, ""})
        assignments = _assignment_evidence(design, module, relevant)
        registered = sorted({
            item["lhs"] for item in assignments
            if item["kind"] == "nonblocking" and item["lhs"] in relevant
        })
        feedback = sorted({
            item["lhs"] for item in assignments
            if item["kind"] == "nonblocking"
            and item["lhs"] in (expression_signals(item["rhs"]) | expression_signals(item["guard"]))
        })
        payload = sorted({
            name for name in relevant
            if name in table and bool(table[name].width)
        })
        constants = {
            name for name, signal in table.items() if signal.direction == "constant"
        }
        phases = deepcopy(region.get("microarchitecture_phases", []))
        event_id = "event_" + _digest(region["region_id"], predicate)
        state_context = _state_atoms(predicate)
        structural_facts = []
        if state_context:
            structural_facts.append("explicit_state_selector")
        if registered:
            structural_facts.append("registered_context")
        if feedback:
            structural_facts.append("registered_lifetime_feedback")
        if phases:
            structural_facts.append("spec_phase_context")
        if payload:
            structural_facts.append("data_identity_candidate")
        if activation.get("status") == "GROUNDED" and len(structural_facts) >= 2:
            strength = "STRONG"
        elif activation.get("status") == "GROUNDED" and structural_facts:
            strength = "COMPATIBLE"
        elif activation.get("status") == "GROUNDED":
            strength = "WEAK"
        else:
            strength = "UNKNOWN"
        context_id = "context_" + _digest(
            module, predicate, json.dumps(state_context, sort_keys=True),
            json.dumps(phases, sort_keys=True),
        )
        event = {
            "event_id": event_id, "region_id": region["region_id"],
            "module": module, "kind": region.get("kind"),
            "activation": deepcopy(activation), "context_id": context_id,
            "rtl_evidence": {
                "core_node_ids": region.get("core_node_ids", []),
                "boundary_signals": sorted(boundary),
                "assignments": assignments,
            },
        }
        context = {
            "context_id": context_id, "event_id": event_id,
            "region_id": region["region_id"], "module": module,
            "activation": predicate,
            "control_context": {
                "runtime_signals": sorted(runtime),
                "operation_select_predicate": predicate,
            },
            "state_context": state_context,
            "transaction_context": {
                "registered_signals": registered,
                "registered_lifetime_signals": feedback,
                "spec_phases": phases,
            },
            "data_context": {
                "payload_or_data_signals": payload,
                "activation_target": activation.get("target", ""),
            },
            "reset_flush_context": {
                "reset_signal": reset,
                "reset_excluded_by_property": True,
                "flush_or_cancel_evidence": [],
            },
            "stable_configuration": _boolean_atoms(predicate, constants),
            "context_strength": strength,
            "evidence": structural_facts,
        }
        events.append(event)
        contexts.append(context)
    return (
        {
            "schema": "region_flow.6-region-events.v1", "events": events,
            "summary": {"events": len(events), "grounded": sum(
                item["activation"].get("status") == "GROUNDED" for item in events
            )},
        },
        {
            "schema": "region_flow.6-execution-contexts.v1", "contexts": contexts,
            "summary": {"contexts": len(contexts), "by_strength": dict(Counter(
                item["context_strength"] for item in contexts
            ))},
            "policy": {
                "evidence_only": True, "missing_context_is_not_guessed": True,
                "llm_may_explain_but_not_decide_compatibility": True,
            },
        },
    )


def check_context_compatibility(
    path_regions: list[str], context_by_region: dict[str, dict[str, Any]],
    edge_by_pair: dict[tuple[str, str], dict[str, Any]],
) -> dict[str, Any]:
    """Check state/configuration/transaction compatibility for a partial path."""

    contexts = [context_by_region[item] for item in path_regions]
    evidence: list[dict[str, Any]] = []
    reasons: list[str] = []
    if len({item["module"] for item in contexts}) != 1:
        return {"status": "INCOMPATIBLE", "context_strength": "UNKNOWN",
                "reason": "cross_module_without_transaction_binding", "evidence": []}
    constants: dict[str, set[bool]] = defaultdict(set)
    for context in contexts:
        for name, values in context.get("stable_configuration", {}).items():
            constants[name].update(values)
    contradictions = sorted(name for name, values in constants.items() if values == {False, True})
    if contradictions:
        return {"status": "INCOMPATIBLE", "context_strength": "UNKNOWN",
                "reason": "stable_configuration_contradiction",
                "evidence": [{"parameters": contradictions}]}

    link_strengths = []
    for left, right in zip(path_regions, path_regions[1:]):
        edge = edge_by_pair.get((left, right))
        if edge is None:
            return {"status": "INCOMPATIBLE", "context_strength": "UNKNOWN",
                    "reason": "missing_directed_region_edge", "evidence": []}
        status = edge.get("ordering_constraint", "UNKNOWN")
        if status == "DISALLOW":
            return {"status": "INCOMPATIBLE", "context_strength": "UNKNOWN",
                    "reason": "ordering_constraint_disallow",
                    "evidence": [{"edge_id": edge.get("edge_id"), "constraint": status}]}
        records = edge.get("constraint_evidence", [])
        causal = [item for item in records if item.get("reason") in {
            "bounded_activation_dependency", "fsm_state_reachable", "nondecreasing_spec_phase",
            "shared_runtime_execution_context",
        } and item.get("status") == "ALLOW"]
        evidence.append({
            "edge_id": edge.get("edge_id"), "ordering_constraint": status,
            "same_execution_evidence": causal,
        })
        causal_reasons = {item.get("reason") for item in causal}
        if "bounded_activation_dependency" in causal_reasons and (
            "fsm_state_reachable" in causal_reasons or "nondecreasing_spec_phase" in causal_reasons
        ):
            link_strengths.append("STRONG")
        elif causal and status == "ALLOW":
            link_strengths.append("COMPATIBLE")
        elif status == "ALLOW":
            link_strengths.append("WEAK")
            reasons.append("allow_without_same_execution_evidence")
        else:
            link_strengths.append("UNKNOWN")
            reasons.append("unresolved_dynamic_relation")
    if not link_strengths:
        strength, status = "UNKNOWN", "UNKNOWN"
    elif all(item == "STRONG" for item in link_strengths):
        strength, status = "STRONG", "COMPATIBLE"
    elif all(item in {"STRONG", "COMPATIBLE"} for item in link_strengths):
        strength, status = "COMPATIBLE", "COMPATIBLE"
    elif any(item == "UNKNOWN" for item in link_strengths):
        strength, status = "UNKNOWN", "UNKNOWN"
    else:
        strength, status = "WEAK", "COMPATIBLE"
    assert status in CONTEXT_RESULTS and strength in CONTEXT_STRENGTHS
    return {
        "status": status, "context_strength": strength,
        "reason": ",".join(sorted(set(reasons))) or "evidence_compatible",
        "link_strengths": link_strengths, "evidence": evidence,
        "checks": {
            "state_compatibility": "EVIDENCE_DRIVEN",
            "control_compatibility": "EVIDENCE_DRIVEN",
            "transaction_compatibility": strength,
            "operation_compatibility": "NO_STABLE_CONTRADICTION",
            "reset_flush_compatibility": "RESET_EXCLUDED_NO_FLUSH_EVIDENCE",
            "stable_configuration_compatibility": "COMPATIBLE",
        },
    }


def constraint_aware_search(
    annotated_graph: dict[str, Any], contexts_doc: dict[str, Any], *,
    min_regions: int = 2, max_regions: int = 4, scalable_budget_per_module: int = 8,
    include_weak_probe: bool = True,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Enumerate only constraint-consistent branches using bounded DFS.

    Unlike Req. 8.5.1 this routine checks an edge and the partial execution
    context *before* descending.  Activation-equivalent Req. 8.4 aliases are
    canonicalised at the event boundary to keep bounded completeness useful.
    """

    nodes = {item["region_id"]: item for item in annotated_graph.get("nodes", [])}
    contexts = {item["region_id"]: item for item in contexts_doc.get("contexts", [])}
    # Pick the strongest encoding for each directed activation-event pair.
    best: dict[tuple[str, str], dict[str, Any]] = {}
    rank = {"ALLOW": 2, "UNKNOWN": 1, "DISALLOW": 0}
    for edge in annotated_graph.get("edges", []):
        if edge.get("scope") != "CROSS_REGION_INTRA_MODULE":
            continue
        left, right = edge["source_region"], edge["target_region"]
        if left not in nodes or right not in nodes:
            continue
        key = (_norm(nodes[left]["activation"]["predicate"]), _norm(nodes[right]["activation"]["predicate"]))
        if key[0] == key[1]:
            continue
        current = best.get(key)
        edge_rank = (rank.get(edge.get("ordering_constraint"), -1),
                     float(edge.get("constraint_confidence", 0)),
                     float(edge.get("normalized_structural_similarity", 0)))
        current_rank = (-1, -1.0, -1.0) if current is None else (
            rank.get(current.get("ordering_constraint"), -1),
            float(current.get("constraint_confidence", 0)),
            float(current.get("normalized_structural_similarity", 0)),
        )
        if current is None or edge_rank > current_rank:
            best[key] = edge
    outgoing: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for edge in best.values():
        outgoing[edge["source_region"]].append(edge)
    for source in outgoing:
        outgoing[source].sort(key=lambda item: (
            -rank.get(item.get("ordering_constraint"), 0),
            -float(item.get("constraint_confidence", 0)), item["edge_id"],
        ))

    search_states = 0
    pruned_constraint = 0
    pruned_context = 0
    pruned_cycle = 0
    all_paths: list[dict[str, Any]] = []
    decisions: list[dict[str, Any]] = []

    def emit(regions: list[str], edges: list[dict[str, Any]], compatibility: dict[str, Any]) -> None:
        records = [nodes[item] for item in regions]
        predicates = [item["activation"]["predicate"] for item in records]
        path_id = "req86_path_" + _digest(*regions, *(item["edge_id"] for item in edges))
        score = (
            sum(float(item.get("constraint_confidence", 0)) for item in edges) / len(edges)
            + len(set(item.get("kind") for item in records)) / len(records)
            + {"STRONG": 1.0, "COMPATIBLE": 0.7, "WEAK": 0.2, "UNKNOWN": 0.0}[
                compatibility["context_strength"]
            ]
        ) / 3.0
        all_paths.append({
            "path_id": path_id, "module": records[0]["module"],
            "regions": regions, "region_events": [
                "event_" + _digest(item["region_id"], item["activation"]["predicate"]) for item in records
            ],
            "region_kinds": [item.get("kind") for item in records],
            "region_edges": [item["edge_id"] for item in edges],
            "edge_types": [item.get("edge_type") for item in edges],
            "activation_predicates": predicates,
            "execution_context": compatibility,
            "context_strength": compatibility["context_strength"],
            "constraint_evidence": [item.get("constraint_evidence", []) for item in edges],
            "constraint_statuses": [item.get("ordering_constraint", "UNKNOWN") for item in edges],
            "semantic_path_length": len(regions),
            "search_score": round(score, 6),
            "joint_path_result": "NOT_QUERIED",
            "validation_status": "CANDIDATE",
        })

    def walk(regions: list[str], edges: list[dict[str, Any]]) -> None:
        nonlocal search_states, pruned_constraint, pruned_context, pruned_cycle
        if len(regions) >= max_regions:
            return
        tail = regions[-1]
        seen_events = {_norm(nodes[item]["activation"]["predicate"]) for item in regions}
        for edge in outgoing.get(tail, []):
            search_states += 1
            target = edge["target_region"]
            if _norm(nodes[target]["activation"]["predicate"]) in seen_events:
                pruned_cycle += 1
                continue
            if edge.get("ordering_constraint") == "DISALLOW":
                pruned_constraint += 1
                decisions.append({"edge_id": edge["edge_id"], "decision": "PRUNE_BRANCH",
                                  "reason": "ordering_constraint_disallow", "prefix": regions})
                continue
            new_regions = regions + [target]
            compatibility = check_context_compatibility(new_regions, contexts, {
                (item["source_region"], item["target_region"]): item for item in best.values()
            })
            if compatibility["status"] == "INCOMPATIBLE":
                pruned_context += 1
                decisions.append({"edge_id": edge["edge_id"], "decision": "PRUNE_BRANCH",
                                  "reason": compatibility["reason"], "prefix": new_regions})
                continue
            emit(new_regions, edges + [edge], compatibility)
            walk(new_regions, edges + [edge])

    # All canonical events may form an adjacent path.  Longer paths naturally
    # continue only from directed, context-compatible prefixes.
    for source in sorted(outgoing):
        walk([source], [])

    unique: dict[tuple[str, tuple[str, ...]], dict[str, Any]] = {}
    for path in all_paths:
        key = (path["module"], tuple(_norm(item) for item in path["activation_predicates"]))
        current = unique.get(key)
        if current is None or path["search_score"] > current["search_score"]:
            unique[key] = path
    complete = sorted(unique.values(), key=lambda item: (
        item["module"], -item["search_score"], -len(item["regions"]), item["path_id"]
    ))
    eligible = [item for item in complete if item["context_strength"] in {"STRONG", "COMPATIBLE"}]
    if include_weak_probe:
        weak = [item for item in complete if item["context_strength"] == "WEAK"]
    else:
        weak = []
    by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for item in eligible:
        by_module[item["module"]].append(item)
    scalable = []
    for module, items in sorted(by_module.items()):
        # Preserve at least one multi-region candidate when available.
        ranked = sorted(items, key=lambda item: (
            len(item["regions"]) < 3, -item["search_score"], -len(item["regions"]), item["path_id"]
        ))
        scalable.extend(ranked[:scalable_budget_per_module])
    result = {
        "schema": "region_flow.6-constraint-aware-search.v1",
        "paths": scalable,
        "summary": {
            "raw_search_states": search_states,
            "constraint_pruned_branches": pruned_constraint,
            "context_pruned_branches": pruned_context,
            "cycle_pruned_branches": pruned_cycle,
            "constraint_consistent_candidates": len(complete),
            "eligible_candidates": len(eligible),
            "weak_probe_candidates": len(weak),
            "formal_candidate_paths": len(scalable),
            "by_module": dict(Counter(item["module"] for item in scalable)),
        },
        "policy": {
            "constraint_checked_before_descending": True,
            "context_checked_before_descending": True,
            "semantic_path_bound": max_regions,
            "cycle_count_is_path_length": False,
            "formal_is_not_search_engine": True,
        },
    }
    completeness = {
        "schema": "region_flow.6-bounded-completeness.v1",
        "mode": "BOUNDED_COMPLETENESS",
        "region_set": sorted(nodes), "maximum_semantic_path_length": max_regions,
        "constraint_consistent_candidates": complete,
        "progressive_widening": [
            {"batch": index // max(1, scalable_budget_per_module) + 1,
             "path_ids": [item["path_id"] for item in complete[index:index + max(1, scalable_budget_per_module)]]}
            for index in range(0, len(complete), max(1, scalable_budget_per_module))
        ],
        "enumeration_complete": True,
        "claim_scope": (
            "all canonical activation-event paths in the given Region Set, Execution Context, "
            f"Constraint Set, and semantic length <= {max_regions}; not all CPU micro-paths"
        ),
    }
    pruning = {
        "schema": "region_flow.6-path-pruning-decisions.v1",
        "decisions": decisions,
        "summary": result["summary"],
    }
    return result, completeness, pruning


def _query_property(
    query_id: str, module: str, body: str, signals: set[str], reset_asserted: str,
    query_type: str,
) -> PropertyIR:
    return PropertyIR(
        property_id=query_id, region_id=query_id, object_type=ObjectType.EXTENSION,
        family=f"REQ86_{query_type}", template="FUNCTIONAL_PATH_QUERY", bindings={},
        signals=sorted(signals), source="req8.6-minimal-formal-primitive",
        llm_confidence=0.0, body=body, disable_iff=reset_asserted,
        description=f"Req8.6 {query_type}; Formal is the execution oracle.",
        source_classification="RTL_STRUCTURAL", target_module=module,
    )


def build_minimal_formal_queries(
    candidate_doc: dict[str, Any], annotated_graph: dict[str, Any], *,
    reset_asserted: str = "!resetn", ordering_bound: int = 48,
    strengthening_limit: int = 8, exclusivity_limit: int = 4,
) -> tuple[list[PropertyIR], dict[str, dict[str, Any]]]:
    """Create the three mandatory primitives plus selective strengthening."""

    nodes = {item["region_id"]: item for item in annotated_graph.get("nodes", [])}
    edges = {item["edge_id"]: item for item in annotated_graph.get("edges", [])}
    properties: list[PropertyIR] = []
    metadata: dict[str, dict[str, Any]] = {}
    seen: set[tuple[Any, ...]] = set()

    def add(query_type: str, module: str, body: str, signals: set[str], meta: dict[str, Any], key: tuple[Any, ...]) -> None:
        if key in seen:
            return
        seen.add(key)
        query_id = "req86_" + query_type.lower() + "_" + _digest(*key)
        properties.append(_query_property(query_id, module, body, signals, reset_asserted, query_type))
        metadata[query_id] = {"query_id": query_id, "query_type": query_type, **meta,
                              "retry_count": 0, "eventual_usefulness": "PENDING"}

    paths = candidate_doc.get("paths", [])
    for path in paths:
        for region_id, event_id, activation in zip(
            path["regions"], path["region_events"], path["activation_predicates"]
        ):
            add("REGION_REACHABILITY", path["module"], f"({activation}) |-> 1'b1",
                expression_signals(activation), {
                    "region": region_id, "region_event": event_id,
                    "execution_context": nodes[region_id].get("activation", {}),
                    "path_ids": [path["path_id"]],
                }, ("REGION_REACHABILITY", path["module"], event_id, _norm(activation)))
        for index, edge_id in enumerate(path["region_edges"]):
            edge = edges[edge_id]
            if edge.get("ordering_constraint") != "UNKNOWN":
                continue
            left, right = path["activation_predicates"][index:index + 2]
            add("ORDERED_COREACHABILITY", path["module"],
                f"(({left}) ##[0:{ordering_bound}] ({right})) |-> 1'b1",
                expression_signals(left) | expression_signals(right), {
                    "source_event": path["region_events"][index],
                    "target_event": path["region_events"][index + 1],
                    "static_relation": edge.get("edge_type"),
                    "constraint_status": "UNKNOWN", "bound": ordering_bound,
                    "path_ids": [path["path_id"]],
                }, ("ORDERED_COREACHABILITY", path["module"], edge_id))
        if len(path["regions"]) >= 3 and path["context_strength"] in {"STRONG", "COMPATIBLE"}:
            sequence = f") ##[0:{ordering_bound}] (".join(path["activation_predicates"])
            body = f"((({sequence}))) |-> 1'b1"
            add("JOINT_PATH_REACHABILITY", path["module"], body,
                set().union(*(expression_signals(item) for item in path["activation_predicates"])), {
                    "path_id": path["path_id"], "regions": path["regions"],
                    "region_events": path["region_events"], "context_strength": path["context_strength"],
                    "partial_order_bound_per_edge": ordering_bound,
                }, ("JOINT_PATH_REACHABILITY", path["module"], path["path_id"]))

    # Strengthening is deliberately path-selective, never all-pair.  Bounded
    # dominance is preferred for composition because it proves that a terminal
    # event belongs to a prior path start without assuming unconditional liveness.
    ranked_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for item in paths:
        if len(item["regions"]) >= 3 and item["context_strength"] in {"STRONG", "COMPATIBLE"}:
            ranked_by_module[item["module"]].append(item)
    for module, items in list(ranked_by_module.items()):
        by_length: dict[int, list[dict[str, Any]]] = defaultdict(list)
        for item in items:
            by_length[len(item["regions"])].append(item)
        for length in by_length:
            by_length[length].sort(key=lambda item: (-item["search_score"], item["path_id"]))
        diversified: list[dict[str, Any]] = []
        while any(by_length.values()):
            for length in sorted(by_length, reverse=True):
                if by_length[length]:
                    diversified.append(by_length[length].pop(0))
        ranked_by_module[module] = diversified
    # A global score can let one large module consume the entire strengthening
    # budget.  Round-robin is a bounded structural-diversity policy, not a
    # design-specific rule.
    long_paths: list[dict[str, Any]] = []
    while len(long_paths) < strengthening_limit and any(ranked_by_module.values()):
        for module in sorted(ranked_by_module):
            if ranked_by_module[module] and len(long_paths) < strengthening_limit:
                long_paths.append(ranked_by_module[module].pop(0))
    for path in long_paths:
        first, last = path["activation_predicates"][0], path["activation_predicates"][-1]
        history = " || ".join([f"({first})"] + [
            f"$past(({first}), {delay})" for delay in range(1, ordering_bound + 1)
        ])
        add("SELECTIVE_DOMINANCE", path["module"], f"({last}) |-> ({history})",
            expression_signals(first) | expression_signals(last), {
                "path_id": path["path_id"], "regions": path["regions"],
                "selection_reason": "strong_multi_region_composition_prerequisite",
                "bound": ordering_bound,
            }, ("SELECTIVE_DOMINANCE", path["module"], path["path_id"]))

    # Exclusivity appears only at an actual fork and is capped independently.
    fork_targets: dict[tuple[str, str], list[tuple[dict[str, Any], str]]] = defaultdict(list)
    for path in paths:
        if len(path["regions"]) != 2:
            continue
        fork_targets[(path["module"], path["region_events"][0])].append((path, path["activation_predicates"][1]))
    count = 0
    for (module, source_event), targets in sorted(fork_targets.items()):
        distinct = {}
        for path, predicate in targets:
            distinct.setdefault(_norm(predicate), (path, predicate))
        values = list(distinct.values())
        if len(values) < 2:
            continue
        for index in range(len(values) - 1):
            if count >= exclusivity_limit:
                break
            left_path, left = values[index]
            right_path, right = values[index + 1]
            add("BRANCH_EXCLUSIVITY", module, f"!(({left}) && ({right}))",
                expression_signals(left) | expression_signals(right), {
                    "source_event": source_event,
                    "left_target_event": left_path["region_events"][1],
                    "right_target_event": right_path["region_events"][1],
                    "selection_reason": "observed_region_graph_fork",
                }, ("BRANCH_EXCLUSIVITY", module, source_event,
                    left_path["region_events"][1], right_path["region_events"][1]))
            count += 1
    return properties, metadata


def build_progressive_widening_queries(
    bounded_completeness: dict[str, Any], annotated_graph: dict[str, Any], *,
    target_modules: set[str], excluded_path_ids: set[str] | None = None,
    reset_asserted: str = "!resetn", ordering_bound: int = 48,
    limit_per_module: int = 16,
) -> tuple[dict[str, Any], list[PropertyIR], dict[str, dict[str, Any]]]:
    """Widen after a module has Joint paths but no trusted composition.

    Selection is generic: three-event paths, grounded UPDATE entry event, an
    FSM event, compatible execution context, and structural diversity.  The
    strengthening property mentions *every* event in order; it is not an
    endpoint property relabelled as Intermediate.
    """

    nodes = {item["region_id"]: item for item in annotated_graph.get("nodes", [])}
    excluded = excluded_path_ids or set()
    by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for path in bounded_completeness.get("constraint_consistent_candidates", []):
        if path["path_id"] in excluded or path["module"] not in target_modules:
            continue
        if len(path["regions"]) != 3 or "FSM" not in path["region_kinds"]:
            continue
        if path["context_strength"] not in {"STRONG", "COMPATIBLE"}:
            continue
        source = nodes[path["regions"][0]].get("activation", {})
        if source.get("status") != "GROUNDED" or source.get("role") != "UPDATE":
            continue
        by_module[path["module"]].append(path)

    selected = []
    for module, paths in sorted(by_module.items()):
        # Round-robin by kind signature prevents one overlapping Req8.4
        # encoding from consuming the widening budget.
        by_signature: dict[tuple[str, ...], list[dict[str, Any]]] = defaultdict(list)
        for path in paths:
            by_signature[tuple(path["region_kinds"])].append(path)
        for signature in by_signature:
            by_signature[signature].sort(key=lambda item: (-item["search_score"], item["path_id"]))
        module_selected = []
        while len(module_selected) < limit_per_module and any(by_signature.values()):
            for signature in sorted(by_signature):
                if by_signature[signature] and len(module_selected) < limit_per_module:
                    module_selected.append(by_signature[signature].pop(0))
        selected.extend(module_selected)

    properties: list[PropertyIR] = []
    metadata: dict[str, dict[str, Any]] = {}
    for path in selected:
        sequence = f") ##[0:{ordering_bound}] (".join(path["activation_predicates"])
        joint_id = "req86_widen_joint_" + _digest(path["path_id"])
        joint_body = f"((({sequence}))) |-> 1'b1"
        properties.append(_query_property(
            joint_id, path["module"], joint_body,
            set().union(*(expression_signals(item) for item in path["activation_predicates"])),
            reset_asserted, "JOINT_PATH_REACHABILITY",
        ))
        metadata[joint_id] = {
            "query_id": joint_id, "query_type": "JOINT_PATH_REACHABILITY",
            "path_id": path["path_id"], "regions": path["regions"],
            "region_events": path["region_events"], "context_strength": path["context_strength"],
            "partial_order_bound_per_edge": ordering_bound,
            "selection_reason": "progressive_widening_missing_trusted_composition",
            "retry_count": 0, "eventual_usefulness": "PENDING",
        }
        progress_id = "req86_widen_progress_" + _digest(path["path_id"])
        tail = f") ##[0:{ordering_bound}] (".join(path["activation_predicates"][1:])
        # At least one cycle separates the entry update from the first sampled
        # post-entry state.  Later semantic events may coincide in a cycle.
        progress_body = (
            f"({path['activation_predicates'][0]}) |-> "
            f"##[1:{ordering_bound}] (({tail}))"
        )
        properties.append(_query_property(
            progress_id, path["module"], progress_body,
            set().union(*(expression_signals(item) for item in path["activation_predicates"])),
            reset_asserted, "COMPOSITIONAL_PROGRESS",
        ))
        metadata[progress_id] = {
            "query_id": progress_id, "query_type": "COMPOSITIONAL_PROGRESS",
            "path_id": path["path_id"], "regions": path["regions"],
            "region_events": path["region_events"], "bound": ordering_bound,
            "selection_reason": "three_event_progressive_widening",
            "all_path_events_in_property": True, "retry_count": 0,
            "eventual_usefulness": "PENDING",
        }
    return {
        "schema": "region_flow.6-progressive-widening-candidates.v1",
        "paths": selected,
        "summary": {"target_modules": sorted(target_modules), "selected_paths": len(selected),
                    "queries": len(properties), "limit_per_module": limit_per_module},
    }, properties, metadata


def analyze_same_transaction_gates(
    bounded_completeness: dict[str, Any], annotated_graph: dict[str, Any],
    constraint_graph: dict[str, Any],
) -> dict[str, Any]:
    """Audit lifecycle coverage for every optional protocol/spec chain."""

    nodes = {item["region_id"]: item for item in annotated_graph.get("nodes", [])}
    analyses = []
    for chain in constraint_graph.get("spec_chains", []):
        phase_names = [item["name"] for item in chain.get("phases", [])]
        last_rank = len(phase_names) - 1
        records = []
        for path in bounded_completeness.get("constraint_consistent_candidates", []):
            matches = []
            for region in path["regions"]:
                matches.extend(
                    item for item in nodes[region].get("microarchitecture_phases", [])
                    if item.get("chain_id") == chain.get("chain_id")
                )
            if not matches:
                continue
            ranks = [int(item["rank"]) for item in matches]
            complete = bool(ranks and min(ranks) == 0 and max(ranks) == last_rank and last_rank > 0)
            monotonic = ranks == sorted(ranks)
            records.append({
                "path_id": path["path_id"], "module": path["module"],
                "phase_ranks": ranks, "phases": [item["phase"] for item in matches],
                "context_strength": path["context_strength"],
                "complete_lifecycle": complete, "monotonic_lifecycle": monotonic,
                "same_transaction_gate": (
                    "ELIGIBLE" if complete and monotonic
                    and path["context_strength"] in {"STRONG", "COMPATIBLE"}
                    else "INSUFFICIENT_LIFECYCLE_CONTEXT"
                ),
            })
        eligible = sum(item["same_transaction_gate"] == "ELIGIBLE" for item in records)
        analyses.append({
            "chain_id": chain.get("chain_id"), "module_selector": chain.get("module", "*"),
            "phase_names": phase_names, "candidate_paths_with_chain_context": len(records),
            "complete_lifecycle_paths": sum(item["complete_lifecycle"] for item in records),
            "same_transaction_eligible_paths": eligible,
            "gate_result": "ELIGIBLE_PATHS_PRESENT" if eligible else "NO_COMPLETE_LIFECYCLE_CONTEXT",
            "explanation": (
                "At least one bounded path spans all ordered lifecycle phases with compatible context."
                if eligible else
                "No bounded path spans both lifecycle endpoints with compatible monotonic context; "
                "the protocol must not be composed from request-only or completion-only evidence."
            ),
            "records": records,
        })
    return {
        "schema": "region_flow.6-same-transaction-gates.v1",
        "chains": analyses,
        "summary": {
            "chains": len(analyses),
            "chains_with_eligible_paths": sum(item["same_transaction_eligible_paths"] > 0 for item in analyses),
            "chains_without_complete_context": sum(item["gate_result"] == "NO_COMPLETE_LIFECYCLE_CONTEXT"
                                                    for item in analyses),
        },
        "policy": {
            "adjacent_pass_is_not_same_transaction": True,
            "weak_or_incomplete_lifecycle_cannot_form_end_to_end_contract": True,
        },
    }


def cache_key(meta: dict[str, Any], formal_config: dict[str, Any]) -> str:
    stable_config = {
        key: formal_config.get(key) for key in (
            "tool", "executable", "prove_time_limit", "engine_mode", "clock", "reset",
        )
    }
    return hashlib.sha256(json.dumps({
        "region_event": meta.get("region_event"),
        "execution_context": meta.get("execution_context"),
        "formal_config": stable_config,
    }, sort_keys=True, default=str).encode()).hexdigest()
