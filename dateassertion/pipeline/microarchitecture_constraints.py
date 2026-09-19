"""Constraint-guided Functional Region Path search for Requirement 8.5.1.

The optimizer is intentionally split from Formal validation.  It may reject a
path only when an auditable RTL or optional SPEC ordering rule says that an
edge is impossible.  An ``ALLOW`` annotation is a search hint, never proof of
dynamic execution; JasperGold remains the trust oracle.
"""

from __future__ import annotations

from collections import Counter, defaultdict, deque
from copy import deepcopy
import fnmatch
import hashlib
import re
from typing import Any

from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


ORDERING_VALUES = {"ALLOW", "DISALLOW", "UNKNOWN"}
_STATE_EQ = re.compile(
    r"\b([A-Za-z_][A-Za-z0-9_$]*)\s*==\?\s*"
    r"([A-Za-z_][A-Za-z0-9_$]*|(?:\d+)?'[bodh][0-9a-fA-F_xzXZ]+|\d+)"
)
_SIMPLE_VALUE = re.compile(
    r"^\s*([A-Za-z_][A-Za-z0-9_$]*|(?:\d+)?'[bodh][0-9a-fA-F_xzXZ]+|\d+)\s*$"
)


def _normalized(expression: str) -> str:
    return re.sub(r"\s+", "", expression)


def _signal_node(module: str, signal: str) -> str:
    return f"signal:{module}.{signal}"


def _state_atoms(expression: str) -> dict[str, set[str]]:
    result: dict[str, set[str]] = defaultdict(set)
    for signal, value in _STATE_EQ.findall(expression or ""):
        # ``1'b1 ==? predicate`` is a case-equality encoding of a condition,
        # not a state selector.  In that form the literal is on the left and
        # therefore does not match this regex.
        result[signal].add(value)
    return dict(result)


def _runtime_signals(expression: str, design: RTLDesign, module: str, reset: str) -> set[str]:
    table = design.module_signals.get(module, {})
    return {
        name for name in expression_signals(expression)
        if name != reset and table.get(name) is not None
        and table[name].direction != "constant"
    }


def _constant_polarities(expression: str, design: RTLDesign, module: str) -> dict[str, set[bool]]:
    """Extract only unambiguous Boolean parameter literals.

    This deliberately ignores compound terms.  A weak parser must return
    UNKNOWN rather than manufacture a DISALLOW decision.
    """

    result: dict[str, set[bool]] = defaultdict(set)
    constants = {
        name for name, signal in design.module_signals.get(module, {}).items()
        if signal.direction == "constant"
    }
    for name in constants:
        if re.search(rf"(?<![A-Za-z0-9_$!]){re.escape(name)}(?![A-Za-z0-9_$])", expression):
            result[name].add(True)
        if re.search(rf"!\s*{re.escape(name)}(?![A-Za-z0-9_$])", expression):
            result[name].add(False)
    return dict(result)


def derive_fsm_transition_graph(
    design: RTLDesign, *, reset: str = "resetn",
) -> dict[str, Any]:
    """Recover explicit ``state=A`` -> ``state<=B`` RTL transitions."""

    transitions: dict[tuple[str, str], set[tuple[str, str]]] = defaultdict(set)
    evidence: dict[tuple[str, str, str, str], list[dict[str, Any]]] = defaultdict(list)
    for assignment in design.assignments:
        if assignment.kind != "nonblocking":
            continue
        match = _SIMPLE_VALUE.fullmatch(assignment.rhs or "")
        if not match:
            continue
        target_value = match.group(1)
        for state_signal, source_values in _state_atoms(assignment.guard).items():
            if assignment.lhs != state_signal:
                continue
            # Reset-only jumps initialize the FSM; they are not transaction
            # ordering evidence.
            guard_signals = expression_signals(assignment.guard)
            if guard_signals and guard_signals <= {reset}:
                continue
            key = (assignment.module, state_signal)
            for source_value in source_values:
                transitions[key].add((source_value, target_value))
                evidence[(assignment.module, state_signal, source_value, target_value)].append({
                    "file": assignment.file, "line": assignment.line,
                    "guard": assignment.guard, "update": f"{assignment.lhs} <= {assignment.rhs}",
                })
    machines = []
    for (module, state_signal), pairs in sorted(transitions.items()):
        values = sorted({value for pair in pairs for value in pair})
        machines.append({
            "module": module, "state_signal": state_signal, "states": values,
            "transitions": [
                {
                    "source": source, "target": target,
                    "evidence": evidence[(module, state_signal, source, target)],
                }
                for source, target in sorted(pairs)
            ],
        })
    return {
        "schema": "region_flow.5.1-rtl-fsm-constraint-graph.v1",
        "machines": machines,
        "summary": {
            "machines": len(machines),
            "transitions": sum(len(item["transitions"]) for item in machines),
        },
    }


def _fsm_reachability(fsm_doc: dict[str, Any], max_depth: int) -> dict[tuple[str, str], dict[str, set[str]]]:
    result: dict[tuple[str, str], dict[str, set[str]]] = {}
    for machine in fsm_doc.get("machines", []):
        adjacent: dict[str, set[str]] = defaultdict(set)
        for transition in machine["transitions"]:
            adjacent[transition["source"]].add(transition["target"])
        closure: dict[str, set[str]] = {}
        for source in machine["states"]:
            seen = {source}
            frontier = {source}
            for _ in range(max_depth):
                frontier = {target for item in frontier for target in adjacent.get(item, set())} - seen
                if not frontier:
                    break
                seen |= frontier
            closure[source] = seen
        result[(machine["module"], machine["state_signal"])] = closure
    return result


def _semantic_adjacency(graph: dict[str, Any]) -> dict[str, list[tuple[str, str, dict[str, Any]]]]:
    adjacent: dict[str, list[tuple[str, str, dict[str, Any]]]] = defaultdict(list)
    for edge in graph.get("edges", []):
        adjacent[str(edge.get("source", ""))].append((
            str(edge.get("target", "")), str(edge.get("type", "")), edge.get("evidence", {}),
        ))
    return adjacent


def _activation_nodes(region: dict[str, Any]) -> list[str]:
    activation = region.get("activation", {})
    result = []
    if activation.get("assignment_id"):
        result.append(activation["assignment_id"])
    if activation.get("target"):
        result.append(_signal_node(region["module"], activation["target"]))
    return result


def _bounded_semantic_witness(
    source: dict[str, Any], target: dict[str, Any],
    adjacent: dict[str, list[tuple[str, str, dict[str, Any]]]], *, max_depth: int,
) -> list[dict[str, Any]]:
    starts = _activation_nodes(source)
    goals = set(_activation_nodes(target))
    if not starts or not goals:
        return []
    queue = deque((item, []) for item in starts)
    seen = set(starts)
    while queue:
        current, path = queue.popleft()
        if current in goals and path:
            return path
        if len(path) >= max_depth:
            continue
        for successor, edge_type, evidence in adjacent.get(current, []):
            if successor in seen:
                continue
            seen.add(successor)
            queue.append((successor, path + [{
                "source": current, "target": successor,
                "semantic_edge": edge_type, "evidence": evidence,
            }]))
    return []


def _selector_matches(region: dict[str, Any], selector: dict[str, Any]) -> bool:
    if selector.get("region_kinds") and region.get("kind") not in selector["region_kinds"]:
        return False
    predicate_signals = expression_signals(region.get("activation", {}).get("predicate", ""))
    boundary = set(region.get("boundary_signals", []))
    all_signals = predicate_signals | boundary | {region.get("activation", {}).get("target", "")}
    required = set(selector.get("signals_all", []))
    alternatives = set(selector.get("signals_any", []))
    if required and not required <= all_signals:
        return False
    if alternatives and not alternatives & all_signals:
        return False
    predicate_regex = selector.get("predicate_regex")
    return not predicate_regex or bool(re.search(predicate_regex, region.get("activation", {}).get("predicate", "")))


def _spec_phase_matches(region: dict[str, Any], spec: dict[str, Any]) -> list[dict[str, Any]]:
    matches = []
    for chain in spec.get("chains", []):
        if not fnmatch.fnmatch(region["module"], chain.get("module", "*")):
            continue
        for rank, phase in enumerate(chain.get("phases", [])):
            if _selector_matches(region, phase.get("selector", {})):
                matches.append({
                    "chain_id": chain["chain_id"], "phase": phase["name"], "rank": rank,
                    "strict_order": bool(chain.get("strict_order", True)),
                    "max_stage_span": chain.get("max_stage_span"),
                    "source": chain.get("source", "SPEC"),
                })
                # Ordered protocol selectors often overlap: a completion
                # predicate still contains the active/request context.  The
                # first matching phase is the conservative entry phase; using
                # every match would manufacture contradictory forward and
                # reverse relations for one region.
                break
    return matches


def _spec_relation(source_matches: list[dict[str, Any]], target_matches: list[dict[str, Any]]) -> list[dict[str, Any]]:
    records = []
    for left in source_matches:
        for right in target_matches:
            if left["chain_id"] != right["chain_id"]:
                continue
            span = right["rank"] - left["rank"]
            max_span = left.get("max_stage_span")
            if span >= 0 and max_span is not None and span > int(max_span):
                status = "DISALLOW"
                reason = "spec_stage_span_exceeded"
            elif span >= 0:
                status = "ALLOW"
                reason = "nondecreasing_spec_phase"
            elif left["strict_order"]:
                status = "DISALLOW"
                reason = "reverse_strict_spec_phase"
            else:
                status = "UNKNOWN"
                reason = "reverse_nonstrict_spec_phase"
            records.append({
                "status": status, "source": "SPEC", "reason": reason,
                "chain_id": left["chain_id"],
                "source_phase": left["phase"], "source_rank": left["rank"],
                "target_phase": right["phase"], "target_rank": right["rank"],
                "stage_span": span, "max_stage_span": max_span,
                "confidence": 1.0 if status != "UNKNOWN" else 0.5,
            })
    return records


def build_constraint_annotated_region_graph(
    region_graph: dict[str, Any], semantic_graph: dict[str, Any], design: RTLDesign,
    *, spec: dict[str, Any] | None = None, reset: str = "resetn",
    semantic_depth: int = 8, fsm_depth: int = 16,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Annotate every Region Edge with ALLOW/DISALLOW/UNKNOWN evidence."""

    spec = spec or {}
    nodes = {item["region_id"]: deepcopy(item) for item in region_graph.get("nodes", [])}
    fsm_doc = derive_fsm_transition_graph(design, reset=reset)
    fsm_reachable = _fsm_reachability(fsm_doc, fsm_depth)
    semantic_adjacent = _semantic_adjacency(semantic_graph)
    phase_matches = {region_id: _spec_phase_matches(item, spec) for region_id, item in nodes.items()}
    for region_id, node in nodes.items():
        node["microarchitecture_phases"] = phase_matches[region_id]

    annotated_edges = []
    for edge in region_graph.get("edges", []):
        copied = deepcopy(edge)
        source = nodes[edge["source_region"]]
        target = nodes[edge["target_region"]]
        evidence: list[dict[str, Any]] = []
        evidence.extend(_spec_relation(phase_matches[source["region_id"]], phase_matches[target["region_id"]]))

        source_atoms = _state_atoms(source["activation"]["predicate"])
        target_atoms = _state_atoms(target["activation"]["predicate"])
        for state_signal in sorted(set(source_atoms) & set(target_atoms)):
            closure = fsm_reachable.get((source["module"], state_signal))
            if not closure:
                continue
            for left in sorted(source_atoms[state_signal]):
                for right in sorted(target_atoms[state_signal]):
                    reachable = right in closure.get(left, set())
                    evidence.append({
                        "status": "ALLOW" if reachable else "DISALLOW",
                        "source": "RTL", "reason": (
                            "fsm_state_reachable" if reachable else "fsm_state_unreachable_within_captured_transition_graph"
                        ),
                        "state_signal": state_signal, "source_state": left, "target_state": right,
                        "max_transition_depth": fsm_depth, "confidence": 0.98 if reachable else 0.95,
                    })

        source_constants = _constant_polarities(source["activation"]["predicate"], design, source["module"])
        target_constants = _constant_polarities(target["activation"]["predicate"], design, target["module"])
        for name in sorted(set(source_constants) & set(target_constants)):
            if source_constants[name] == {True} and target_constants[name] == {False} or (
                source_constants[name] == {False} and target_constants[name] == {True}
            ):
                evidence.append({
                    "status": "DISALLOW", "source": "RTL",
                    "reason": "stable_configuration_contradiction", "parameter": name,
                    "confidence": 1.0,
                })

        shared_runtime = sorted(
            _runtime_signals(source["activation"]["predicate"], design, source["module"], reset)
            & _runtime_signals(target["activation"]["predicate"], design, target["module"], reset)
        )
        if shared_runtime:
            evidence.append({
                "status": "ALLOW", "source": "RTL", "reason": "shared_runtime_execution_context",
                "signals": shared_runtime, "confidence": min(0.92, 0.72 + 0.04 * len(shared_runtime)),
            })

        witness = _bounded_semantic_witness(source, target, semantic_adjacent, max_depth=semantic_depth)
        if witness:
            evidence.append({
                "status": "ALLOW", "source": "RTL", "reason": "bounded_activation_dependency",
                "semantic_depth": len(witness), "path": witness,
                "confidence": round(max(0.65, 0.95 - 0.04 * (len(witness) - 1)), 3),
            })

        disallow = [item for item in evidence if item["status"] == "DISALLOW"]
        allow = [item for item in evidence if item["status"] == "ALLOW"]
        # An explicit SPEC reverse-order or stable configuration contradiction
        # dominates hints.  For an RTL FSM, direct/reachable order dominates a
        # weak non-reachability result caused by incomplete state extraction.
        hard_disallow = [
            item for item in disallow
            if item["source"] == "SPEC" or item["reason"] == "stable_configuration_contradiction"
        ]
        if hard_disallow:
            ordering = "DISALLOW"
            confidence = max(item["confidence"] for item in hard_disallow)
        elif allow:
            ordering = "ALLOW"
            confidence = max(item["confidence"] for item in allow)
        elif disallow:
            ordering = "DISALLOW"
            confidence = max(item["confidence"] for item in disallow)
        else:
            ordering = "UNKNOWN"
            confidence = 0.0
        copied.update({
            "semantic_edge": edge["edge_type"],
            "ordering_constraint": ordering,
            "constraint_evidence": evidence,
            "constraint_sources": sorted({item["source"] for item in evidence}),
            "constraint_confidence": round(confidence, 3),
        })
        assert copied["ordering_constraint"] in ORDERING_VALUES
        annotated_edges.append(copied)

    annotated = {
        **deepcopy(region_graph),
        "schema": "region_flow.5.1-constraint-annotated-region-graph.v1",
        "nodes": list(nodes.values()), "edges": annotated_edges,
        "constraint_policy": {
            "formal_remains_final_oracle": True,
            "allow_is_formal_proof": False,
            "unknown_is_directly_rejected": False,
            "hard_disallow_sources": ["SPEC strict ordering", "RTL stable configuration", "RTL captured FSM impossibility"],
            "semantic_dependency_depth": semantic_depth,
            "fsm_transition_depth": fsm_depth,
        },
        "summary": {
            **region_graph.get("summary", {}),
            "constraint_counts": dict(Counter(item["ordering_constraint"] for item in annotated_edges)),
            "edges_with_spec_evidence": sum("SPEC" in item["constraint_sources"] for item in annotated_edges),
            "edges_with_rtl_evidence": sum("RTL" in item["constraint_sources"] for item in annotated_edges),
        },
    }
    constraint_graph = {
        "schema": "region_flow.5.1-microarchitecture-constraint-graph.v1",
        "spec_chains": spec.get("chains", []),
        "rtl_fsm": fsm_doc,
        "region_phase_matches": phase_matches,
        "summary": {
            "spec_chains": len(spec.get("chains", [])),
            "regions_with_spec_phase": sum(bool(items) for items in phase_matches.values()),
            **fsm_doc["summary"],
        },
    }
    return annotated, constraint_graph


def filter_constraint_guided_paths(
    candidate_doc: dict[str, Any], annotated_graph: dict[str, Any], *,
    max_paths_per_module: int = 16, max_pair_paths_per_module: int = 12,
    unknown_reserve_per_module: int = 4,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Prune impossible paths and spend a bounded budget on high-quality ones."""

    edge_by_id = {item["edge_id"]: item for item in annotated_graph.get("edges", [])}
    evaluated: list[dict[str, Any]] = []
    for path in candidate_doc.get("paths", []):
        edge_constraints = [edge_by_id[item] for item in path["region_edges"]]
        statuses = [item["ordering_constraint"] for item in edge_constraints]
        if "DISALLOW" in statuses:
            decision, reason = "REJECT", "ordering_or_context_constraint_violation"
        elif statuses and all(item == "ALLOW" for item in statuses):
            decision, reason = "ELIGIBLE", "all_region_edges_constraint_allowed"
        else:
            decision, reason = "UNKNOWN_RESERVE", "incomplete_constraint_evidence"
        confidence = (
            sum(item["constraint_confidence"] for item in edge_constraints) / len(edge_constraints)
            if edge_constraints else 0.0
        )
        evaluated.append({
            **deepcopy(path),
            "constraint_statuses": statuses,
            "constraint_confidence": round(confidence, 6),
            "constraint_decision": decision,
            "constraint_reason": reason,
            "constraint_evidence_edge_ids": [item["edge_id"] for item in edge_constraints],
        })

    by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for item in evaluated:
        by_module[item["module"]].append(item)
    selected: list[dict[str, Any]] = []
    budget_rejected: set[str] = set()
    for module, items in sorted(by_module.items()):
        eligible = [item for item in items if item["constraint_decision"] == "ELIGIBLE"]
        unknown = [item for item in items if item["constraint_decision"] == "UNKNOWN_RESERVE"]

        def rank(item: dict[str, Any]) -> tuple[Any, ...]:
            return (
                -item["constraint_confidence"],
                -item["normalized_structural_similarity"],
                -len(set(item["region_kinds"])),
                len(item["regions"]), item["path_id"],
            )

        eligible.sort(key=rank)
        unknown.sort(key=rank)
        pairs = [item for item in eligible if len(item["regions"]) == 2]
        longer = [item for item in eligible if len(item["regions"]) > 2]
        module_selected = longer[:max(0, max_paths_per_module - max_pair_paths_per_module)]
        # Cover distinct structural transitions before using the remaining
        # pair budget.  Dense Decode fan-out must not crowd out FSM->update or
        # datapath->completion relations merely because their confidence ties.
        transition_seen: set[tuple[Any, ...]] = set()
        diverse_pairs: list[dict[str, Any]] = []
        pair_remainder: list[dict[str, Any]] = []
        for item in pairs:
            transition = (
                item["region_kinds"][0], item["region_kinds"][1],
                tuple(item.get("edge_types", [])), tuple(item["constraint_statuses"]),
            )
            if transition not in transition_seen:
                transition_seen.add(transition)
                diverse_pairs.append(item)
            else:
                pair_remainder.append(item)
        module_selected += (diverse_pairs + pair_remainder)[:max_pair_paths_per_module]
        remaining = max_paths_per_module - len(module_selected)
        already = {item["path_id"] for item in module_selected}
        module_selected += [item for item in eligible if item["path_id"] not in already][:remaining]
        remaining = min(unknown_reserve_per_module, max_paths_per_module - len(module_selected))
        module_selected += unknown[:remaining]
        selected.extend(module_selected)
        budget_rejected |= {
            item["path_id"] for item in eligible + unknown
            if item["path_id"] not in {selected_item["path_id"] for selected_item in module_selected}
        }

    selected.sort(key=lambda item: (item["module"], -len(item["regions"]), item["path_id"]))
    decisions = []
    selected_ids = {item["path_id"] for item in selected}
    for item in evaluated:
        final_decision = item["constraint_decision"]
        final_reason = item["constraint_reason"]
        if item["path_id"] in selected_ids:
            final_decision = "FORMAL_CANDIDATE"
            final_reason = "selected_by_constraint_aware_budget"
        elif item["path_id"] in budget_rejected:
            final_decision = "REJECT"
            final_reason = "constraint_aware_search_budget"
        decisions.append({
            key: item[key] for key in (
                "path_id", "module", "regions", "region_kinds", "region_edges",
                "constraint_statuses", "constraint_confidence",
            )
        } | {"decision": final_decision, "reason": final_reason})

    guided = {
        "schema": "region_flow.5.1-constraint-guided-functional-paths.v1",
        "policy": {
            "formal_remains_final_oracle": True,
            "unknown_reserve_per_module": unknown_reserve_per_module,
            "max_paths_per_module": max_paths_per_module,
            "max_pair_paths_per_module": max_pair_paths_per_module,
            "path_length_is_semantic_region_count": True,
        },
        "paths": selected,
        "summary": {
            "raw_bounded_paths": candidate_doc.get("summary", {}).get("raw_bounded_paths", 0),
            "static_candidate_paths": len(candidate_doc.get("paths", [])),
            "constraint_eligible_paths": sum(item["constraint_decision"] == "ELIGIBLE" for item in evaluated),
            "constraint_unknown_paths": sum(item["constraint_decision"] == "UNKNOWN_RESERVE" for item in evaluated),
            "constraint_rejected_paths": sum(item["constraint_decision"] == "REJECT" for item in evaluated),
            "formal_candidate_paths": len(selected),
            "by_module": dict(Counter(item["module"] for item in selected)),
            "by_length": dict(Counter(str(len(item["regions"])) for item in selected)),
        },
    }
    decision_doc = {
        "schema": "region_flow.5.1-path-pruning-decisions.v1",
        "decisions": decisions,
        "summary": dict(Counter(item["decision"] for item in decisions)),
        "digest": hashlib.sha256(
            "\n".join(f"{item['path_id']}:{item['decision']}:{item['reason']}" for item in decisions).encode()
        ).hexdigest(),
    }
    return guided, decision_doc
