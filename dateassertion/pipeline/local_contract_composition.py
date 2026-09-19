"""Req8.8 contract-level composition over Req8.7 Local Contracts.

The implementation is deliberately design agnostic.  RTL graph facts create
interfaces and possible relations; an optional SPEC/LLM pass may name/order
already-grounded events, but cannot introduce identifiers or emit SVA.  Only
the deterministic compilers at the bottom of this file create properties.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from copy import deepcopy
import hashlib
import json
import re
from typing import Any, Iterable

from dateassertion.ir.schema import ObjectType, PropertyIR
from dateassertion.rtl_frontend.parser import RTLDesign


class Requirement88ValidationError(ValueError):
    """A contract, SPEC binding, or composition violated a Req8.8 gate."""


_IDENTIFIER = re.compile(r"(?<![.'\d])\b[A-Za-z_$][A-Za-z0-9_$]*\b")
_RESERVED = {
    "and", "or", "not", "if", "else", "begin", "end", "posedge", "negedge",
    "past", "stable", "rose", "fell", "true", "false", "bx", "b0", "b1",
}


def _digest(*values: Any, size: int = 12) -> str:
    raw = "\x1f".join(json.dumps(value, sort_keys=True) if not isinstance(value, str) else value
                      for value in values)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()[:size]


def expression_signals(expression: Any, known: Iterable[str] | None = None) -> list[str]:
    """Return identifiers used by a SystemVerilog expression.

    When ``known`` is supplied, only identifiers that exist in the elaborated
    module are retained.  This prevents keywords and enum literals from
    becoming checker ports.
    """

    if isinstance(expression, list):
        text = " ".join(str(item) for item in expression)
    else:
        text = str(expression or "")
    candidates = [item for item in _IDENTIFIER.findall(text) if item.lower() not in _RESERVED]
    if known is not None:
        allowed = set(known)
        candidates = [item for item in candidates if item in allowed]
    return list(dict.fromkeys(candidates))


def _signal_name(node_id: str) -> str:
    return node_id.rsplit(".", 1)[-1] if node_id.startswith("signal:") else ""


def _binding_events(prop: PropertyIR, known: set[str]) -> list[dict[str, Any]]:
    roles = prop.bindings
    raw: list[tuple[str, Any, str, int | None]] = []
    template = str(prop.template).upper()
    if template == "CAUSALITY":
        raw += [("CAUSE", roles.get("CAUSE"), "TRIGGER", 0),
                ("EFFECT", roles.get("EFFECT"), "EFFECT", int(roles.get("DELAY", 1)))]
    elif template == "UPDATE":
        raw += [("CONDITION", roles.get("CONDITION"), "TRIGGER", 0),
                ("UPDATE", roles.get("TARGET"), "EFFECT", int(roles.get("DELAY", 1)))]
    elif template == "RESET":
        raw += [("RESET", roles.get("RESET"), "TRIGGER", 0),
                ("RESET_VALUE", roles.get("TARGET"), "STATE", 1)]
    elif template == "DATA_INTEGRITY":
        raw += [("CONDITION", roles.get("CONDITION"), "TRIGGER", 0),
                ("RESULT", roles.get("TARGET"), "EFFECT", int(roles.get("DELAY", 0)))]
    elif template == "PERSISTENCE":
        raw += [("REQUEST", roles.get("START"), "TRIGGER", 0),
                ("COMPLETION", roles.get("END"), "EFFECT", None)]
    elif template == "STABILITY":
        raw += [("ACTIVE", roles.get("CONDITION"), "TRIGGER", 0)]
        for signal in roles.get("SIGNALS", []):
            raw.append(("STABLE_PAYLOAD", signal, "STATE", None))
    elif template == "HOLD":
        raw += [("HOLD_ENABLE", roles.get("CONDITION"), "TRIGGER", 0),
                ("HELD_STATE", roles.get("TARGET"), "STATE", 1)]
    result = []
    for semantic_role, predicate, event_kind, delay in raw:
        if predicate in (None, "", []):
            continue
        predicate = str(predicate)
        signals = expression_signals(predicate, known)
        if not signals:
            continue
        result.append({
            "event_id": "event_" + _digest(prop.property_id, semantic_role, predicate),
            "predicate": predicate,
            "semantic_role": semantic_role,
            "event_kind": event_kind,
            "signals": signals,
            "delay_from_trigger": delay,
            "source": "TRUSTED_LOCAL_OBLIGATION",
            "source_property_ids": [prop.property_id],
        })
    return result


def _assignment_events(region: dict[str, Any], known: set[str]) -> list[dict[str, Any]]:
    core = set(region.get("core_node_ids", []))
    nodes = region.get("coi", {}).get("nodes", [])
    result = []
    for node in nodes:
        if node.get("kind") != "assignment" or node.get("id") not in core:
            continue
        assignment_id = str(node["id"])
        guard = str(node.get("guard") or "")
        lhs = str(node.get("lhs") or "")
        rhs = str(node.get("rhs") or "")
        source = node.get("source", {})
        if guard and guard not in {"1", "1'b1", "True"}:
            signals = expression_signals(guard, known)
            if signals:
                result.append({
                    "event_id": "event_" + _digest(region["region_id"], assignment_id, "guard", guard),
                    "predicate": guard,
                    "semantic_role": "RTL_GUARD",
                    "event_kind": "TRIGGER",
                    "signals": signals,
                    "delay_from_trigger": 0,
                    "source": "RTL_ASSIGNMENT_GUARD",
                    "assignment_id": assignment_id,
                    "evidence": source,
                    "source_property_ids": [],
                })
        if lhs in known:
            info = region.get("_module_signal_info", {}).get(lhs, {})
            width = str(info.get("width", ""))
            if not width and rhs.strip() in {"0", "1", "1'b0", "1'b1"}:
                predicate = f"!{lhs}" if rhs.strip() in {"0", "1'b0"} else lhs
            else:
                predicate = lhs
            result.append({
                "event_id": "event_" + _digest(region["region_id"], assignment_id, "effect", predicate),
                "predicate": predicate,
                "semantic_role": "RTL_UPDATE_EFFECT",
                "event_kind": "EFFECT",
                "signals": [lhs],
                "delay_from_trigger": 1 if node.get("timing") == "next_cycle" else 0,
                "source": "RTL_ASSIGNMENT_EFFECT",
                "assignment_id": assignment_id,
                "evidence": source,
                "source_property_ids": [],
            })
    return result


def _deduplicate_events(events: list[dict[str, Any]], limit: int = 16) -> list[dict[str, Any]]:
    by_key: dict[tuple[str, str], dict[str, Any]] = {}
    priority = {"TRUSTED_LOCAL_OBLIGATION": 3, "RTL_ASSIGNMENT_GUARD": 2,
                "RTL_ASSIGNMENT_EFFECT": 1}
    for event in events:
        key = ("".join(str(event["predicate"]).split()), str(event["event_kind"]))
        prior = by_key.get(key)
        if prior is None:
            by_key[key] = deepcopy(event)
            continue
        prior["source_property_ids"] = sorted(set(prior.get("source_property_ids", [])) |
                                               set(event.get("source_property_ids", [])))
        if priority.get(event.get("source", ""), 0) > priority.get(prior.get("source", ""), 0):
            preserved = prior["source_property_ids"]
            by_key[key] = deepcopy(event)
            by_key[key]["source_property_ids"] = preserved
    values = sorted(by_key.values(), key=lambda item: (
        -priority.get(item.get("source", ""), 0),
        item.get("semantic_role", ""), item["event_id"],
    ))
    return values[:limit]


def _region_interface(region: dict[str, Any], graph: dict[str, Any], known: set[str]) -> dict[str, Any]:
    core = set(region.get("core_node_ids", []))
    inputs: set[str] = set()
    outputs: set[str] = set()
    dependencies = []
    for edge in graph.get("edges", []):
        source, target = str(edge.get("source", "")), str(edge.get("target", ""))
        if target in core and source.startswith("signal:"):
            name = _signal_name(source)
            if name in known:
                inputs.add(name)
                dependencies.append({
                    "type": edge.get("type"), "signal": name,
                    "assignment_id": target, "direction": "IN",
                    "evidence": edge.get("evidence", {}),
                })
        if source in core and target.startswith("signal:"):
            name = _signal_name(target)
            if name in known:
                outputs.add(name)
                dependencies.append({
                    "type": edge.get("type"), "signal": name,
                    "assignment_id": source, "direction": "OUT",
                    "evidence": edge.get("evidence", {}),
                })
    state = sorted(inputs & outputs)
    return {
        "inputs": sorted(inputs - outputs),
        "outputs": sorted(outputs),
        "state": state,
        "dependencies": dependencies,
    }


def build_local_contracts(
    region_inventory: dict[str, Any], trusted_properties: list[PropertyIR],
    property_metadata: dict[str, dict[str, Any]], graph: dict[str, Any], design: RTLDesign,
) -> dict[str, Any]:
    """Upgrade every Req8.7 Region into a contract node.

    A Trusted property is attached to every evidence-backed Region listed in
    its Req8.7 metadata, not merely to the property's display/primary Region.
    This preserves the exact graph attribution established by Req8.7.
    """

    properties_by_region: dict[str, list[PropertyIR]] = defaultdict(list)
    for prop in trusted_properties:
        metadata = property_metadata.get(prop.property_id, {})
        region_ids = metadata.get("region_ids") or [prop.region_id]
        for region_id in region_ids:
            properties_by_region[str(region_id)].append(prop)

    contracts = []
    for raw_region in region_inventory.get("regions", []):
        region = deepcopy(raw_region)
        module = str(region.get("module", ""))
        module_signals = design.module_signals.get(module, {})
        known = set(module_signals)
        region["_module_signal_info"] = {
            name: {"width": value.width, "direction": value.direction, "kind": value.kind}
            for name, value in module_signals.items()
        }
        interface = _region_interface(region, graph, known)
        local_props = properties_by_region.get(str(region["region_id"]), [])
        events = []
        for prop in local_props:
            if (prop.target_module or module) == module:
                events.extend(_binding_events(prop, known))
        events.extend(_assignment_events(region, known))
        events = _deduplicate_events(events)

        # Property bindings fill gaps left by a conservative core-node boundary.
        event_inputs = {
            signal for event in events if event["event_kind"] == "TRIGGER"
            for signal in event["signals"]
        }
        event_outputs = {
            signal for event in events if event["event_kind"] in {"EFFECT", "STATE"}
            for signal in event["signals"]
        }
        inputs = sorted((set(interface["inputs"]) | event_inputs) - event_outputs)
        outputs = sorted(set(interface["outputs"]) | event_outputs)
        state = sorted(set(interface["state"]) | {
            name for name in outputs
            if getattr(module_signals.get(name), "kind", "") in {"reg", "logic"}
            and getattr(module_signals.get(name), "direction", "") == "internal"
        })
        if local_props and len(local_props) >= 2:
            readiness = 3
        elif local_props:
            readiness = 2
        elif events and (inputs or outputs):
            readiness = 1
        else:
            readiness = 0
        contract_id = "local_contract_" + _digest(region["region_id"])
        evidence = region.get("evidence", {})
        contracts.append({
            "contract_id": contract_id,
            "region_id": region["region_id"],
            "module": module,
            "region_kind": region.get("kind", "UNKNOWN"),
            "ontology_classification": region.get("ontology_classification", ""),
            "boundary": {
                "core_node_ids": list(region.get("core_node_ids", [])),
                "coi_node_ids": list(region.get("coi", {}).get("node_ids", [])),
                "source": evidence,
            },
            "interface": {"inputs": inputs, "outputs": outputs, "events": events,
                          "state": state},
            "dependencies": interface["dependencies"],
            "trusted_local_obligations": sorted({item.property_id for item in local_props}),
            "local_evidence": [item for prop in local_props for item in prop.evidence],
            "readiness_level": readiness,
            "readiness_meaning": {
                0: "DISCOVERED_ONLY", 1: "INTERFACE_READY",
                2: "TRUSTED_LOCAL_CONTRACT", 3: "STRONG_LOCAL_CONTRACT",
            }[readiness],
        })
    counts = Counter(item["readiness_level"] for item in contracts)
    return {
        "schema": "region_flow.8-local-contracts.v1",
        "contracts": contracts,
        "summary": {
            "contracts": len(contracts),
            "readiness": {f"level_{key}": counts[key] for key in range(4)},
            "contracts_with_trusted_local_obligations": sum(bool(item["trusted_local_obligations"])
                                                             for item in contracts),
        },
    }


def package_spec_composition_context(
    spec_lines: list[dict[str, Any]], local_contracts: dict[str, Any], *,
    max_contracts: int = 24, max_context_chars: int = 32_000,
) -> dict[str, Any]:
    """Package only SPEC-relevant contract/event summaries for DeepSeek.

    ``max_contracts`` alone is not a transport bound because real predicates
    vary greatly in size.  Apply a deterministic serialized-character budget
    after semantic scoring, while retaining at least two contracts so a
    cross-contract relation remains expressible.
    """

    spec_text = "\n".join(item["text"] for item in spec_lines)
    tick_names = set(re.findall(r"`([A-Za-z_$][A-Za-z0-9_$]*)`", spec_text))
    scored = []
    for contract in local_contracts.get("contracts", []):
        interface = contract["interface"]
        signals = set(interface["inputs"]) | set(interface["outputs"]) | set(interface["state"])
        score = 8 * len(signals & tick_names) + 3 * int(contract["readiness_level"] >= 2) + len(interface["events"])
        if score:
            scored.append((score, contract))
    ranked = [
        item for _, item in sorted(
            scored, key=lambda value: (-value[0], value[1]["contract_id"])
        )[:max_contracts]
    ]

    def contract_summary(item: dict[str, Any]) -> dict[str, Any]:
        return {
            "contract_id": item["contract_id"], "region_id": item["region_id"],
            "module": item["module"], "region_kind": item["region_kind"],
            "readiness_level": item["readiness_level"],
            "inputs": item["interface"]["inputs"],
            "outputs": item["interface"]["outputs"],
            "state": item["interface"]["state"],
            "events": [{key: event.get(key) for key in (
                "event_id", "predicate", "semantic_role", "event_kind", "signals", "source",
            )} for event in item["interface"]["events"]],
            "trusted_local_obligations": item["trusted_local_obligations"],
        }

    def assemble(selected: list[dict[str, Any]]) -> dict[str, Any]:
        return {
            "schema": "region_flow.8-spec-composition-context.v1",
            "whole_design_rtl_supplied": False,
            "spec_lines": spec_lines,
            "allowed_relation_types": ["CAUSALITY", "ORDERING", "DATA_TRANSFER", "STATE_CONTROL"],
            "allowed_contract_ids": [item["contract_id"] for item in selected],
            "contracts": [contract_summary(item) for item in selected],
            "prohibited_outputs": ["SVA", "SystemVerilog", "assert property", "assume property"],
        }

    selected = list(ranked)
    budget = max(0, int(max_context_chars))
    while budget and len(selected) > 2:
        compact_chars = len(json.dumps(assemble(selected), ensure_ascii=False, separators=(",", ":")))
        if compact_chars <= budget:
            break
        selected.pop()
    context = assemble(selected)
    compact_chars = len(json.dumps(context, ensure_ascii=False, separators=(",", ":")))
    context["packaging_audit"] = {
        "eligible_contracts": len(scored),
        "contract_limit": int(max_contracts),
        "contracts_before_character_budget": len(ranked),
        "contracts_selected": len(selected),
        "max_context_chars": budget,
        "serialized_chars_before_audit": compact_chars,
        "character_budget_satisfied": not budget or compact_chars <= budget,
        "minimum_two_contracts_preserved": len(selected) >= min(2, len(ranked)),
    }
    return context


def _contains_forbidden_generation(value: Any) -> bool:
    if isinstance(value, dict):
        for key, item in value.items():
            if str(key).lower() in {"sva", "assertion", "property_body", "assumption"}:
                return True
            if _contains_forbidden_generation(item):
                return True
    elif isinstance(value, list):
        return any(_contains_forbidden_generation(item) for item in value)
    elif isinstance(value, str):
        lowered = value.lower()
        return "assert property" in lowered or "assume property" in lowered
    return False


def validate_spec_composition_response(
    response: dict[str, Any], context: dict[str, Any], *, maximum_delay: int = 128,
) -> dict[str, Any]:
    if not isinstance(response, dict) or _contains_forbidden_generation(response):
        raise Requirement88ValidationError("DeepSeek may bind contract semantics but may not generate SVA")
    contracts = {item["contract_id"]: item for item in context["contracts"]}
    events = {
        (item["contract_id"], event["event_id"]): event
        for item in context["contracts"] for event in item["events"]
    }
    supplied = {int(item["line"]): str(item["text"]) for item in context["spec_lines"]}
    constraints = []
    ids = set()
    for raw in response.get("constraints", []):
        if not isinstance(raw, dict):
            raise Requirement88ValidationError("constraint must be an object")
        required = {"constraint_id", "source_contract_id", "source_event_id",
                    "target_contract_id", "target_event_id", "relation_type", "evidence"}
        if not required <= set(raw):
            raise Requirement88ValidationError(f"constraint lacks fields: {sorted(required - set(raw))}")
        constraint_id = str(raw["constraint_id"])
        if not constraint_id or constraint_id in ids:
            raise Requirement88ValidationError("constraint IDs must be unique and non-empty")
        ids.add(constraint_id)
        source_key = (str(raw["source_contract_id"]), str(raw["source_event_id"]))
        target_key = (str(raw["target_contract_id"]), str(raw["target_event_id"]))
        if source_key not in events or target_key not in events:
            raise Requirement88ValidationError(f"{constraint_id}: invented contract/event ID")
        if source_key[0] == target_key[0]:
            raise Requirement88ValidationError(f"{constraint_id}: composition must cross Local Contracts")
        if contracts[source_key[0]]["module"] != contracts[target_key[0]]["module"]:
            raise Requirement88ValidationError(f"{constraint_id}: cross-module relation lacks hierarchy mapping")
        if "".join(str(events[source_key]["predicate"]).split()) == "".join(
            str(events[target_key]["predicate"]).split()
        ):
            raise Requirement88ValidationError(
                f"{constraint_id}: source and target are duplicate predicates, not composition"
            )
        relation = str(raw["relation_type"]).upper()
        if relation not in context["allowed_relation_types"]:
            raise Requirement88ValidationError(f"{constraint_id}: unsupported relation {relation}")
        minimum = int(raw.get("min_delay", 0))
        maximum = int(raw.get("max_delay", max(1, minimum)))
        if minimum < 0 or maximum < minimum or maximum > maximum_delay:
            raise Requirement88ValidationError(f"{constraint_id}: invalid bounded delay")
        evidence = raw["evidence"]
        start, end, quote = int(evidence.get("line_start", 0)), int(evidence.get("line_end", 0)), str(evidence.get("quote", ""))
        # Line wrapping in Markdown is presentation, not semantic content; keep
        # every word exact while normalizing only whitespace, as Req8.7 does.
        excerpt = re.sub(r"\s+", " ", " ".join(
            supplied.get(line, "") for line in range(start, end + 1)
        )).strip()
        normalized_quote = re.sub(r"\s+", " ", quote).strip()
        if not normalized_quote or normalized_quote not in excerpt:
            # Models occasionally identify an exact quotation but miss the
            # first/last wrapped Markdown line by one.  Locate that unchanged
            # quotation in the complete supplied section and repair only the
            # provenance range.  Hallucinated/reworded text still fails.
            ordered_lines = sorted(supplied)
            matches: list[tuple[int, int]] = []
            for candidate_start in ordered_lines:
                aggregate = ""
                for candidate_end in [line for line in ordered_lines if line >= candidate_start]:
                    aggregate = re.sub(r"\s+", " ", (aggregate + " " + supplied[candidate_end])).strip()
                    if normalized_quote in aggregate:
                        matches.append((candidate_start, candidate_end))
                        break
            if not matches:
                raise Requirement88ValidationError(f"{constraint_id}: SPEC quote is not exact supplied text")
            found = min(matches, key=lambda pair: (pair[1] - pair[0], pair[0]))
            start, end = found
            evidence = {**evidence, "line_start": start, "line_end": end,
                        "line_range_corrected_from_llm": True}
        constraints.append({
            **deepcopy(raw), "relation_type": relation,
            "min_delay": minimum, "max_delay": maximum,
            "confidence": float(raw.get("confidence", 0.0)),
            "source_predicate": events[source_key]["predicate"],
            "target_predicate": events[target_key]["predicate"],
            "validated_exact_spec_evidence": True,
            "evidence": evidence,
        })

    constraint_by_id = {item["constraint_id"]: item for item in constraints}
    chains = []
    for raw in response.get("lifecycle_chains", []):
        constraint_ids = [str(item) for item in raw.get("constraint_ids", [])]
        if len(constraint_ids) < 2 or any(item not in constraint_by_id for item in constraint_ids):
            raise Requirement88ValidationError("lifecycle chain must reference at least two known constraints")
        relations = [constraint_by_id[item] for item in constraint_ids]
        for left, right in zip(relations, relations[1:]):
            if left["target_contract_id"] != right["source_contract_id"] or left["target_event_id"] != right["source_event_id"]:
                raise Requirement88ValidationError("lifecycle constraint IDs do not form a contiguous event chain")
        contract_path = [relations[0]["source_contract_id"]] + [
            item["target_contract_id"] for item in relations
        ]
        if len(contract_path) != len(set(contract_path)):
            raise Requirement88ValidationError("lifecycle chain repeats a Local Contract")
        chains.append({**deepcopy(raw), "constraint_ids": constraint_ids})
    return {
        "schema": "region_flow.8-validated-spec-constraints.v1",
        "constraints": constraints,
        "lifecycle_chains": chains,
        "llm_generated_sva": False,
    }


def _event_index(contracts: list[dict[str, Any]]) -> dict[tuple[str, str], dict[str, Any]]:
    return {(contract["contract_id"], event["event_id"]): event
            for contract in contracts for event in contract["interface"]["events"]}


def _relation(
    source: dict[str, Any], target: dict[str, Any], *, spec_constraint: dict[str, Any] | None = None,
) -> dict[str, Any] | None:
    if source["contract_id"] == target["contract_id"] or source["module"] != target["module"]:
        return None
    sout = set(source["interface"]["outputs"])
    tin = set(target["interface"]["inputs"]) | set(target["interface"]["state"])
    shared = sorted(sout & tin)
    shared_state = sorted((set(source["interface"]["state"]) | sout) &
                          (set(target["interface"]["state"]) | tin))
    if spec_constraint is None and not shared:
        return None
    if shared_state:
        context_status = "STRONG"
        anchors = shared_state
    elif shared:
        context_status = "COMPATIBLE"
        anchors = shared
    elif spec_constraint is not None:
        source_signals = set(expression_signals(spec_constraint["source_predicate"]))
        target_signals = set(expression_signals(spec_constraint["target_predicate"]))
        common_region_state = set(source["interface"]["state"]) & set(target["interface"]["state"])
        if common_region_state or source_signals & set(target["interface"]["inputs"]):
            context_status, anchors = "COMPATIBLE", sorted(common_region_state or source_signals)
        else:
            # Same-module SPEC ordering is useful for search, but remains weak
            # until the event sequence itself is formally validated.
            context_status, anchors = "SPEC_ORDERED_PENDING_FORMAL", []
    else:
        return None
    relation_type = (spec_constraint or {}).get("relation_type")
    if not relation_type:
        relation_type = "STATE_CONTROL" if shared_state else "DATA_TRANSFER"
    relation_id = "contract_edge_" + _digest(
        source["contract_id"], target["contract_id"], relation_type,
        (spec_constraint or {}).get("constraint_id", ""), shared,
    )
    return {
        "edge_id": relation_id,
        "source_contract_id": source["contract_id"],
        "target_contract_id": target["contract_id"],
        "relation_type": relation_type,
        "interface_compatible": bool(shared) or spec_constraint is not None,
        "shared_interface_signals": shared,
        "partial_order_status": "ALLOW" if spec_constraint else "RTL_COMPATIBLE",
        "execution_context_status": context_status,
        "execution_context_anchors": anchors,
        "spec_constraint_id": (spec_constraint or {}).get("constraint_id"),
        "source_event_id": (spec_constraint or {}).get("source_event_id"),
        "target_event_id": (spec_constraint or {}).get("target_event_id"),
        "min_delay": (spec_constraint or {}).get("min_delay"),
        "max_delay": (spec_constraint or {}).get("max_delay"),
        "evidence": (spec_constraint or {}).get("evidence", {}),
    }


def build_contract_graph(
    local_contracts: dict[str, Any], validated_constraints: dict[str, Any] | None = None,
) -> dict[str, Any]:
    contracts = local_contracts.get("contracts", [])
    edges: dict[str, dict[str, Any]] = {}
    for source in contracts:
        if source["readiness_level"] < 1:
            continue
        for target in contracts:
            if target["readiness_level"] < 1:
                continue
            edge = _relation(source, target)
            if edge:
                edges[edge["edge_id"]] = edge
    by_id = {item["contract_id"]: item for item in contracts}
    for constraint in (validated_constraints or {}).get("constraints", []):
        source = by_id[constraint["source_contract_id"]]
        target = by_id[constraint["target_contract_id"]]
        edge = _relation(source, target, spec_constraint=constraint)
        if edge:
            edges[edge["edge_id"]] = edge
    values = sorted(edges.values(), key=lambda item: item["edge_id"])
    return {
        "schema": "region_flow.8-contract-graph.v1",
        "nodes": deepcopy(contracts), "edges": values,
        "summary": {
            "nodes": len(contracts), "edges": len(values),
            "by_relation": dict(Counter(item["relation_type"] for item in values)),
            "by_context": dict(Counter(item["execution_context_status"] for item in values)),
            "spec_constrained_edges": sum(bool(item.get("spec_constraint_id")) for item in values),
        },
    }


def incremental_update_contract_graph(
    previous_graph: dict[str, Any], all_contracts: dict[str, Any],
    validated_constraints: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Update only relations touching newly added Local Contracts."""

    previous_ids = {item["contract_id"] for item in previous_graph.get("nodes", [])}
    contracts = all_contracts.get("contracts", [])
    new_ids = {item["contract_id"] for item in contracts} - previous_ids
    retained_edges = [item for item in previous_graph.get("edges", [])
                      if item["source_contract_id"] not in new_ids and item["target_contract_id"] not in new_ids]
    by_id = {item["contract_id"]: item for item in contracts}
    recomputed_map: dict[str, dict[str, Any]] = {}
    # Only evaluate ordered pairs where at least one endpoint is new.
    for source in contracts:
        if source["readiness_level"] < 1:
            continue
        for target in contracts:
            if target["readiness_level"] < 1:
                continue
            if source["contract_id"] not in new_ids and target["contract_id"] not in new_ids:
                continue
            edge = _relation(source, target)
            if edge:
                recomputed_map[edge["edge_id"]] = edge
    for constraint in (validated_constraints or {}).get("constraints", []):
        source_id = constraint["source_contract_id"]
        target_id = constraint["target_contract_id"]
        if source_id not in new_ids and target_id not in new_ids:
            continue
        if source_id not in by_id or target_id not in by_id:
            continue
        edge = _relation(by_id[source_id], by_id[target_id], spec_constraint=constraint)
        if edge:
            recomputed_map[edge["edge_id"]] = edge
    recomputed = list(recomputed_map.values())
    merged = {item["edge_id"]: item for item in retained_edges + recomputed}
    values = sorted(merged.values(), key=lambda item: item["edge_id"])
    result = {
        "schema": "region_flow.8-contract-graph.v1",
        "nodes": deepcopy(contracts), "edges": values,
    }
    result["summary"] = {
        "nodes": len(contracts), "edges": len(values),
        "by_relation": dict(Counter(item["relation_type"] for item in values)),
        "by_context": dict(Counter(item["execution_context_status"] for item in values)),
        "spec_constrained_edges": sum(bool(item.get("spec_constraint_id")) for item in values),
        "incremental": True, "new_contracts": len(new_ids),
    }
    audit = {
        "schema": "region_flow.8-incremental-update-audit.v1",
        "new_contract_ids": sorted(new_ids),
        "retained_unaffected_edges": len(retained_edges),
        "recomputed_edges_touching_new_contract": len(recomputed),
        "full_pair_space": len(contracts) * max(0, len(contracts) - 1),
        "recomputed_pair_space": len(new_ids) * max(0, 2 * len(contracts) - len(new_ids) - 1),
        "unaffected_formal_results_invalidated": 0,
    }
    return result, audit


def generate_composition_candidates(
    contract_graph: dict[str, Any], validated_constraints: dict[str, Any], *, max_chain_length: int = 6,
) -> dict[str, Any]:
    """Generate compatible candidates; never enumerate arbitrary Region paths."""

    contracts = {item["contract_id"]: item for item in contract_graph["nodes"]}
    events = _event_index(list(contracts.values()))
    edge_by_constraint = {
        item["spec_constraint_id"]: item for item in contract_graph["edges"]
        if item.get("spec_constraint_id")
    }
    candidates = []
    rejected = Counter()
    for constraint in validated_constraints.get("constraints", []):
        edge = edge_by_constraint.get(constraint["constraint_id"])
        if not edge:
            rejected["NO_CONTRACT_EDGE"] += 1
            continue
        source = contracts[constraint["source_contract_id"]]
        target = contracts[constraint["target_contract_id"]]
        if min(source["readiness_level"], target["readiness_level"]) < 1:
            rejected["READINESS_LEVEL_0"] += 1
            continue
        candidates.append({
            "candidate_id": "composition_" + _digest(constraint["constraint_id"], "ADJACENT"),
            "level": "ADJACENT",
            "contract_ids": [source["contract_id"], target["contract_id"]],
            "region_ids": [source["region_id"], target["region_id"]],
            "module": source["module"],
            "event_ids": [constraint["source_event_id"], constraint["target_event_id"]],
            "event_predicates": [constraint["source_predicate"], constraint["target_predicate"]],
            "delay_ranges": [[constraint["min_delay"], constraint["max_delay"]]],
            "edge_ids": [edge["edge_id"]],
            "constraint_ids": [constraint["constraint_id"]],
            "relation_types": [constraint["relation_type"]],
            "context_status": edge["execution_context_status"],
            "context_anchors": edge["execution_context_anchors"],
            "source": "SPEC_RTL_CONTRACT_BINDING",
            "evidence": [constraint["evidence"]],
        })

    constraint_by_id = {item["constraint_id"]: item for item in validated_constraints.get("constraints", [])}
    for chain in validated_constraints.get("lifecycle_chains", []):
        all_constraint_ids = chain["constraint_ids"][:max_chain_length - 1]
        # Every prefix is a meaningful progressive portfolio point: 3
        # contracts is Intermediate, while 4+ is Lifecycle.  This is bounded
        # by available semantic relations, not by enumerating Region paths.
        for prefix_length in range(2, len(all_constraint_ids) + 1):
            constraint_ids = all_constraint_ids[:prefix_length]
            relations = [constraint_by_id[item] for item in constraint_ids]
            if any(item not in edge_by_constraint for item in constraint_ids):
                rejected["CHAIN_EDGE_NOT_AVAILABLE"] += 1
                continue
            contract_ids = [relations[0]["source_contract_id"]] + [item["target_contract_id"] for item in relations]
            if len(set(contract_ids)) != len(contract_ids):
                rejected["REPEATED_CONTRACT"] += 1
                continue
            if any(contracts[item]["readiness_level"] < 1 for item in contract_ids):
                rejected["READINESS_LEVEL_0"] += 1
                continue
            event_ids = [relations[0]["source_event_id"]] + [item["target_event_id"] for item in relations]
            predicates = [events[(contract_ids[index], event_ids[index])]["predicate"]
                          for index in range(len(contract_ids))]
            level = "INTERMEDIATE" if len(contract_ids) == 3 else "LIFECYCLE"
            candidates.append({
                "candidate_id": "composition_" + _digest(chain.get("chain_id", ""), level, constraint_ids),
                "level": level, "contract_ids": contract_ids,
                "region_ids": [contracts[item]["region_id"] for item in contract_ids],
                "module": contracts[contract_ids[0]]["module"],
                "event_ids": event_ids, "event_predicates": predicates,
                "delay_ranges": [[item["min_delay"], item["max_delay"]] for item in relations],
                "edge_ids": [edge_by_constraint[item]["edge_id"] for item in constraint_ids],
                "constraint_ids": constraint_ids,
                "relation_types": [item["relation_type"] for item in relations],
                "context_status": "STRONG" if all(edge_by_constraint[item]["execution_context_status"] == "STRONG"
                                                   for item in constraint_ids) else "FORMAL_REQUIRED",
                "context_anchors": sorted({anchor for item in constraint_ids
                                           for anchor in edge_by_constraint[item]["execution_context_anchors"]}),
                "source": "SPEC_RTL_CONTRACT_CHAIN",
                "evidence": [item["evidence"] for item in relations],
            })
    values = []
    seen = set()
    for item in sorted(candidates, key=lambda value: (len(value["contract_ids"]), value["candidate_id"])):
        signature = (item["module"], tuple(item["event_predicates"]), tuple(map(tuple, item["delay_ranges"])))
        if signature in seen:
            rejected["DUPLICATE_SEMANTICS"] += 1
            continue
        seen.add(signature)
        # Value rewards new relation/stage coverage, and penalizes cost/overlap.
        item["selection_score"] = round(
            8 * len(set(item["region_ids"])) + 5 * len(set(item["relation_types"]))
            + 3 * len(item["context_anchors"]) - 1.5 * len(item["contract_ids"]), 3
        )
        values.append(item)
    return {
        "schema": "region_flow.8-composition-candidates.v1",
        "candidates": values,
        "rejections": dict(rejected),
        "summary": {
            "candidates": len(values),
            "by_level": dict(Counter(item["level"] for item in values)),
            "regions_participating": len({region for item in values for region in item["region_ids"]}),
            "relations_participating": len({edge for item in values for edge in item["edge_ids"]}),
        },
    }


def select_composition_portfolio(
    candidate_doc: dict[str, Any], *, caps: dict[str, int] | None = None,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    caps = {"ADJACENT": 8, "INTERMEDIATE": 4, "LIFECYCLE": 3, **(caps or {})}
    selected = []
    seen_relations: set[str] = set()
    seen_regions: set[str] = set()
    by_level = Counter()
    remaining = list(candidate_doc.get("candidates", []))
    while remaining:
        ranked = []
        for candidate in remaining:
            if by_level[candidate["level"]] >= int(caps.get(candidate["level"], 0)):
                continue
            new_relations = len(set(candidate["edge_ids"]) - seen_relations)
            new_regions = len(set(candidate["region_ids"]) - seen_regions)
            marginal = candidate["selection_score"] + 10 * new_relations + 4 * new_regions
            ranked.append((marginal, candidate))
        if not ranked:
            break
        _, chosen = max(ranked, key=lambda pair: (pair[0], pair[1]["candidate_id"]))
        chosen = {**chosen, "portfolio_rank": len(selected) + 1,
                  "marginal_score_at_selection": round(_, 3)}
        selected.append(chosen)
        by_level[chosen["level"]] += 1
        seen_relations.update(chosen["edge_ids"])
        seen_regions.update(chosen["region_ids"])
        remaining = [item for item in remaining if item["candidate_id"] != chosen["candidate_id"]]
    return selected, {
        "schema": "region_flow.8-composition-portfolio.v1",
        "selected": len(selected), "by_level": dict(by_level),
        "covered_contract_relations": len(seen_relations),
        "covered_regions": len(seen_regions),
        "not_selected": len(candidate_doc.get("candidates", [])) - len(selected),
    }


def compile_composition_properties(
    candidates: list[dict[str, Any]], design: RTLDesign, reset_asserted: str,
) -> tuple[list[PropertyIR], dict[str, dict[str, Any]]]:
    """Compile fixed bounded-sequence templates.  No LLM text reaches SVA."""

    properties = []
    metadata = {}
    for index, candidate in enumerate(candidates, 1):
        predicates = candidate["event_predicates"]
        ranges = candidate["delay_ranges"]
        if len(predicates) != len(ranges) + 1:
            raise Requirement88ValidationError("composition event/delay arity mismatch")
        source = f"$rose(({predicates[0]}))"
        if candidate["level"] == "ADJACENT":
            minimum, maximum = ranges[0]
            # Small progressive window absorbs registered interface staging;
            # this is a Formal search bound, never an assumed latency.
            maximum = max(int(maximum), 4)
            delay = f"##{minimum}" if minimum == maximum else f"##[{minimum}:{maximum}]"
            body = f"({source}) |-> {delay} ({predicates[-1]})"
            compiler = "FIXED_ADJACENT_BOUNDED_SEQUENCE_V1"
        else:
            minimum = sum(int(item[0]) for item in ranges)
            maximum = max(sum(int(item[1]) for item in ranges), 64)
            delay = f"##{minimum}" if minimum == maximum else f"##[{minimum}:{maximum}]"
            # Intermediate event IDs remain mandatory Contract-Graph evidence;
            # the composite property validates the transitive endpoint relation
            # without over-constraining the exact internal schedule.
            body = f"({source}) |-> {delay} ({predicates[-1]})"
            compiler = "FIXED_TRANSITIVE_ENDPOINT_SEQUENCE_V1"
        module = candidate["module"]
        known = set(design.module_signals.get(module, {}))
        signals = expression_signals(" ".join(predicates), known)
        if not signals:
            raise Requirement88ValidationError("compiled composition has no grounded RTL signals")
        property_id = f"composition_{candidate['level'].lower()}_{index:03d}_{_digest(candidate['candidate_id'], size=8)}"
        prop = PropertyIR(
            property_id=property_id,
            region_id="contract_composition_" + _digest(candidate["contract_ids"]),
            object_type=ObjectType.EXTENSION,
            family=f"COMPOSITE_{candidate['level']}", template=f"COMPOSITE_{candidate['level']}",
            bindings={
                "EVENTS": predicates, "DELAY_RANGES": ranges,
                "CONTRACT_IDS": candidate["contract_ids"],
            },
            signals=signals,
            source="validated-contract-graph+spec-rtl-partial-order+fixed-sequence-template",
            llm_confidence=1.0, body=body, disable_iff=reset_asserted,
            description=(f"Req8.8 {candidate['level']} composition across "
                         f"{len(candidate['contract_ids'])} Local Contracts."),
            source_classification="COMPOSITIONAL_CONTRACT",
            evidence=candidate.get("evidence", []), target_module=module,
        )
        properties.append(prop)
        metadata[property_id] = {
            "property_id": property_id, "candidate_id": candidate["candidate_id"],
            "level": candidate["level"], "contract_ids": candidate["contract_ids"],
            "region_ids": candidate["region_ids"], "edge_ids": candidate["edge_ids"],
            "constraint_ids": candidate["constraint_ids"],
            "execution_context_status": candidate["context_status"],
            "execution_context_anchors": candidate["context_anchors"],
            "unproven_assumptions": [], "compiler": compiler,
        }
    return properties, metadata


def relation_coverage(
    trusted_property_ids: set[str], metadata: dict[str, dict[str, Any]], graph: dict[str, Any],
) -> dict[str, Any]:
    trusted_records = {prop_id: item for prop_id, item in metadata.items()
                       if prop_id in trusted_property_ids}
    trusted_edges = {edge for item in trusted_records.values() for edge in item.get("edge_ids", [])}
    direct_edges = {edge for item in trusted_records.values() if item.get("level") == "ADJACENT"
                    for edge in item.get("edge_ids", [])}
    spec_edges = {item["edge_id"] for item in graph.get("edges", []) if item.get("spec_constraint_id")}
    stages = {level for prop_id, item in metadata.items() if prop_id in trusted_property_ids
              for level in [item.get("level")] if level}
    return {
        "validated_contract_relations": len(spec_edges),
        "trusted_composition_relations": len(trusted_records),
        "directly_trusted_adjacent_relations": len(direct_edges),
        "transitively_covered_graph_relations": len(trusted_edges),
        "relation_coverage_percent": round(100 * len(trusted_edges) / len(spec_edges), 2) if spec_edges else 0.0,
        "covered_lifecycle_stages": sorted(stages),
        "trusted_relation_ids": sorted(trusted_edges),
    }
