"""Feedback-local graph refinement; semantic names never drive discovery."""

from collections import Counter, defaultdict
from copy import deepcopy
from dataclasses import replace
import hashlib
from math import log1p
from pathlib import Path
import re

from dateassertion.pipeline.formal_gap_semantics import (
    localize_coverage_gaps, refine_gap_classification,
    package_extension_interpretation_context, extension_region_from_interpretation,
    build_elaborated_toggle_mapping_index, resolve_elaborated_toggle_producers,
)
from dateassertion.pipeline.local_region_assertions import (
    enumerate_local_candidate_bindings, select_local_candidate_bindings,
    compile_rtl_properties, deduplicate_exact_properties,
)
from dateassertion.ir.schema import dump_json


def localize_refinement_gaps(items, graph, regions, *, design_map=None):
    """Resolve specialization names and declaration toggles to exact producers.

    Keep official item identity/status intact. Input ports without a local
    producer remain unmapped; a toggle is never evidence of a register update.
    """
    normalized = [replace(item, module=item.module.split(":(", 1)[0]) for item in items]
    records = localize_coverage_gaps(normalized, graph, regions)
    originals = {item.cid: item for item in items}
    nodes = {n["id"]: n for n in graph["nodes"]}
    producers = defaultdict(set)
    owners = defaultdict(set)
    region_modules = {region["region_id"]: region.get("module") for region in regions}
    mapping_index = build_elaborated_toggle_mapping_index(graph, design_map) if design_map else None
    for edge in graph["edges"]:
        if edge["type"] == "DATA" and nodes.get(edge["source"], {}).get("kind") == "assignment":
            producers[edge["target"]].add(edge["source"])
    for region in regions:
        for nid in region.get("core_node_ids", []):
            owners[nid].add(region["region_id"])
    for row in records:
        original = originals[row["cid"]]
        row["elaborated_module"] = original.module
        row["instance"] = original.instance
        # stable_cover_item_id includes elaborated module identity.
        from dateassertion.pipeline.formal_gap_semantics import stable_cover_item_id
        row["rtl_item_id"] = stable_cover_item_id(original)
        if original.status != "uncovered_or_unchecked" or original.cover_item_type != "toggle":
            continue
        signal_ids = {nid for nid in row["graph_node_ids"] if nodes[nid]["kind"] == "signal"}
        quoted = re.search(r'"([^"\n]+)"', original.description)
        if quoted:
            name = re.sub(r"\[[^\]]+\]$", "", quoted[1]).rsplit(".", 1)[-1]
            nid = f"signal:{row['module']}.{name}"
            # Require the reported declaration location as well as the name.
            source = nodes.get(nid, {}).get("source", {})
            signal_ids = set()
            if source.get("file") == original.file and source.get("line") == original.line_start:
                signal_ids = {nid}
        assignment_ids = {aid for nid in signal_ids for aid in producers[nid]}
        if assignment_ids:
            row["graph_node_ids"] = sorted(signal_ids | assignment_ids)
            row["existing_region_ids"] = sorted({rid for nid in row["graph_node_ids"] for rid in owners[nid]})
            row["gap_type"] = "B_CONTRACT_GAP" if row["existing_region_ids"] else "A_REGION_GAP"
            row["diagnosis_reason"] = "declaration toggle traced through literal DATA result edges to local producers"
            row["producer_resolution"] = "EXACT_TYPED_DATA_EDGE"
        else:
            row["graph_node_ids"] = sorted(signal_ids)
            row["existing_region_ids"] = sorted({rid for nid in signal_ids for rid in owners[nid]})
            row["gap_type"] = "D_NON_ACTIONABLE"
            row["diagnosis_reason"] = "reported toggle has no exact declaration-to-local-producer path"
            if design_map:
                resolved = resolve_elaborated_toggle_producers(original, graph, design_map, mapping_index=mapping_index)
                row["hierarchical_mapping_audit"] = resolved
                recovered = set(resolved.get("producer_assignment_ids", []))
                if recovered:
                    row["graph_node_ids"] = sorted(signal_ids | recovered | set(resolved.get("signal_node_ids", [])))
                    producer_modules = {nodes[nid]["module"] for nid in recovered}
                    # The child port explains the coverage item's provenance;
                    # its Region does not own the parent's update obligation.
                    producer_context = {nid for nid in row["graph_node_ids"] if nodes[nid].get("module") in producer_modules}
                    row["existing_region_ids"] = sorted({rid for nid in producer_context for rid in owners[nid]
                                                         if region_modules.get(rid) in producer_modules})
                    row["gap_type"] = "B_CONTRACT_GAP" if row["existing_region_ids"] else "A_REGION_GAP"
                    row["diagnosis_reason"] = "exact elaborated DATA port connection traced to producer assignments"
                    row["producer_resolution"] = resolved["producer_resolution"]
    return refine_gap_classification(records, graph, regions)


def discover_refinement_candidates(records, graph, regions, *, max_regions=32, max_assignments=16, depth=2):
    """Seed producer families at gaps and grow bounded upstream typed motifs.

    Same-target assignments are indivisible. Expansion follows DATA producers
    and CONTROL predicates, never arbitrary shared clock/reset fanout. Ranking
    round-robins modules and rewards new gap items over already selected cones.
    """
    nodes = {n["id"]: n for n in graph["nodes"]}
    incoming = defaultdict(list)
    families = defaultdict(set)
    owners = defaultdict(set)
    region_by_id = {r["region_id"]: r for r in regions}
    for edge in graph["edges"]:
        if edge["type"] in {"DATA", "CONTROL", "SEQUENTIAL"}:
            incoming[edge["target"]].append(edge)
    for node in nodes.values():
        if node["kind"] == "assignment":
            families[(node["module"], node["lhs"])].add(node["id"])
    for region in regions:
        for nid in region.get("core_node_ids", []):
            owners[nid].add(region["region_id"])
    gaps_by_node = defaultdict(set)
    for row in records:
        if row["official_status"] == "uncovered_or_unchecked" and row["gap_type"] != "D_NON_ACTIONABLE":
            for nid in row["graph_node_ids"]:
                gaps_by_node[nid].add(row["rtl_item_id"])
    proposals = []
    for (module, target), family in sorted(families.items()):
        seed_gaps = set().union(*(gaps_by_node[nid] for nid in family))
        if not seed_gaps:
            continue
        parent_ids = set().union(*(owners[nid] for nid in family))
        broad = {rid for rid in parent_ids if region_by_id[rid].get("kind") == "DATAPATH"}
        if parent_ids and not broad:
            continue
        selected = set(family)
        frontier = set(family)
        for _ in range(depth):
            additions = set()
            for nid in sorted(frontier):
                for edge in incoming[nid]:
                    sid = edge["source"]
                    for producer_edge in incoming[sid]:
                        aid = producer_edge["source"]
                        node = nodes.get(aid, {})
                        if node.get("kind") == "assignment" and node.get("module") == module:
                            additions.update(families[(module, node["lhs"])])
            frontier = set()
            for nid in sorted(additions - selected):
                family_add = families[(module, nodes[nid]["lhs"])] - selected
                if len(selected | family_add) <= max_assignments:
                    frontier.update(family_add)
                    selected.update(family_add)
        if len(selected) > max_assignments:
            continue
        local_ids = set(selected)
        for nid in selected:
            local_ids.add(f"signal:{module}.{nodes[nid]['lhs']}")
            local_ids.update(e["source"] for e in incoming[nid])
        local_ids &= nodes.keys()
        edges = [e for e in graph["edges"] if e["source"] in local_ids and e["target"] in local_ids]
        cuts = [e for e in graph["edges"] if (e["source"] in local_ids) != (e["target"] in local_ids)]
        signals = [nodes[nid] for nid in sorted(local_ids) if nodes[nid]["kind"] == "signal"]
        produced = {nodes[nid]["lhs"] for nid in selected}
        inputs = sorted(n["name"] for n in signals if n["name"] not in produced)
        outgoing_cut_signals = {e["source"] for e in cuts if e["source"] in local_ids}
        outputs = sorted(n["name"] for n in signals if n["name"] in produced and (
            n.get("direction") == "output" or n["id"] in outgoing_cut_signals or n["name"] == target))
        source_groups = defaultdict(list)
        for nid in selected:
            source_groups[nodes[nid]["source"]["file"]].append(int(nodes[nid]["source"]["line"]))
        # A module's motif must have one literal source file.
        if len(source_groups) != 1:
            continue
        file, lines = next(iter(source_groups.items()))
        file_lines = Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
        evidence = {"file": file, "line_start": min(lines), "line_end": max(lines),
                    "snippet": "\n".join(f"L{line}: {file_lines[line-1]}" for line in sorted(set(lines)))}
        gap_ids = set().union(*(gaps_by_node[nid] for nid in local_ids))
        digest = hashlib.sha256("|".join(sorted(selected)).encode()).hexdigest()[:14]
        proposals.append({
            "schema": "region_refinement-extension-candidate.v1", "region_id": f"region_refinement_{digest}",
            "module": module, "candidate_kind": "EXTENSION", "residual_target": target,
            "refinement_subtype": "REGION_REFINEMENT" if broad else "NEW_REGION",
            "parent_region_ids": sorted(broad), "gap_item_ids": sorted(gap_ids),
            "core_node_ids": sorted(local_ids), "assignment_node_ids": sorted(selected),
            "local_graph_nodes": [nodes[nid] for nid in sorted(local_ids)], "local_graph_edges": edges,
            "signals": sorted(n["name"] for n in signals), "inputs": inputs, "outputs": outputs,
            "important_state_candidates": sorted({nodes[nid]["lhs"] for nid in selected if nodes[nid].get("timing") == "next_cycle"}),
            "important_event_candidates": sorted({nodes[e["source"]]["name"] for e in edges if e["type"] == "CONTROL" and nodes[e["source"]]["kind"] == "signal"}),
            "source_evidence": evidence, "whole_design_rtl_supplied": False,
            "boundary": {"semantic_cut_edges": cuts, "imported_signals": inputs, "exported_signals": outputs},
            "structural_evidence": {"algorithm": "BOUNDED_UPSTREAM_TYPED_PRODUCER_MOTIF", "depth": depth,
                "assignment_count": len(selected), "edge_types": dict(Counter(e["type"] for e in edges)),
                "parent_graph_sizes": {rid: len(region_by_id[rid].get("core_node_ids", [])) for rid in broad}},
        })
    chosen, seen_assignments, seen_gaps, module_counts = [], set(), set(), Counter()
    while proposals and len(chosen) < max_regions:
        def score(c):
            novel = len(set(c["gap_item_ids"]) - seen_gaps)
            overlap = len(set(c["assignment_node_ids"]) & seen_assignments) / len(c["assignment_node_ids"])
            return (log1p(novel) + 0.5 * bool(c["parent_region_ids"])) * (1-overlap) / (1+module_counts[c["module"]])
        candidate = max(proposals, key=lambda c: (score(c), c["region_id"]))
        value = score(candidate)
        proposals.remove(candidate)
        if value <= 0:
            break
        candidate["selection_score"] = round(value, 6)
        chosen.append(candidate)
        seen_assignments.update(candidate["assignment_node_ids"])
        seen_gaps.update(candidate["gap_item_ids"])
        module_counts[candidate["module"]] += 1
    by_gap = defaultdict(list)
    for candidate in chosen:
        for gid in candidate["gap_item_ids"]:
            by_gap[gid].append(candidate)
    for row in records:
        refinements = [c for c in by_gap[row["rtl_item_id"]] if c["parent_region_ids"]]
        if refinements:
            row.update(gap_type="A_REGION_GAP", type_a_subtype="REGION_REFINEMENT",
                       type_a_subtype_reason="existing broad Region contains a selected gap-seeded typed motif",
                       refinement_candidate_ids=[c["region_id"] for c in refinements])
            row["priority"]["eligible_for_refinement"] = True
            row["priority"]["prior_disposition"] = row["priority"].get("disposition")
            row["priority"]["disposition"] = "REGION_REFINEMENT_SELECTED"
            row["priority"]["refinement_selection"] = {
                "method": "gap novelty, overlap and module diversity; separate from legacy gap threshold",
                "candidate_scores": {c["region_id"]: c["selection_score"] for c in refinements},
            }
    return chosen


def ground_refinement_roles(candidate, interpretation):
    """Keep semantic role proposals distinct from graph-certified interfaces."""
    proposed = {"inputs": interpretation["inputs"], "outputs": interpretation["outputs"],
                "state": interpretation["important_state"], "events": interpretation["important_events"]}
    allowed = {
        "inputs": set(candidate["inputs"]), "outputs": set(candidate["outputs"]),
        "state": set(candidate["important_state_candidates"]),
        "events": set(candidate["important_event_candidates"]),
    }
    # A one-bit boundary control can be used as an event. A wide datapath value
    # does not become an event because its identifier sounds like a request.
    allowed["events"].update(n["name"] for n in candidate["local_graph_nodes"]
        if n["kind"] == "signal" and n.get("width") == 1)
    grounded = {key: sorted(set(values) & allowed[key]) for key, values in proposed.items()}
    # Structural input/output sets and owned sequential state are complete;
    # the LLM may select interesting roles but cannot redefine the boundary.
    for key in ("inputs", "outputs", "state"):
        grounded[key] = sorted(allowed[key])
    return {**grounded, "llm_proposed_roles": proposed,
        "role_grounding": {"policy": "typed boundary and temporal producers are authoritative",
            "unsupported_proposals": {key: sorted(set(values)-allowed[key]) for key, values in proposed.items()},
            "state_scope": "owned next-cycle producers; outside or unresolved state proposals remain unconfirmed"}}


def interpret_refinements(candidates, regions, spec, client, root, *, attempts=4):
    from dateassertion.pipeline.gap_interpretation import _validated_llm_interpretation
    prompt = (Path(__file__).resolve().parents[1] / "llm/prompts/gap_interpretation.txt").read_text()
    extensions, calls = [], []
    for candidate in candidates:
        nearby = [r for r in regions if r["region_id"] in candidate["parent_region_ids"]]
        context = package_extension_interpretation_context(candidate, nearby, [])
        context["coverage_gap_description"].update(
            subtype=candidate["refinement_subtype"],
            reason="gap-seeded local motif refines a coarse Region or supplies a missing Region",
            parent_region_ids=candidate["parent_region_ids"],
        )
        context["boundary"] = candidate["boundary"]
        path = root / candidate["region_id"]
        dump_json(path / "context.json", context)
        interpretation, call = _validated_llm_interpretation(client, prompt, context, path / "calls.json", attempts=attempts)
        extension = extension_region_from_interpretation(candidate, interpretation)
        extension.update(ground_refinement_roles(candidate, interpretation))
        extension.update(kind="EXTENSION", extension_type=interpretation["candidate_region_name"],
                         parent_region_ids=candidate["parent_region_ids"],
                         creation_reason=candidate["refinement_subtype"], boundary=candidate["boundary"],
                         coi={"node_ids": candidate["core_node_ids"], "nodes": candidate["local_graph_nodes"], "edges": candidate["local_graph_edges"]})
        extensions.append(extension)
        calls.append(call)
        dump_json(path / "extension_region.json", extension)
    return extensions, {"provider": getattr(client.config, "provider", "deepseek"), "calls": sum(c["calls"] for c in calls),
        "api_calls_this_run": sum(c["api_calls_this_run"] for c in calls),
        "real_response_artifacts": sum(c["real_response_artifacts"] for c in calls),
        "generated_sva": False, "regions": calls}


def compile_refinement_properties(pool, extensions, design, reset_asserted, root, *, deduplicate=True):
    # A local equation remains local when one of its signals also crosses a
    # module boundary. Cross-module relations still require composition gates.
    scoped = []
    scope_audit = []
    for candidate in pool:
        item = deepcopy(candidate)
        anchors = set(item.rtl_relation.get("assignment_ids", []))
        anchors.add(item.rtl_relation.get("assignment_id", ""))
        matches = [r for r in extensions if r["module"] == item.module and anchors & set(r["core_node_ids"])]
        if not matches:
            continue
        if item.scope == "CROSS_REGION" and not item.semantic_path:
            item.scope = "LOCAL"
            scope_audit.append({"candidate_id": item.candidate_id, "reason": "single-module exact relation; port connectivity alone does not make its equation cross-module"})
        scoped.append(item)
    bindings = enumerate_local_candidate_bindings(scoped, {"regions": extensions}, design, reset_asserted, recall_mode=True)
    selected, selection = select_local_candidate_bindings(bindings, budget=100000, selection_policy="all_grounded_exact_sva")
    properties, template_bindings, metadata = compile_rtl_properties(selected, design, reset_asserted)
    duplicates = []
    if deduplicate:
        properties, template_bindings, metadata, duplicates = deduplicate_exact_properties(properties, template_bindings, metadata)
    for prop in properties:
        old = prop.property_id
        prop.property_id = "extension_" + old
        prop.iteration_added = 1
        metadata[prop.property_id] = {**metadata.pop(old), "property_id": prop.property_id}
        for binding in template_bindings:
            if binding.property_id == old:
                binding.property_id = prop.property_id
    dump_json(root / "scope_audit.json", scope_audit)
    dump_json(root / "template_bindings.json", template_bindings)
    dump_json(root / "property_metadata.json", metadata)
    contract_records = []
    for item in selected:
        property_ids = {pid for pid, value in metadata.items() if value["candidate_id"] == item.candidate.candidate_id}
        contract_records.append({
            "candidate_id": item.candidate.candidate_id, "region_id": item.primary_region_id,
            "grounded_source_contract": item.candidate.contract,
            "bound_template_contract_ids": sorted({b.contract_id for b in template_bindings if b.property_id in property_ids}),
            "generated_property_ids": sorted(property_ids),
            "primitive": item.candidate.primitive,
            "semantic_obligation": item.candidate.obligation,
            "binding_evidence": item.binding_evidence_by_region[item.primary_region_id],
            "phase": "grounded generic contract before local template identity rebinding",
        })
    dump_json(root / "grounded_contracts.json", {"contracts": contract_records,
        "source": "Req10 grounded candidate pool; exact compiler bindings retained separately"})
    dump_json(root / "selection.json", selection)
    dump_json(root / "exact_duplicates.json", duplicates)
    return properties, metadata
