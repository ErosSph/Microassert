"""Additional fixed invariant obligations from complete graph producer families.

This is an explicit companion to local relation enumeration, not a claim that
RTL-derived invariants prove independent SPEC requirements. No new assumptions.
"""
import hashlib
from dateassertion.ir.schema import ContractIR
from dateassertion.ontology.primitives import bind_extension_primitives
from dateassertion.rtl_frontend.graph_motif_matching import Matcher, bare_name, same_clock
from dateassertion.rtl_frontend.invariant_patterns import constant_value, onehot_progress

ARCHITECTURE_PRIMITIVES = ("STATE_LEGAL", "ONEHOT_STATE", "ONEHOT_STEP", "INDEXED_READ", "INDEXED_WRITE")


def compile_architecture_contracts(design, graph, inventory, reset_asserted):
    m = Matcher(graph)
    contracts, audit, region_by_contract, evidence_by_contract = [], [], {}, {}
    seen = set()
    for region in inventory.get("regions", []):
        kind = region.get("kind")
        if kind not in {"FSM", "ONEHOT_PROGRESS"}:
            continue
        cert = region.get("match_certificate") or {}
        roles = cert.get("roles", {})
        state = roles.get("state")
        if state not in m.index.nodes:
            continue
        symbol = m.index.nodes[state]
        width = m.index.signal_width(state)
        if not width or width <= 1 or str(symbol.get("signal_kind", "")).endswith("_array"):
            continue
        target = symbol["name"]
        scope = roles.get("next", state) if kind == "FSM" else state
        family = [m.index.nodes[a] for a in m.family(scope)]
        failure = ""
        if kind == "ONEHOT_PROGRESS":
            failure, evidence, detail = onehot_progress(m, state)
            primitive, bindings = "ONEHOT_STATE", {"TARGET": target}
            from dateassertion.rtl_frontend.invariant_patterns import reset_guard_asserted
            resets = [n for n in family if constant_value(m,n) is not None and
                      reset_guard_asserted(n.get("guard", ""),reset_asserted)]
            if not resets and not failure:
                seeds = [n.get("guard") or "1'b1" for n in family if constant_value(m,n) is not None]
                primitive = "ONEHOT_STEP"
                bindings = {"TARGET":target,"SEED":" || ".join(f"({s})" for s in sorted(set(seeds)))}
        else:
            evidence = set(m.family(scope)) | set(m.family(state)) | {scope, state}
            values = []
            if scope == state and not same_clock(family):
                failure = "unknown_or_mixed_clock"
            for n in family:
                if n.get("lhs_expression", n["lhs"]) != n["lhs"]:
                    failure = "partial_destination"
                    break
                if bare_name(n["rhs"]) in {target, m.index.nodes[scope]["name"]}:
                    continue
                value = constant_value(m, n)
                if value is None or not 0 <= value < (1 << width):
                    failure = "non_constant_or_out_of_range_state_value"
                    break
                values.append(value)
            if not values or len(set(values)) == 1 << width:
                failure = "no_nontrivial_state_set"
            primitive = "STATE_LEGAL"
            bindings = {"TARGET": target, "VALUES": [f"{width}'d{v}" for v in sorted(set(values))]}
        key = (region["module"], primitive, target)
        if key in seen:
            continue
        seen.add(key)
        if failure:
            audit.append({"module":region["module"],"target":target,"primitive":primitive,
                          "status":"NOT_GENERATED","reason":failure})
            continue
        token = hashlib.sha256(repr(key).encode()).hexdigest()[:12]
        rid = f"arch_{primitive.lower()}_{token}"
        ev = [{"files":[m.index.nodes[n]["source"]["file"]],
               "line_start":m.index.nodes[n]["source"]["line"],
               "line_end":m.index.nodes[n]["source"]["line"],"node_id":n}
              for n in sorted(evidence) if m.index.nodes[n].get("source", {}).get("file")]
        contracts.append(ContractIR(contract_id=f"contract_{rid}",object_type=kind,
            ontology_classification="NEW_OBJECT_CANDIDATE",region=rid,module=region["module"],
            state=[target],invariants=[{"primitive":primitive,"roles":bindings,
                "semantics":"Complete-producer structural invariant candidate; SPEC correctness is separate."}],
            evidence=ev,reused_primitives=[primitive]))
        region_by_contract[rid] = region
        evidence_by_contract[rid] = ev
        audit.append({"module":region["module"],"target":target,"primitive":primitive,
                      "status":"GENERATED_CANDIDATE","evidence_node_ids":sorted(evidence),"roles":bindings,
                      "source_classification":"RTL_STRUCTURAL","SPEC_conformance":False})
    from dateassertion.pipeline.indexed_storage_contracts import indexed_storage_records
    indexed, indexed_rejections = indexed_storage_records(design, m, inventory)
    for region, primitive, bindings, evidence in indexed:
        token = hashlib.sha256(repr((region["module"],primitive,sorted(bindings.items()))).encode()).hexdigest()[:12]
        rid = f"arch_{primitive.lower()}_{token}"
        ev = [{"files":[m.index.nodes[n]["source"]["file"]],"line_start":m.index.nodes[n]["source"]["line"],
               "line_end":m.index.nodes[n]["source"]["line"],"node_id":n} for n in sorted(evidence)
              if m.index.nodes[n].get("source",{}).get("file")]
        contracts.append(ContractIR(contract_id=f"contract_{rid}",object_type="REGISTER_FILE",
            ontology_classification="NEW_OBJECT_CANDIDATE",region=rid,module=region["module"],
            invariants=[{"primitive":primitive,"roles":bindings,
                "semantics":"Indexed element relation with actual writer priority; not a full register-file SPEC."}],
            evidence=ev,reused_primitives=[primitive]))
        region_by_contract[rid], evidence_by_contract[rid] = region, ev
        audit.append({"module":region["module"],"primitive":primitive,"roles":bindings,
                      "status":"GENERATED_CANDIDATE","SPEC_conformance":False,"evidence_node_ids":sorted(evidence)})
    audit.extend({**r,"status":"NOT_GENERATED"} for r in indexed_rejections)
    props, templates = bind_extension_primitives(contracts,
        {module:set(signals) for module,signals in design.module_signals.items()},reset_asserted)
    metadata = {}
    for prop in props:
        old = prop.region_id
        region = region_by_contract[old]
        prop.region_id = region["region_id"]
        prop.source = "complete-producer-family+fixed-architecture-invariant"
        prop.source_classification = "RTL_STRUCTURAL"
        prop.llm_confidence = 1.0
        metadata[prop.property_id] = {
            "property_id":prop.property_id,"origin":"RTL_ONLY","source_classification":"RTL_STRUCTURAL",
            "module":prop.target_module,"region_id":prop.region_id,"region_ids":[prop.region_id],
            "obligation":prop.template,"semantic_obligation":prop.template,"primitive":prop.template,
            "family":prop.family,"candidate_id":prop.property_id,"assignment_id":"",
            "selection_rank":None,"selection_score":None,"rtl_evidence":evidence_by_contract[old],
            "primary_binding_evidence":{"binding_level":"EXACT_CORE","binding_rank":3},
            "binding_evidence_by_region":{prop.region_id:{"binding_level":"EXACT_CORE","binding_rank":3}}}
        for template in templates:
            if template.property_id == prop.property_id:
                template.region_id = prop.region_id
    return props, templates, metadata, {"candidates":audit,"contracts":contracts,
        "source":"RTL_STRUCTURAL_NOT_INDEPENDENT_SPEC","compiler_primitives":list(ARCHITECTURE_PRIMITIVES)}
