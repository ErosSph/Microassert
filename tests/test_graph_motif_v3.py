from copy import deepcopy
from pathlib import Path
from dateassertion.rtl_frontend.parser import parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph
from dateassertion.rtl_frontend.graph_patterns import detect_graph_patterns, anonymize_signal_names
from dateassertion.rtl_frontend.graph_motif_library import MOTIFS

FIXTURE = Path(__file__).with_name("fixtures_graph_motifs_v3.sv")

def artifacts():
    return build_semantic_graph(parse_rtl([FIXTURE]))

def test_ansi_port_continuations_inherit_direction_and_width():
    design = parse_rtl([FIXTURE])
    signals = design.module_signals["iter_divide"]
    assert signals["b"].direction == "input"
    assert signals["b"].width == signals["a"].width == "[7:0]"
    assert signals["rst"].direction == signals["start"].direction == "input"
    assert signals["rst"].width == ""

def test_composite_architecture_patterns_have_literal_certificates():
    graph = artifacts()
    doc = detect_graph_patterns(graph)
    found = {(p["module"],p["kind"]) for p in doc["patterns"]}
    assert {"REGISTER_FILE", "LSU", "ITERATIVE_MULTIPLIER", "ITERATIVE_DIVIDER"} <= {m["kind"] for m in MOTIFS}
    for pair in (("bank_2r1w","REGISTER_FILE"), ("load_store_rmw","LSU"),
                 ("iter_multiply","ITERATIVE_MULTIPLIER"), ("iter_divide","ITERATIVE_DIVIDER"),
                 ("case_alu","ALU")):
        assert pair in found, pair
    assert ("bank_same_address","REGISTER_FILE") not in found
    assert ("unrelated_subword_paths","LSU") not in found
    assert ("iter_multiply","ITERATIVE_DIVIDER") not in found
    edges = {(e["source"],e["target"],e["type"]) for e in graph["edges"]}
    for p in doc["patterns"]:
        c=p["match_certificate"]
        assert len(set(c["roles"].values())) == len(c["roles"])
        assert all((e["source"],e["target"],e["type"]) in edges
                   for e in c["required_edges"]+c["composed_edges"])

def test_decode_composition_requires_every_or_arm_and_preserves_dependency():
    doc=detect_graph_patterns(artifacts())
    results={p["anchor_signals"][0] for p in doc["patterns"] if p["kind"]=="DECODE" and p["module"]=="staged_decode"}
    assert "result" in results and "bad" not in results
    assert "merged" in results and "bad_merge" not in results

def test_array_write_index_metadata_and_edge_are_required():
    graph=artifacts()
    write=next(n for n in graph["nodes"] if n.get("module")=="bank_2r1w" and n.get("lhs")=="storage")
    assert write["lhs_expression"]=="storage[wa]"
    graph["edges"]=[e for e in graph["edges"] if not (e["target"]==write["id"] and e.get("dependency_role")=="write_index")]
    assert not any(p["kind"]=="REGISTER_FILE" and p["module"]=="bank_2r1w" for p in detect_graph_patterns(graph)["patterns"])

def test_composites_do_not_infer_from_names_or_invent_cycle_bounds():
    graph=artifacts()
    renamed,mapping=anonymize_signal_names(graph)
    def sig(doc,translate):
        return {(p["module"],p["kind"],tuple(sorted(translate.get(n,n) for n in p["core_node_ids"])))
                for p in doc["patterns"]}
    assert sig(detect_graph_patterns(graph),mapping)==sig(detect_graph_patterns(renamed),{})
    for p in detect_graph_patterns(graph)["patterns"]:
        if p["kind"].startswith("ITERATIVE_"):
            assert "proved_iteration_bound" in p["match_certificate"]["composition_details"]["unresolved_obligations"]

def test_missing_completion_blocks_iterative_claim():
    graph=artifacts()
    for n in graph["nodes"]:
        if n.get("name")=="done":
            n["direction"]="internal"
    assert not any(p["kind"].startswith("ITERATIVE_") for p in detect_graph_patterns(graph)["patterns"])

def test_register_file_does_not_compile_as_scalar_and_reports_observation_gap():
    from dateassertion.pipeline.initial_property_planner import _safety_rejection
    from dateassertion.pipeline.local_region_assertions import build_region_inventory, GENERIC_PRIMITIVES
    design = parse_rtl([FIXTURE])
    write = next(a for a in design.assignments if a.module == "bank_2r1w" and a.lhs == "storage")
    assert "array" in _safety_rejection(write, design)
    region = build_region_inventory({"regions": [dict(region_id="r", kind="REGISTER_FILE")]}, [])["regions"][0]
    assert region["architecture_contract_support"]["mapping_status"] == "LOCAL_INDEXED_RELATIONS_ONLY_PENDING_SPEC"
    assert not region["architecture_contract_support"]["full_architecture_contract_ready"]
    assert len(GENERIC_PRIMITIVES) == 11

def test_unary_zero_test_and_missing_multiplier_bit_shift():
    from dateassertion.rtl_frontend.graph_motif_matching import Matcher
    from dateassertion.rtl_frontend.composite_motifs import CompositeMotifs
    graph = artifacts()
    assert CompositeMotifs(Matcher(graph)).zero_test({"guard": "(!count && busy)"}, "count")
    shift = next(n for n in graph["nodes"] if n.get("module") == "iter_multiply" and
                 n.get("lhs") == "bits" and ">>" in n.get("rhs", ""))
    graph["edges"] = [e for e in graph["edges"] if e["source"] != shift["id"] and e["target"] != shift["id"]]
    assert not any(p["kind"] == "ITERATIVE_MULTIPLIER" for p in detect_graph_patterns(graph)["patterns"])
