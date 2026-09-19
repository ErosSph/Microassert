from pathlib import Path
import pytest
from dateassertion.rtl_frontend.graph_motif_library import MOTIFS
from dateassertion.rtl_frontend.graph_patterns import detect_graph_patterns, anonymize_signal_names
from dateassertion.rtl_frontend.parser import parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph

FIXTURE = Path(__file__).with_name("fixtures_graph_motifs_v2.sv")
# Development diagnostics, NOT a held-out architecture recognition benchmark.
ORACLE = [
    ("unit_counter", "COUNTER", True), ("unit_counter", "ACCUMULATOR", False),
    ("unit_accumulator", "ACCUMULATOR", True), ("unit_accumulator", "COUNTER", False),
    ("unit_mixed_feedback", "COUNTER", False),
    ("unit_shift", "SHIFTER", True), ("unit_add_only", "SHIFTER", False),
    ("unit_compare", "COMPARATOR", True), ("unit_add_only", "COMPARATOR", False),
    ("unit_multiply", "MULTIPLIER", True), ("unit_add_only", "MULTIPLIER", False),
    ("unit_divide", "DIVIDER", True), ("unit_multiply", "DIVIDER", False),
    ("unit_mux", "MUX", True), ("unit_add_only", "MUX", False),
    ("unit_inline_alu", "ALU", True), ("unit_composed_alu", "ALU", True),
    ("unit_mux", "ALU", False), ("unit_selector_arithmetic_not_alu", "ALU", False),
    ("unit_unconnected_operations", "ALU", False),
]

def artifacts():
    return build_semantic_graph(parse_rtl([FIXTURE]))

def test_fourteen_classes_have_executable_motifs():
    # v3 retains all v2 classes and adds four composite architecture classes.
    assert {"COUNTER", "ACCUMULATOR", "SHIFTER", "COMPARATOR", "MULTIPLIER", "DIVIDER", "MUX", "ALU"} <= {m["kind"] for m in MOTIFS}
    found = {(p["module"], p["kind"]) for p in detect_graph_patterns(artifacts())["patterns"]}
    for module, kind, expected in ORACLE:
        assert ((module, kind) in found) == expected, (module, kind)

def test_declaration_net_is_driver_variable_initializer_is_not():
    graph = artifacts()
    producers = {n["lhs"] for n in graph["nodes"] if n["kind"] == "assignment"
                 and n["module"] == "unit_net_vs_variable_initializer"}
    assert "real_driver" in producers
    assert "initial_only" not in producers

def test_composed_alu_certificate_and_renaming():
    graph = artifacts()
    doc = detect_graph_patterns(graph)
    alu = next(p for p in doc["patterns"] if p["kind"] == "ALU" and p["module"] == "unit_composed_alu")
    cert = alu["match_certificate"]
    assert cert["composed_node_ids"] and cert["composed_edges"]
    edges = {(e["source"], e["target"], e["type"]) for e in graph["edges"]}
    assert all((e["source"], e["target"], e["type"]) in edges for e in cert["composed_edges"])
    renamed, mapping = anonymize_signal_names(graph)
    anon = detect_graph_patterns(renamed)
    def signature(data, mapping):
        return {(p["kind"], p["module"], tuple(sorted(mapping.get(n,n) for n in p["core_node_ids"])))
                for p in data["patterns"]}
    assert signature(doc, mapping) == signature(anon, {})

def test_no_hidden_twelve_cap(tmp_path):
    path = tmp_path / "many.sv"
    # Distinct anchors, not 20 writes to the same packed signal.
    path.write_text("module many(input clk,d);\n" + "\n".join(
        f"reg q{i}; always @(posedge clk) q{i} <= d;" for i in range(20)) + "\nendmodule")
    graph = build_semantic_graph(parse_rtl([path]))
    full = detect_graph_patterns(graph)
    capped = detect_graph_patterns(graph, max_candidates_per_kind=12)
    assert full["summary"]["by_kind"]["REGISTER_UPDATE"] == 20
    assert full["summary"]["truncated"] == 0
    assert capped["summary"]["by_kind"]["REGISTER_UPDATE"] == 12
    assert capped["summary"]["truncated"] == 8

def test_topology_ablation_does_not_claim_semantic_predicates():
    full = detect_graph_patterns(artifacts())
    topo = detect_graph_patterns(artifacts(), matching_backend="topology_vf2")
    assert len(topo["patterns"]) > len(full["patterns"])
    assert all(not p["match_certificate"]["satisfied_predicates"] for p in topo["patterns"])
    with pytest.raises(ValueError):
        detect_graph_patterns(artifacts(), matching_backend="legacy_weighted")

def test_alu_does_not_count_operand_preparation_as_selected_operations():
    assert not any(p["module"] == "unit_selected_multiply_not_alu" and p["kind"] == "ALU"
                   for p in detect_graph_patterns(artifacts())["patterns"])
