from copy import deepcopy
from pathlib import Path

import pytest

from dateassertion.rtl_frontend.graph_patterns import detect_graph_patterns, anonymize_signal_names
from dateassertion.rtl_frontend.parser import parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph

FIXTURE = Path(__file__).with_name("fixtures_graph_motifs.sv")
# Presence queries about structural intent, including two alternative encodings.
# Arithmetic pipelines are a distinct semantic class from copy-register stages;
# arithmetic_chain is deliberately NOT a negative pipeline label below.
ORACLE = [
    ("decode_case", "DECODE", True), ("continuous_decode", "DECODE", True),
    ("wide_mux", "DECODE", False), ("boolean_enable", "DECODE", False),
    ("inequality_flag", "DECODE", False), ("negated_comparison", "DECODE", False),
    ("mixed_decode", "DECODE", False), ("counter_feedback", "FSM", False),
    ("fsm_constant", "FSM", True), ("split_fsm", "FSM", True),
    ("copy_pipeline", "PIPELINE", True), ("different_clock", "PIPELINE", False),
    ("opposite_edge", "PIPELINE", False), ("bit_lifecycle", "HANDSHAKE", True),
    ("unrelated_set_clear", "HANDSHAKE", False),
]


def artifacts():
    return build_semantic_graph(parse_rtl([FIXTURE]))


def test_certificate_edges_are_literal_injective_and_attributed():
    graph = artifacts()
    doc = detect_graph_patterns(graph, max_candidates_per_kind=1000)
    literal = {(e["source"], e["target"], e["type"]) for e in graph["edges"]}
    assert doc["weighted_scores_used"] is False
    assert doc["patterns"]
    for item in doc["patterns"]:
        cert = item["match_certificate"]
        assert len(set(cert["roles"].values())) == len(cert["roles"])
        assert cert["satisfied_predicates"]
        assert all((e["source"], e["target"], e["type"]) in literal for e in cert["required_edges"])


def test_required_structure_rejects_diagnostic_negatives():
    found = {(p["module"], p["kind"]) for p in detect_graph_patterns(artifacts())["patterns"]}
    for module, kind, expected in ORACLE:
        if not expected:
            assert (module, kind) not in found
    assert {("decode_case", "DECODE"), ("fsm_constant", "FSM"),
            ("continuous_decode", "DECODE"), ("split_fsm", "FSM"),
            ("copy_pipeline", "PIPELINE"), ("bit_lifecycle", "HANDSHAKE")} <= found


@pytest.mark.parametrize("mutation", ["reverse", "retype", "remove"])
def test_decode_requires_directed_control_edge(mutation):
    graph = artifacts()
    graph = {**graph, "nodes": [n for n in graph["nodes"] if n.get("module") == "decode_case"]}
    ids = {n["id"] for n in graph["nodes"]}
    graph["edges"] = [deepcopy(e) for e in graph["edges"] if e["source"] in ids and e["target"] in ids]
    assert any(p["kind"] == "DECODE" for p in detect_graph_patterns(graph)["patterns"])
    edge = next(e for e in graph["edges"] if e["type"] == "CONTROL")
    if mutation == "reverse":
        edge["source"], edge["target"] = edge["target"], edge["source"]
    elif mutation == "retype":
        edge["type"] = "DATA"
    else:
        graph["edges"].remove(edge)
    assert not any(p["kind"] == "DECODE" for p in detect_graph_patterns(graph)["patterns"])


def test_renaming_preserves_exact_role_witnesses_not_just_counts():
    graph = artifacts()
    anonymous, mapping = anonymize_signal_names(graph)
    original = detect_graph_patterns(graph, max_candidates_per_kind=1000)
    renamed = detect_graph_patterns(anonymous, max_candidates_per_kind=1000)
    def signature(doc, translate):
        return {(p["kind"], p["module"], tuple(sorted((r, translate.get(n, n))
                    for r, n in p["match_certificate"]["roles"].items()))) for p in doc["patterns"]}
    assert signature(original, mapping) == signature(renamed, {})


def test_old_saved_graph_does_not_guess_clock_polarity():
    graph = artifacts()
    for n in graph["nodes"]:
        n.pop("event_control", None)
    assert not any(p["kind"] in {"PIPELINE", "REGISTER_UPDATE", "FSM", "HANDSHAKE"}
                   for p in detect_graph_patterns(graph)["patterns"])


def test_unrecognized_backend_does_not_silently_fall_back():
    with pytest.raises(ValueError):
        detect_graph_patterns(artifacts(), matching_backend="typo")


def test_localparam_state_values_are_structural_evidence():
    graph = build_semantic_graph(parse_rtl([Path(__file__).with_name("fixtures_four_types.sv")]))
    state = next(p for p in detect_graph_patterns(graph)["patterns"] if p["kind"] == "FSM")
    assert state["anchor_signals"] == ["state"]
    constants = {n["name"]: n.get("constant_expression") for n in graph["nodes"]
                 if n.get("signal_kind") == "localparam"}
    assert constants["IDLE"] == "2'b01"
    assert constants["BUSY"] == "2'b10"


def test_non_utf8_parameter_comment_does_not_break_parser(tmp_path):
    source = tmp_path / "params.sv"
    source.write_bytes(b"module dut;\n// \xd6\xd0\xce\xc4\nlocalparam A=1;\nendmodule\n")
    graph = build_semantic_graph(parse_rtl([source]))
    assert next(n for n in graph["nodes"] if n.get("name") == "A")["constant_expression"] == "1"


def test_parse_uses_ordered_compilation_unit_macros_and_keeps_source_location(tmp_path):
    """A defs file can legally control the next RTL file in one compile unit."""

    defs = tmp_path / "00_defs.v"
    dut = tmp_path / "01_dut.v"
    defs.write_text("`define ENABLE_VALUE 1\n", encoding="utf-8")
    dut.write_text("""`ifdef ENABLE_VALUE
module selected(input logic a, output logic y);
  assign y = a & `ENABLE_VALUE;
endmodule
`else
module excluded;
endmodule
`endif
`undef ENABLE_VALUE
`ifdef ENABLE_VALUE
module incorrectly_retained;
endmodule
`endif
""", encoding="utf-8")

    design = parse_rtl([defs, dut])

    assert design.diagnostics == []
    assert [module.name for module in design.modules] == ["selected"]
    assert len(design.assignments) == 1
    assignment = design.assignments[0]
    assert assignment.file == str(dut.resolve())
    assert assignment.line == 3
    assert assignment.rhs == "a & 1"


def test_legacy_ir_adapter_uses_certificate_roles_without_re_guessing():
    from dateassertion.rtl_frontend.region_candidates import extract_candidates
    from dateassertion.ir.schema import ObjectType
    design = parse_rtl([FIXTURE])
    decode = next(p for p in extract_candidates(design, "decode_case") if p.suggested_type == ObjectType.DECODE)
    assert decode.metadata["selector"] == "op"
    pipe = next(p for p in extract_candidates(design, "copy_pipeline") if p.suggested_type == ObjectType.PIPELINE)
    assert pipe.metadata["transfers"] == [{"input": "d", "output": "q"}]
    assert pipe.metadata["register_stages"] == 2
    life = next(p for p in extract_candidates(design, "bit_lifecycle") if p.suggested_type == ObjectType.HANDSHAKE)
    assert life.metadata["request"] == "request"
    assert life.metadata["response"] == "response"
    assert life.metadata["events"]["completed"] is None
    assert life.metadata["match_certificate"]


def test_witness_selection_is_independent_of_python_hash_seed():
    import os
    import subprocess
    import sys
    fixture = Path(__file__).with_name("fixtures_four_types.sv").resolve()
    script = f"""
import json
from dateassertion.rtl_frontend.parser import parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph
from dateassertion.rtl_frontend.graph_patterns import detect_graph_patterns
doc = detect_graph_patterns(build_semantic_graph(parse_rtl([{str(fixture)!r}])))
print(json.dumps([(p['candidate_id'], p['match_certificate']['roles']) for p in doc['patterns']], sort_keys=True))
"""
    outputs = [subprocess.check_output([sys.executable, "-c", script],
               env={**os.environ, "PYTHONHASHSEED": seed}, text=True) for seed in ("7", "19")]
    assert outputs[0] == outputs[1]
