from pathlib import Path

from dateassertion.ir.schema import ContractIR
from dateassertion.pipeline.contract_grounding import check_rule, ground_contracts
from dateassertion.rtl_frontend.parser import parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph, infer_signal_role


FIXTURE = Path(__file__).with_name("fixtures_grounding.sv")


def _design_graph():
    design = parse_rtl([FIXTURE])
    return design, build_semantic_graph(design)


def _rule(primitive, **roles):
    return {"primitive": primitive, "roles": roles}


def test_semantic_graph_has_required_edge_kinds_and_context():
    design, graph = _design_graph()
    assert {"IDLE", "BUSY"} <= set(design.module_signals["grounding_flow_fixture"])
    assert {"DATA", "CONTROL", "SEQUENTIAL"} <= {item["type"] for item in graph["edges"]}
    assert any(item["assignment_kind"] == "continuous" and item["lhs"] == "passthrough" for item in graph["assignments"])
    seq = next(item for item in graph["assignments"] if item["lhs"] == "seq_result" and item["rhs"] == "comb_result")
    assert seq["timing"] == "next_cycle"
    assert seq["clock"] == "clk"
    assert "!(!resetn)" in seq["guard"] and "(en)" in seq["guard"]


def test_combinational_and_sequential_timing_are_deterministic():
    design, graph = _design_graph()
    same = check_rule(_rule("UPDATE", CONDITION="1'b1", TARGET="passthrough", VALUE="a", DELAY=0), "grounding_flow_fixture", design, graph)
    nxt = check_rule(_rule("UPDATE", CONDITION="!resetn && en", TARGET="seq_result", VALUE="comb_result", DELAY=1), "grounding_flow_fixture", design, graph)
    assert same["deterministic_facts"]["timing"]["value"] == "same_cycle"
    assert nxt["deterministic_facts"]["timing"]["value"] == "next_cycle"


def test_if_else_if_and_case_guards_include_priority_conditions():
    design, graph = _design_graph()
    subtraction = next(item for item in graph["assignments"] if item["lhs"] == "comb_result" and item["rhs"] == "a - b")
    assert "!(opcode == 7'h33" in subtraction["guard"]
    assert "funct7 == 7'h20" in subtraction["guard"]
    case_update = next(item for item in graph["assignments"] if item["lhs"] == "narrow_result" and item["rhs"] == "a[7:0]")
    assert "state ==? IDLE" in case_update["guard"]
    assert "state ==? 2'd2" in case_update["guard"]
    assert "==? ," not in case_update["guard"]
    assert "(en)" in case_update["guard"]


def test_missing_funct7_and_wrong_delay_are_found_then_grounded():
    design, graph = _design_graph()
    contract = ContractIR(
        contract_id="c", object_type="EXEC", ontology_classification="NEW_OBJECT_CANDIDATE",
        region="r", module="grounding_flow_fixture",
        invariants=[_rule("UPDATE", CONDITION="opcode == 7'h33 && funct3 == 3'h0", TARGET="comb_result", VALUE="a + b", DELAY=1)],
    )
    grounded, results, _metrics = ground_contracts([contract], design, graph)
    record = results["objects"][0]["rules"][0]
    assert {item["category"] for item in record["findings"]} >= {"TIMING_CONFLICT", "GUARD_TOO_WEAK"}
    assert record["disposition"] == "REFINED_VALID"
    roles = grounded[0].invariants[0]["roles"]
    assert roles["DELAY"] == 0
    assert "funct7 == 7'h00" in roles["CONDITION"]


def test_width_type_and_predicate_conflicts_are_preformal():
    design, graph = _design_graph()
    mismatch = check_rule(_rule("DATA_INTEGRITY", CONDITION="en", SOURCE="a", TARGET="narrow_result", DELAY=0), "grounding_flow_fixture", design, graph)
    mutex = check_rule(_rule("MUTUAL_EXCLUSION", SIGNALS=["a", "b"]), "grounding_flow_fixture", design, graph)
    assert mismatch["result"] == "TYPE_CONFLICT"
    assert mutex["result"] == "TYPE_CONFLICT"


def test_role_inference_covers_event_state_data_address_counter_payload():
    design, _graph = _design_graph()
    assert infer_signal_role(design, "grounding_flow_fixture", "event_o")["role"] in {"event", "predicate"}
    assert infer_signal_role(design, "grounding_flow_fixture", "state")["role"] == "state"
    assert infer_signal_role(design, "grounding_flow_fixture", "comb_result")["role"] in {"data", "state"}
    assert infer_signal_role(design, "grounding_flow_fixture", "mem_addr")["role"] == "address"
    assert infer_signal_role(design, "grounding_flow_fixture", "cycle_counter")["role"] == "counter"
    assert infer_signal_role(design, "grounding_flow_fixture", "write_data")["role"] == "payload"
    assert infer_signal_role(design, "grounding_flow_fixture", "en")["role"] in {"control", "predicate"}
    roles = {item["role"] for item in build_semantic_graph(design)["roles"]}
    assert {"predicate", "state", "data", "address", "counter", "payload"} <= roles


def test_reset_priority_register_transfer_and_unsupported_binding():
    design, graph = _design_graph()
    reset = check_rule(_rule("RESET", RESET="!resetn", TARGET="seq_result", VALUE="32'h0"), "grounding_flow_fixture", design, graph)
    transfer = check_rule(_rule("UPDATE", CONDITION="!resetn && en", TARGET="seq_result", VALUE="comb_result", DELAY=1), "grounding_flow_fixture", design, graph)
    unsupported = check_rule(_rule("PROGRESS", START="en", END="event_o", MAX_DELAY=4), "grounding_flow_fixture", design, graph)
    ambiguous = check_rule(_rule("MUTUAL_EXCLUSION", SIGNALS=["en", "event_o"]), "grounding_flow_fixture", design, graph)
    incoherent = check_rule(_rule("CAUSALITY", CAUSE="resetn", EFFECT="event_o", DELAY=0), "grounding_flow_fixture", design, graph)
    assert reset["result"] == "VALID"
    assert transfer["result"] in {"VALID", "GUARD_TOO_WEAK"}
    assert unsupported["result"] == "UNSUPPORTED_SEMANTICS"
    assert ambiguous["result"] == "AMBIGUOUS"
    assert incoherent["result"] == "BOUNDARY_INCOHERENT"
