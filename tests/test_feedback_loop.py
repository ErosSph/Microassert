from __future__ import annotations

from pathlib import Path

import pytest

from dateassertion.coverage_analysis.proof_core import CoverItem
from dateassertion.ir.schema import FormalPropertyResult, FormalRunResult, ObjectType, PropertyIR, dump_json


def _contract(identifier: str, *, inputs=(), outputs=(), state=(), readiness=2) -> dict:
    return {
        "contract_id": identifier, "region_id": f"region_{identifier}", "module": "dut",
        "region_kind": "REGISTER_UPDATE", "readiness_level": readiness,
        "interface": {"inputs": list(inputs), "outputs": list(outputs), "state": list(state), "events": []},
        "trusted_local_obligations": [],
    }


def _prop(identifier: str = "initial") -> PropertyIR:
    return PropertyIR(
        property_id=identifier, region_id="region_a", object_type=ObjectType.EXTENSION,
        family="PRIMITIVE_DATA_INTEGRITY", template="DATA_INTEGRITY", bindings={},
        signals=["a", "q"], source="test", llm_confidence=1.0,
        body="(1'b1) |-> q == a", disable_iff="!rst_n", target_module="dut",
    )


def _coverage_item(
    status: str = "covered_and_checked", *, cid: int = 1, line: int = 1,
    formal_status: str = "", checker_status: str = "",
) -> CoverItem:
    return CoverItem(
        cid=cid, status=status, formal_status=formal_status, checker_status=checker_status,
        cover_item_type="statement", description="assignment", expression="", module="dut",
        instance="", file="/tmp/dut.sv", line_start=line, column_start=1, line_end=line, column_end=1,
    )


def test_effective_denominator_status_migration_is_recorded_but_not_an_identity_failure():
    from dateassertion.pipeline.feedback_loop import (
        _coverage_delta,
        _coverage_identity,
        _rtl_coverage_identity_is_stable,
    )

    # This contains the observed category: unreachable/undetectable ->
    # checked.  The third item becomes reachable but remains unchecked, which
    # verifies that a denominator-only change is not reported as a new checked
    # item.
    previous = [
        _coverage_item("uncovered_or_unchecked", cid=1, line=1),
        _coverage_item("unreachable_or_undetectable", cid=2, line=2),
        _coverage_item("unreachable_or_undetectable", cid=3, line=3),
    ]
    current = [
        _coverage_item("covered_and_checked", cid=1, line=1),
        _coverage_item("covered_and_checked", cid=2, line=2),
        _coverage_item("uncovered_or_unchecked", cid=3, line=3),
    ]
    gain = _coverage_delta(previous, current)

    assert gain["item_universe_constant"] is True
    assert gain["source_identity_constant"] is True
    assert gain["effective_denominator_before"] == 1
    assert gain["effective_denominator_after"] == 3
    # Only the two real transitions into covered_and_checked count as a gain;
    # the undetectable -> unchecked denominator migration contributes zero.
    assert gain["new_checked_items"] == 2
    assert gain["status_transition_counts"] == {
        "uncovered_or_unchecked->covered_and_checked": 1,
        "unreachable_or_undetectable->covered_and_checked": 1,
        "unreachable_or_undetectable->uncovered_or_unchecked": 1,
    }
    assert any(
        row["before_status"] == "unreachable_or_undetectable"
        and row["after_status"] == "covered_and_checked"
        and row["rtl_item_id"]
        for row in gain["status_transitions"]
    )
    assert _rtl_coverage_identity_is_stable(
        gain, _coverage_identity(current), _coverage_identity(previous),
    ) is True


def test_true_rtl_cover_item_universe_drift_still_fails_identity_gate():
    from dateassertion.pipeline.feedback_loop import (
        _coverage_delta,
        _coverage_identity,
        _rtl_coverage_identity_is_stable,
    )

    previous = [_coverage_item("covered_and_checked", cid=1, line=1)]
    # A source-coordinate change creates a different stable RTL item identity.
    current = [_coverage_item("covered_and_checked", cid=1, line=2)]
    gain = _coverage_delta(previous, current)
    assert gain["item_universe_constant"] is False
    assert gain["item_ids_added"] and gain["item_ids_removed"]
    assert _rtl_coverage_identity_is_stable(
        gain, _coverage_identity(current), _coverage_identity(previous),
    ) is False


def test_incremental_graph_recomputes_changed_contract_incident_edges_only():
    from dateassertion.pipeline.feedback_loop import incremental_contract_graph
    from dateassertion.pipeline.local_contract_composition import build_contract_graph

    original = [_contract("a", outputs=("x",)), _contract("b", inputs=("x",), outputs=("y",)), _contract("c", inputs=("y",))]
    previous = build_contract_graph({"contracts": original}, {"constraints": []})
    revised = [_contract("a", outputs=("x",)), _contract("b", inputs=("x",), outputs=("z",)), _contract("c", inputs=("y",))]
    graph, audit = incremental_contract_graph(previous, revised, {"constraints": []}, {"b"})

    assert {(edge["source_contract_id"], edge["target_contract_id"]) for edge in graph["edges"]} == {("a", "b")}
    assert audit["changed_contract_ids"] == ["b"]
    assert audit["unaffected_edges_recomputed"] == 0
    assert audit["evaluated_directed_pair_space"] < audit["full_directed_pair_space"]


def test_identical_failed_property_is_not_probed_again():
    from dateassertion.pipeline.feedback_loop import _deduplicate_new, _property_key

    candidate = _prop("candidate")
    selected, rejected = _deduplicate_new(
        [candidate], active=[],
        history={_property_key(candidate): {"terminal": True, "status": "FAILED_CEX", "round": 1}},
    )
    assert selected == []
    assert rejected[0]["reason"] == "IDENTICAL_PRIOR_TERMINAL_OUTCOME"
    assert rejected[0]["prior"]["status"] == "FAILED_CEX"


def test_delta_constraints_are_namespaced_and_not_duplicated():
    from dateassertion.pipeline.feedback_loop import _merge_delta_constraints

    relation = {
        "constraint_id": "c1", "source_contract_id": "a", "source_event_id": "ea",
        "target_contract_id": "b", "target_event_id": "eb", "relation_type": "CAUSALITY",
        "min_delay": 0, "max_delay": 1, "source_predicate": "go", "target_predicate": "done",
        "evidence": {"line_start": 1, "line_end": 1, "quote": "go then done"},
    }
    merged, audit = _merge_delta_constraints({"constraints": [relation], "lifecycle_chains": []}, {"constraints": [relation], "lifecycle_chains": []}, round_index=2)
    assert len(merged["constraints"]) == 1
    assert audit["duplicate_semantic_constraints"] == 1

    changed = {**relation, "target_event_id": "ec", "target_predicate": "ready"}
    merged, audit = _merge_delta_constraints(merged, {"constraints": [changed], "lifecycle_chains": []}, round_index=2)
    assert audit["added_constraints"] == 1
    assert merged["constraints"][-1]["constraint_id"].startswith("feedback_r02_")


def _chain_fixture_contracts() -> list[dict]:
    """A -> B -> C typed-interface chain with one exact shared B event."""

    contracts = [
        _contract("a", outputs=("x",)),
        _contract("b", inputs=("x",), outputs=("y",)),
        _contract("c", inputs=("y",)),
    ]
    for contract, event_id, predicate, signal in (
        (contracts[0], "ea", "go", "x"),
        (contracts[1], "eb", "mid", "y"),
        (contracts[2], "ec", "done", "y"),
    ):
        contract["interface"]["events"] = [{
            "event_id": event_id, "predicate": predicate,
            "semantic_role": "EFFECT", "event_kind": "EFFECT",
            "signals": [signal], "source": "test",
        }]
    return contracts


def _chain_relation(identifier: str, source: str, source_event: str, source_predicate: str,
                    target: str, target_event: str, target_predicate: str) -> dict:
    return {
        "constraint_id": identifier,
        "source_contract_id": source, "source_event_id": source_event,
        "target_contract_id": target, "target_event_id": target_event,
        "relation_type": "CAUSALITY", "min_delay": 0, "max_delay": 2,
        "source_predicate": source_predicate, "target_predicate": target_predicate,
        "evidence": {"line_start": 1, "line_end": 1, "quote": "ordered event chain"},
    }


def test_incremental_chain_keeps_duplicate_old_link_as_minimal_closure():
    """An old A->B link must not make a new A->B->C chain disappear."""

    from dateassertion.pipeline.local_contract_composition import build_contract_graph, generate_composition_candidates
    from dateassertion.pipeline.feedback_loop import (
        _incremental_composition_input,
        _merge_delta_constraints,
        _retain_incremental_composition_candidates,
    )

    old_ab = _chain_relation("ab", "a", "ea", "go", "b", "eb", "mid")
    new_bc = _chain_relation("bc", "b", "eb", "mid", "c", "ec", "done")
    merged, merge_audit = _merge_delta_constraints(
        {"constraints": [old_ab], "lifecycle_chains": []},
        {"constraints": [old_ab, new_bc], "lifecycle_chains": [{
            "chain_id": "abc", "constraint_ids": ["ab", "bc"],
        }]},
        round_index=1,
    )

    new_bc_id = merge_audit["delta_constraint_ids"][0]
    assert merge_audit["duplicate_semantic_constraints"] == 1
    assert merged["lifecycle_chains"][0]["constraint_ids"] == ["ab", new_bc_id]
    assert merge_audit["delta_chain_ids"] == ["feedback_r01_abc"]

    composition_input, incremental_audit = _incremental_composition_input(merged, merge_audit)
    assert [item["constraint_id"] for item in composition_input["constraints"]] == ["ab", new_bc_id]
    assert incremental_audit["closure_only_constraint_ids"] == ["ab"]
    graph = build_contract_graph({"contracts": _chain_fixture_contracts()}, merged)
    candidates = _retain_incremental_composition_candidates(
        generate_composition_candidates(graph, composition_input), incremental_audit,
    )
    assert any(item["constraint_ids"] == ["ab", new_bc_id] for item in candidates["candidates"])
    assert any(item["constraint_ids"] == [new_bc_id] for item in candidates["candidates"])
    assert not any(item["constraint_ids"] == ["ab"] for item in candidates["candidates"])


def test_new_chain_over_retained_edges_generates_chain_but_not_old_adjacents():
    """A newly proposed chain is useful even when both of its edges predate it."""

    from dateassertion.pipeline.local_contract_composition import build_contract_graph, generate_composition_candidates
    from dateassertion.pipeline.feedback_loop import (
        _incremental_composition_input,
        _merge_delta_constraints,
        _retain_incremental_composition_candidates,
    )

    old_ab = _chain_relation("ab", "a", "ea", "go", "b", "eb", "mid")
    old_bc = _chain_relation("bc", "b", "eb", "mid", "c", "ec", "done")
    merged, merge_audit = _merge_delta_constraints(
        {"constraints": [old_ab, old_bc], "lifecycle_chains": []},
        {"constraints": [old_ab, old_bc], "lifecycle_chains": [{
            "chain_id": "abc", "constraint_ids": ["ab", "bc"],
        }]},
        round_index=2,
    )
    assert merge_audit["delta_constraint_ids"] == []
    assert merge_audit["delta_chain_ids"] == ["feedback_r02_abc"]

    composition_input, incremental_audit = _incremental_composition_input(merged, merge_audit)
    graph = build_contract_graph({"contracts": _chain_fixture_contracts()}, merged)
    candidates = _retain_incremental_composition_candidates(
        generate_composition_candidates(graph, composition_input), incremental_audit,
    )
    assert [item["constraint_ids"] for item in candidates["candidates"]] == [["ab", "bc"]]
    assert candidates["summary"]["closure_only_candidates_excluded"] == 2


def test_typed_interface_pair_queue_requires_real_strict_directional_edge():
    from dateassertion.pipeline.feedback_loop import _pair_composition_context, _typed_interface_pair_queue

    source = _contract("source", outputs=("token",), readiness=2)
    target = _contract("target", inputs=("token",), readiness=3)
    unrelated = _contract("unrelated", inputs=("other",), readiness=3)
    for contract, event_id, predicate in (
        (source, "src_effect", "token"), (target, "dst_effect", "done"), (unrelated, "other", "other"),
    ):
        contract["interface"]["events"] = [{
            "event_id": event_id, "predicate": predicate, "semantic_role": "EFFECT",
            "event_kind": "EFFECT", "signals": [predicate], "source": "test",
        }]

    queue = _typed_interface_pair_queue([source, target, unrelated], {"constraints": []}, {})
    assert [(item["source_contract_id"], item["target_contract_id"]) for item in queue] == [("source", "target")]
    context = _pair_composition_context([{"text": "completion follows request"}], queue[0])
    assert context["allowed_contract_ids"] == ["source", "target"]
    assert context["incremental_scope"]["shared_interface_signals"] == ["token"]
    assert _typed_interface_pair_queue(
        [source, target], {"constraints": []}, {queue[0]["context_key"]: {"status": "VALIDATED_EMPTY"}},
    ) == []


def test_region_worklist_keeps_deferred_motif_for_later_round():
    from dateassertion.pipeline.feedback_loop import _region_key, _region_worklist

    motifs = [
        {"region_id": "later", "module": "dut", "core_node_ids": ["n2"], "assignment_node_ids": ["a2"], "selection_score": 1},
        {"region_id": "first", "module": "dut", "core_node_ids": ["n1"], "assignment_node_ids": ["a1"], "selection_score": 2},
    ]
    state = {"region_history": {}, "pending_region_motifs": []}
    selected, deferred, _ = _region_worklist(state, motifs, budget=1)
    assert [item["region_id"] for item in selected] == ["first"]
    state["region_history"][_region_key(selected[0])] = {"round": 1, "status": "VALIDATED"}
    state["pending_region_motifs"] = deferred
    selected, deferred, _ = _region_worklist(state, motifs, budget=1)
    assert [item["region_id"] for item in selected] == ["later"]
    assert deferred == []


def test_adaptive_context_budget_is_resource_cap_not_sva_quota():
    from dateassertion.pipeline.feedback_loop import _composition_context_budget

    state = {"generation_history": {
        f"local_{index}": {"kind": "LOCAL", "round_compiled": 0} for index in range(1935)
    }}
    budget = _composition_context_budget(state, {
        "desired_composition_fraction": 0.20, "composition_contexts_per_round": 64,
        "composition_min_contexts_per_round": 4, "composition_size_adaptive_budget": True,
    }, 10)
    assert budget["adaptive_contexts_per_round"] == 49
    assert budget["effective_contexts_per_round"] == 49
    assert "not a target number" in budget["policy"]


def test_initial_compact_context_audit_seeds_no_retry_history(tmp_path):
    from dateassertion.pipeline.feedback_loop import _seed_initial_composition_context_history

    dump_json(tmp_path / "composition_expansion" / "composition_context_audit.json", {
        "calls": [
            {"context_key": "exact-event-context", "status": "REJECTED"},
            {"context_key": "exact-empty-context", "status": "VALIDATED_EMPTY"},
        ],
    })
    history = _seed_initial_composition_context_history(tmp_path, {"constraints": [{
        "source_contract_id": "a", "target_contract_id": "b",
    }]})
    assert history["exact-event-context"]["status"] == "REJECTED"
    assert history["exact-empty-context"]["kind"] == "EXACT_EVENT_CONTEXT"
    assert any(item["kind"] == "LEGACY_CONTRACT_PAIR" for item in history.values())


@pytest.mark.parametrize(
    ("probe_result", "probe_vacuity", "expected_reason"),
    [
        ("TIMEOUT_ACCEPTED", "NON_VACUOUS", "NO_TOOL_PASS_CANDIDATES"),
        ("PASS", "VACUOUS", "ALL_TOOL_PASS_CANDIDATES_VACUOUS"),
    ],
)
def test_strict_probe_skips_empty_strict_portfolio_without_faking_pass(
    tmp_path, monkeypatch, probe_result, probe_vacuity, expected_reason,
):
    """Policy timeouts/vacuity must not launch an empty strict Jasper run."""

    import dateassertion.pipeline.feedback_loop as feedback

    prop = _prop("candidate")
    probe = FormalRunResult(
        status="PASS", tool="fake", runtime_seconds=0.0, log_path="",
        results=[FormalPropertyResult(prop.property_id, probe_result, vacuity=probe_vacuity)],
        summary={}, coverage={}, notes=[],
    )
    formal_roots: list[Path] = []

    def fake_formal(_design, _props, _top, root, _config, **_kwargs):
        formal_roots.append(Path(root))
        return probe

    monkeypatch.setattr(feedback, "_formal", fake_formal)
    monkeypatch.setattr(
        feedback, "_stable_formal",
        lambda *_args, **_kwargs: pytest.fail("empty strict portfolio must not invoke _stable_formal"),
    )

    strict, returned_probe, audit, exact = feedback._strict_probe(
        None, [prop], "dut", tmp_path / "composition", {}, {},
    )
    assert strict == []
    assert returned_probe is probe
    assert exact is None
    assert formal_roots == [tmp_path / "composition" / "probe"]
    assert audit[0]["status"] == "SKIPPED_NO_STRICT_PORTFOLIO"
    assert audit[0]["reason"] == expected_reason
    assert audit[0]["tool_pass_candidates"] == (1 if probe_result == "PASS" else 0)
    assert (tmp_path / "composition" / "strict" / "skipped_no_strict_portfolio.json").is_file()


@pytest.mark.parametrize(
    ("probe_status", "result_rows"),
    [
        ("ERROR", [("candidate", "ERROR")]),
        ("PASS", []),
    ],
)
def test_strict_probe_does_not_mask_failed_or_incomplete_probe_as_empty_portfolio(
    tmp_path, monkeypatch, probe_status, result_rows,
):
    """Only a complete candidate probe may legitimately have zero survivors."""

    import dateassertion.pipeline.feedback_loop as feedback

    prop = _prop("candidate")
    probe = FormalRunResult(
        status=probe_status, tool="fake", runtime_seconds=0.0, log_path="",
        results=[FormalPropertyResult(identifier, result, vacuity="NOT_EVALUATED")
                 for identifier, result in result_rows],
        summary={}, coverage={}, notes=[],
    )
    monkeypatch.setattr(feedback, "_formal", lambda *_args, **_kwargs: probe)
    monkeypatch.setattr(
        feedback, "_stable_formal",
        lambda *_args, **_kwargs: pytest.fail("failed/incomplete probe must fail before stable Formal"),
    )

    with pytest.raises(RuntimeError, match="candidate probe did not complete"):
        feedback._strict_probe(None, [prop], "dut", tmp_path / "composition", {}, {})
    assert not (tmp_path / "composition" / "strict" / "skipped_no_strict_portfolio.json").exists()


def test_run_feedback_persists_zero_gain_rounds_and_resumes(tmp_path, monkeypatch):
    """A no-actionable-gap run still executes and saves each full remeasurement."""

    import dateassertion.pipeline.feedback_loop as feedback

    rtl = tmp_path / "dut.sv"
    rtl.write_text("module dut(input clk, input rst_n, input a, output q); assign q = a; endmodule\n")
    initial = tmp_path / "initial"
    from dateassertion.rtl_frontend.parser import parse_rtl
    design = parse_rtl([str(rtl)])
    prop = _prop()
    dump_json(initial / "final" / "trusted_properties.json", [prop])
    dump_json(initial / "regions.json", {"regions": [{
        "region_id": "region_a", "module": "dut", "kind": "DATAPATH",
        "core_node_ids": [], "signals": ["a", "q"], "coi": {"node_ids": []},
    }]})
    dump_json(initial / "local_contracts.json", {"contracts": [_contract("a", outputs=("q",))]})
    dump_json(initial / "partial_order_constraints.json", {"constraints": [], "lifecycle_chains": []})
    dump_json(initial / "local_candidates.json", [prop])
    dump_json(initial / "composition_properties.json", [])
    dump_json(initial / "design_flow_design_summary.json", {"design_id": "fixture", "source_digest": design.source_digest})
    dump_json(initial / "design_map.json", {"instances": []})
    dump_json(initial / "spec" / "selected_evidence.json", [])
    dump_json(initial / "feedback_initial_manifest.json", {"fixture": True})
    design.save(initial / "rtl_structure.json")
    baseline_result = FormalRunResult(
        status="PASS", tool="fake", runtime_seconds=0.0, log_path="",
        results=[FormalPropertyResult("initial", "PASS", vacuity="NON_VACUOUS")], summary={}, coverage={}, notes=[],
    )
    dump_json(initial / "formal" / "without_feedback" / "formal" / "formal_results.json", baseline_result)
    (initial / "formal" / "without_feedback" / "formal" / "coverage_items.tsv").parent.mkdir(parents=True, exist_ok=True)
    (initial / "formal" / "without_feedback" / "formal" / "coverage_items.tsv").write_text("fixture\n")
    dump_json(initial / "formal" / "without_feedback" / "formal" / "input_identity.json", {"fixture": True})
    (initial / "formal" / "without_feedback" / "assertions.sv").write_text("// fixture assertion\n")

    # The test focuses on resumability and round accounting; it deliberately
    # supplies no Region motif, therefore no LLM or JasperGold invocation.
    monkeypatch.setattr(feedback, "parse_coverage_items", lambda _path: [_coverage_item()])
    monkeypatch.setattr(feedback, "discover_refinement_candidates", lambda *_args, **_kwargs: [])
    monkeypatch.setattr(feedback, "build_property_candidate_pool", lambda *_args, **_kwargs: ([], [], {"pool": 0}))
    formal_calls: list[Path] = []

    def fake_formal(design, properties, top, root, config, **_kwargs):
        root = Path(root)
        formal_calls.append(root)
        result = FormalRunResult(
            status="PASS", tool="fake", runtime_seconds=0.0, log_path="",
            results=[FormalPropertyResult(item.property_id, "PASS", vacuity="NON_VACUOUS") for item in properties],
            summary={}, coverage={}, notes=[],
        )
        dump_json(root / "formal" / "formal_results.json", result)
        (root / "formal" / "coverage_items.tsv").parent.mkdir(parents=True, exist_ok=True)
        (root / "formal" / "coverage_items.tsv").write_text("fixture\n")
        return result

    monkeypatch.setattr(feedback, "_formal", fake_formal)

    def fake_stable(design, fixed, candidates, top, root, config, **_kwargs):
        # Req12 must run the strict full portfolio path even for a zero-gain
        # round.  Return only candidate survivors, matching _stable_formal's
        # real API (fixed properties are not returned as survivors).
        return list(candidates), fake_formal(design, [*fixed, *candidates], top, root, config), [{"fake": True}]

    monkeypatch.setattr(feedback, "_stable_formal", fake_stable)
    compact_calls: list[Path] = []

    def fake_compact(_client, _prompt, _spec, _contracts, _design, output, _config):
        compact_calls.append(Path(output))
        return {"constraints": [], "lifecycle_chains": []}, {"calls": [], "contexts_selected": 0}

    monkeypatch.setattr(feedback, "expand_initial_composition", fake_compact)
    cfg = {
        "llm": {"provider": "deepseek", "model": "deepseek-v4-pro"},
        "formal": {}, "design_flow": {"refinement_region_limit": 2, "refinement_max_assignments": 2, "refinement_graph_depth": 1},
        "feedback": {"desired_composition_fraction": 0.20, "composition_event_context_enabled": True},
    }
    target = {
        "design_id": "fixture", "top": "dut", "rtl_files": [str(rtl)], "include_dirs": [],
        "clock": "clk", "reset": "rst_n", "reset_active_low": True, "validation_scope": "module",
    }
    output = tmp_path / "feedback"
    first = feedback.run_feedback(target, cfg, initial, output, rounds=2)
    assert len(formal_calls) == 2
    assert len(compact_calls) == 2
    assert [row["zero_gain_round"] for row in first["trend"]] == [True, True]
    assert (output / "rounds" / "round_01" / "state.json").is_file()
    assert (output / "rounds" / "round_02" / "round_summary.json").is_file()
    assert len(__import__("json").loads((output / "rounds" / "round_02" / "active_properties.json").read_text())) == 1

    resumed = feedback.run_feedback(target, cfg, initial, output, rounds=2)
    assert len(formal_calls) == 2
    assert resumed["rounds_completed"] == 2
    assert resumed["final_portfolio"]["composition_sva"] == 0

    # A revised suffix has a new identity; inherited rounds are not rerun or
    # copied as if they had used the revised algorithm.
    fork = tmp_path / "fork"
    revised = feedback.run_feedback(target, cfg, initial, fork, rounds=2,
                                    checkpoint_root=output, checkpoint_round=1)
    assert len(formal_calls) == 3
    assert revised["rounds_completed"] == 2
    assert revised["inherited_checkpoint"]["round"] == 1
    assert not (fork / "rounds" / "round_01").exists()
    assert (fork / "rounds" / "round_02" / "state.json").exists()
    feedback.run_feedback(target, cfg, initial, fork, rounds=2,
                          checkpoint_root=output, checkpoint_round=1)
    assert len(formal_calls) == 3
    state_path = output / "rounds" / "round_01" / "state.json"
    state_path.write_text(state_path.read_text() + "\n")
    with pytest.raises(RuntimeError, match="checkpoint"):
        feedback.run_feedback(target, cfg, initial, fork, rounds=2,
                              checkpoint_root=output, checkpoint_round=1)


def test_feedback_provider_outage_is_an_interruption_not_a_rejected_region(tmp_path, monkeypatch):
    """A 402 during Region interpretation must stop before semantic history mutates."""

    import dateassertion.pipeline.feedback_loop as feedback
    from dateassertion.llm.client import LLMUnavailableError
    from dateassertion.rtl_frontend.parser import parse_rtl

    rtl = tmp_path / "dut.sv"
    rtl.write_text("module dut(input clk, input rst_n, input a, output q); assign q = a; endmodule\n")
    design = parse_rtl([str(rtl)])
    initial = tmp_path / "initial"
    prop = _prop()
    dump_json(initial / "final" / "trusted_properties.json", [prop])
    dump_json(initial / "regions.json", {"regions": [{
        "region_id": "region_a", "module": "dut", "kind": "DATAPATH",
        "core_node_ids": [], "signals": ["a", "q"], "coi": {"node_ids": []},
    }]})
    dump_json(initial / "local_contracts.json", {"contracts": [_contract("a", outputs=("q",))]})
    dump_json(initial / "partial_order_constraints.json", {"constraints": [], "lifecycle_chains": []})
    dump_json(initial / "local_candidates.json", [prop])
    dump_json(initial / "composition_properties.json", [])
    dump_json(initial / "design_flow_design_summary.json", {"design_id": "fixture", "source_digest": design.source_digest})
    dump_json(initial / "design_map.json", {"instances": []})
    dump_json(initial / "spec" / "selected_evidence.json", [])
    dump_json(initial / "feedback_initial_manifest.json", {"fixture": True})
    design.save(initial / "rtl_structure.json")
    result = FormalRunResult(
        status="PASS", tool="fake", runtime_seconds=0.0, log_path="",
        results=[FormalPropertyResult("initial", "PASS", vacuity="NON_VACUOUS")], summary={}, coverage={}, notes=[],
    )
    dump_json(initial / "formal" / "without_feedback" / "formal" / "formal_results.json", result)
    formal_dir = initial / "formal" / "without_feedback" / "formal"
    formal_dir.mkdir(parents=True, exist_ok=True)
    (formal_dir / "coverage_items.tsv").write_text("fixture\n")
    dump_json(formal_dir / "input_identity.json", {"fixture": True})
    (initial / "formal" / "without_feedback" / "assertions.sv").write_text("// fixture\n")

    monkeypatch.setattr(feedback, "parse_coverage_items", lambda _path: [_coverage_item()])
    monkeypatch.setattr(feedback, "discover_refinement_candidates", lambda *_args, **_kwargs: [{
        "region_id": "unavailable_region", "module": "dut", "core_node_ids": ["assignment:new"],
        "assignment_node_ids": ["assignment:new"], "selection_score": 1,
    }])

    def unavailable(*_args, **_kwargs):
        raise LLMUnavailableError("DeepSeek HTTP 402: Insufficient Balance", status_code=402)

    monkeypatch.setattr(feedback, "interpret_refinements", unavailable)
    target = {
        "design_id": "fixture", "top": "dut", "rtl_files": [str(rtl)], "include_dirs": [],
        "clock": "clk", "reset": "rst_n", "reset_active_low": True, "validation_scope": "module",
    }
    cfg = {
        "llm": {"provider": "deepseek", "model": "deepseek-v4-pro"}, "formal": {},
        "design_flow": {"refinement_region_limit": 1}, "feedback": {},
    }
    output = tmp_path / "feedback"
    with pytest.raises(RuntimeError, match="LLM_UNAVAILABLE_EXTERNAL_SERVICE"):
        feedback.run_feedback(target, cfg, initial, output, rounds=1)
    interruption = __import__("json").loads(
        (output / "rounds" / "round_01" / "external_service_failure.json").read_text()
    )
    failure = __import__("json").loads(
        (output / "rounds" / "round_01" / "round_failure.json").read_text()
    )
    region_audit = __import__("json").loads(
        (output / "rounds" / "round_01" / "llm_region_interpretation.json").read_text()
    )
    assert interruption["status"] == "INTERRUPTED_EXTERNAL_SERVICE"
    assert failure["reason"] == "LLM_UNAVAILABLE_EXTERNAL_SERVICE"
    assert region_audit == [{
        "region_id": "unavailable_region", "status": "INTERRUPTED_EXTERNAL_SERVICE",
        "error": "LLMUnavailableError: DeepSeek HTTP 402: Insufficient Balance",
    }]
    assert not (output / "rounds" / "round_01" / "state.json").exists()
