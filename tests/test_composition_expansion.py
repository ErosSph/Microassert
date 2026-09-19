from __future__ import annotations

import json
import pytest


class _Signal:
    def __init__(self, width: int = 1):
        self.width = width


class _Design:
    def __init__(self):
        self.module_signals = {
            "dut": {name: _Signal(width) for name, width in {
                "x": 1, "y": 1, "wide": "[31:0]", "unknown": "[WIDTH-1:0]", "a_done": 1, "mid": 1, "c_done": 1,
            }.items()},
            "other": {"x": _Signal(1)},
        }


def _event(identifier: str, predicate: str, signals: list[str], kind: str) -> dict:
    return {
        "event_id": identifier, "predicate": predicate, "signals": signals,
        "event_kind": kind, "semantic_role": kind, "source": {"origin": "test", "event": identifier},
    }


def _contract(identifier: str, *, module="dut", inputs=(), outputs=(), events=()) -> dict:
    return {
        "contract_id": identifier, "region_id": f"region_{identifier}", "module": module,
        "region_kind": "REGISTER_UPDATE", "readiness_level": 2,
        "interface": {"inputs": list(inputs), "outputs": list(outputs), "state": [], "events": list(events)},
        "trusted_local_obligations": [f"local_{identifier}"],
    }


def _three_stage_contracts() -> dict:
    return {"contracts": [
        _contract("a", outputs=("x",), events=[_event("a_effect", "a_done", ["x", "a_done"], "EFFECT")]),
        # The original event ID ``mid`` is intentionally used as the target
        # witness for A->B and source witness for B->C.
        _contract("b", inputs=("x",), outputs=("y",), events=[_event("mid", "mid", ["x", "y", "mid"], "STATE")]),
        _contract("c", inputs=("y",), events=[_event("c_trigger", "c_done", ["y", "c_done"], "TRIGGER")]),
        _contract("cross", module="other", inputs=("x",), events=[_event("cross_trigger", "x", ["x"], "TRIGGER")]),
    ]}


def test_typed_queue_excludes_cross_module_and_bare_multibit_boolean():
    from dateassertion.pipeline.composition_expansion import _bare_boolean_rejection_reason, typed_event_pair_queue

    contracts = _three_stage_contracts()
    contracts["contracts"].append(_contract(
        "wide_source", outputs=("wide",), events=[_event("wide_effect", "wide", ["wide"], "EFFECT")],
    ))
    contracts["contracts"].append(_contract(
        "wide_target", inputs=("wide",), events=[_event("wide_trigger", "wide", ["wide"], "TRIGGER")],
    ))
    queue, rejected = typed_event_pair_queue(contracts, _Design(), event_limit=3)

    pairs = {(item["source"]["contract_id"], item["target"]["contract_id"]) for item in queue}
    assert ("a", "b") in pairs and ("b", "c") in pairs
    assert all("cross" not in pair for pair in pairs)
    assert ("wide_source", "wide_target") not in pairs
    assert any(row["reason"] == "NO_SIGNAL_ANCHORED_EVENT_PAIR" for row in rejected)
    wide_contract = _contract("width", outputs=("wide",))
    assert _bare_boolean_rejection_reason(_event("bare", "wide", ["wide"], "EFFECT"), wide_contract, _Design()) == "BARE_MULTIBIT_BOOLEAN_PREDICATE"
    assert _bare_boolean_rejection_reason(_event("not", "!wide", ["wide"], "EFFECT"), wide_contract, _Design()) is None
    assert _bare_boolean_rejection_reason(_event("equal", "wide == 0", ["wide"], "EFFECT"), wide_contract, _Design()) is None
    unknown_contract = _contract("unknown", outputs=("unknown",))
    assert _bare_boolean_rejection_reason(_event("unknown", "unknown", ["unknown"], "EFFECT"), unknown_contract, _Design()) == "BARE_UNKNOWN_WIDTH_BOOLEAN_PREDICATE"


def test_continuous_chain_uses_same_original_intermediate_event_id():
    from dateassertion.pipeline.composition_expansion import _chain_candidates, typed_event_pair_queue

    queue, _ = typed_event_pair_queue(_three_stage_contracts(), _Design(), event_limit=3)
    chains = _chain_candidates(queue)
    abc = next(item for item in chains if item["contract_ids"] == ["a", "b", "c"])
    assert abc["atoms"][0]["target_event_id"] == "mid"
    assert abc["atoms"][1]["source_event_id"] == "mid"
    assert len(abc["contract_ids"]) == len(set(abc["contract_ids"]))


def test_chain_search_is_explicitly_bounded_and_not_claimed_exhaustive():
    from dateassertion.pipeline.composition_expansion import _chain_candidates, typed_event_pair_queue

    queue, _ = typed_event_pair_queue(_three_stage_contracts(), _Design(), event_limit=3, max_pair_evaluations=1)
    assert len(queue) <= 1
    _, pair_rejections = typed_event_pair_queue(_three_stage_contracts(), _Design(), event_limit=3, max_pair_evaluations=1)
    assert any(row["reason"] == "TYPED_INTERFACE_PAIR_EVALUATION_BUDGET_EXHAUSTED" for row in pair_rejections)

    full_queue, _ = typed_event_pair_queue(_three_stage_contracts(), _Design(), event_limit=3)
    audit = {}
    _chain_candidates(full_queue, max_expansions=0, max_candidates=1, audit=audit)
    assert audit["chain_expansions"] == 0
    assert "not exhaustive" in audit["enumeration"]
    assert audit["truncated"]

    discovered_audit = {}
    discovered = _chain_candidates(full_queue, max_expansions=1, max_candidates=8, audit=discovered_audit)
    assert any(item["contract_ids"] == ["a", "b", "c"] for item in discovered)
    # Existing queued work is drained after the enqueue budget is exhausted;
    # this is what preserves a chain discovered at the boundary.
    assert discovered_audit["chain_expansions"] == 1


def test_prior_adjacent_event_does_not_remove_new_continuous_chain(tmp_path, monkeypatch):
    import dateassertion.pipeline.composition_expansion as compact

    seen = []

    def fake_validator(_client, _prompt, context, _path, **_kwargs):
        seen.append(context)
        return {"constraints": [], "lifecycle_chains": []}, {"api_calls_this_run": 0, "real_response_artifacts": 0, "response_models": []}

    monkeypatch.setattr(compact, "_validated_llm_constraints", fake_validator)
    contracts = _three_stage_contracts()
    config = {"feedback": {
        "initial_generated_local_sva": 16, "desired_composition_fraction": .2,
        "initial_composition_context_budget": 4, "initial_composition_min_contexts": 4,
        # Existing A:a_effect -> B:mid must not erase A->B->C.
        "runtime_excluded_event_pairs": [["a", "a_effect", "b", "mid"]],
    }}
    _, audit = compact.expand_initial_composition(
        object(), "bind", [{"line": 1, "text": "request then completion"}],
        contracts, _Design(), tmp_path, config,
    )
    assert audit["excluded_prior_event_pairs"] == 1
    assert any(
        context["context_kind"] == "CONTINUOUS_TYPED_EVENT_CHAIN"
        and ["a", "b", "c"] == context["allowed_contract_ids"]
        for context in seen
    )


def test_expand_initial_composition_bounded_contexts_preserves_ids_and_failures(tmp_path, monkeypatch):
    import dateassertion.pipeline.composition_expansion as compact

    contracts = _three_stage_contracts()
    requested = []

    def fake_validator(_client, _prompt, context, _path, *, attempts, maximum_delay):
        requested.append(context)
        pair = context["allowed_event_pairs"][0]
        if len(requested) == 2:
            raise RuntimeError("simulated retained transport failure")
        return ({
            "constraints": [{
                "constraint_id": "r", "source_contract_id": pair["source_contract_id"],
                "source_event_id": pair["source_event_id"], "target_contract_id": pair["target_contract_id"],
                "target_event_id": pair["target_event_id"], "relation_type": "CAUSALITY",
                "min_delay": 0, "max_delay": 2,
                "source_predicate": next(event["predicate"] for contract in context["contracts"]
                                         if contract["contract_id"] == pair["source_contract_id"]
                                         for event in contract["events"] if event["event_id"] == pair["source_event_id"]),
                "target_predicate": next(event["predicate"] for contract in context["contracts"]
                                         if contract["contract_id"] == pair["target_contract_id"]
                                         for event in contract["events"] if event["event_id"] == pair["target_event_id"]),
                "evidence": {"line_start": 7, "line_end": 7, "quote": "completion follows the request"},
            }], "lifecycle_chains": [],
        }, {"fake_validator": True, "attempts": attempts, "maximum_delay": maximum_delay})

    monkeypatch.setattr(compact, "_validated_llm_constraints", fake_validator)
    config = {
        "design_flow": {"llm_validation_attempts": 1, "maximum_composition_delay": 8},
        "feedback": {
            "desired_composition_fraction": 0.2, "composition_min_contexts_per_round": 1,
            "composition_contexts_per_round": 4, "compact_composition_context_chars": 2000,
            "compact_events_per_role": 2, "initial_generated_local_sva": 16,
        },
    }
    merged, audit = compact.expand_initial_composition(
        object(), "bind only", [{"line": 7, "text": "completion follows the request"}],
        contracts, _Design(), tmp_path, config,
    )

    assert audit["contexts_selected"] <= 4
    assert audit["call_statuses"]["REJECTED"] == 1  # failure is retained in audit, not discarded silently
    assert merged["constraints"]
    assert all(item["constraint_id"].startswith("feedback_initial_c") for item in merged["constraints"])
    assert all(item["supporting_spec_evidence"][0]["quote"] == "completion follows the request" for item in merged["constraints"])
    for context in requested:
        assert len(json.dumps(context, ensure_ascii=False, separators=(",", ":"))) <= 2000
        assert all("a_done" in event["predicate"] or "mid" in event["predicate"] or "c_done" in event["predicate"]
                   for contract in context["contracts"] for event in contract["events"])
        assert all("assert property" not in event["predicate"] for contract in context["contracts"] for event in contract["events"])


def test_provider_outage_writes_compact_audit_and_aborts_instead_of_rejecting(tmp_path, monkeypatch):
    import dateassertion.pipeline.composition_expansion as compact
    from dateassertion.llm.client import LLMUnavailableError

    def unavailable(*_args, **_kwargs):
        raise LLMUnavailableError("DeepSeek HTTP 402: Insufficient Balance", status_code=402)

    monkeypatch.setattr(compact, "_validated_llm_constraints", unavailable)
    config = {"feedback": {
        "initial_generated_local_sva": 4, "desired_composition_fraction": .2,
        "initial_composition_context_budget": 1, "initial_composition_min_contexts": 1,
    }}
    with pytest.raises(LLMUnavailableError):
        compact.expand_initial_composition(
            object(), "bind", [{"line": 1, "text": "completion follows request"}],
            _three_stage_contracts(), _Design(), tmp_path, config,
        )
    audit = json.loads((tmp_path / "composition_context_audit.json").read_text())
    failure = json.loads((tmp_path / "external_service_failure.json").read_text())
    assert audit["status"] == "INTERRUPTED_EXTERNAL_SERVICE"
    assert audit["calls"][0]["status"] == "INTERRUPTED_EXTERNAL_SERVICE"
    assert failure["status"] == "INTERRUPTED_EXTERNAL_SERVICE"
