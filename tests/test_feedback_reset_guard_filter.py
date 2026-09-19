from dateassertion.ir.schema import ObjectType, PropertyIR
from dateassertion.pipeline.feedback_work_selection import select_current_gap_work


def _entry(property_id: str, body: str, disable_iff: str = "!rst_n"):
    prop = PropertyIR(
        property_id=property_id, region_id="region", object_type=ObjectType.EXTENSION,
        family="PRIMITIVE", template="CAUSALITY", bindings={}, signals=["rst_n", "q"],
        source="test", llm_confidence=1.0, body=body, disable_iff=disable_iff,
        target_module="dut",
    )
    return {"property": prop, "metadata": {"assignment_id": f"assignment:{property_id}"}}


def _gap(property_id: str):
    return {
        "cid": property_id, "rtl_item_id": property_id,
        "official_status": "uncovered_or_unchecked", "gap_type": "B_CONTRACT_GAP",
        "graph_node_ids": [f"assignment:{property_id}"],
    }


def test_exact_reset_antecedent_is_deferred_with_auditable_reason():
    blocked = _entry("blocked", "(rst_n == 1'b0) |-> q")
    allowed = _entry("allowed", "(req & rst_n) |-> q")

    selected, deferred, audit = select_current_gap_work(
        [blocked, allowed], [_gap("blocked"), _gap("allowed")], budget=2,
    )

    assert [item["property"].property_id for item in selected] == ["allowed"]
    assert [item["property"].property_id for item in deferred] == ["blocked"]
    assert audit["eligible_candidate_records"] == 1
    assert audit["excluded_reset_guard_contradictions"] == [{
        "property_id": "blocked",
        "reason": "DISABLE_IFF_AND_ANTECEDENT_ASSERT_SAME_RESET_VALUE",
        "disposition": "DEFERRED_PENDING_EXPORT",
        "reset_signal": "rst_n",
        "reset_value": 0,
        "disable_relation": "ZERO",
        "antecedent_relation": "ZERO",
        "disable_iff": "!rst_n",
        "antecedent": "rst_n == 1'b0",
        "entry_index": 0,
    }]


def test_active_high_reset_and_literal_order_are_handled_without_name_heuristics():
    blocked = _entry("blocked", "(1'b1 == reset) |=> q", disable_iff="reset")

    selected, deferred, audit = select_current_gap_work(
        [blocked], [_gap("blocked")], budget=1,
    )

    assert selected == []
    assert deferred == [blocked]
    assert audit["excluded_reset_guard_contradictions"][0]["reset_signal"] == "reset"
    assert audit["excluded_reset_guard_contradictions"][0]["reset_value"] == "NONZERO"
    assert audit["excluded_reset_guard_contradictions"][0]["disable_relation"] == "TRUTHY"
    assert audit["excluded_reset_guard_contradictions"][0]["antecedent_relation"] == "ONE"


def test_unknown_width_truthiness_only_implies_truthiness_or_is_exactly_equal():
    one_implies_truthy = _entry("one_implies_truthy", "(bus == 1'b1) |-> q", disable_iff="bus")
    truthy_not_one = _entry("truthy_not_one", "bus |-> q", disable_iff="bus == 1'b1")
    bitwise_not = _entry("bitwise_not", "(~bus) |-> q", disable_iff="~bus")

    selected, deferred, audit = select_current_gap_work(
        [one_implies_truthy, truthy_not_one, bitwise_not],
        [_gap("one_implies_truthy"), _gap("truthy_not_one"), _gap("bitwise_not")],
        budget=3,
    )

    assert [item["property"].property_id for item in selected] == [
        "truthy_not_one", "bitwise_not",
    ]
    assert [item["property"].property_id for item in deferred] == ["one_implies_truthy"]
    excluded = audit["excluded_reset_guard_contradictions"]
    assert len(excluded) == 1
    assert excluded[0]["property_id"] == "one_implies_truthy"
    assert excluded[0]["disable_relation"] == "TRUTHY"
    assert excluded[0]["antecedent_relation"] == "ONE"


def test_compound_or_different_reset_expression_is_not_guessed_or_excluded():
    compound = _entry("compound", "(rst_n == 1'b0 && req) |-> q")
    different = _entry("different", "(rst_n == 1'b1) |-> q")

    selected, deferred, audit = select_current_gap_work(
        [compound, different], [_gap("compound"), _gap("different")], budget=2,
    )

    assert [item["property"].property_id for item in selected] == ["compound", "different"]
    assert deferred == []
    assert audit["excluded_reset_guard_contradictions"] == []
