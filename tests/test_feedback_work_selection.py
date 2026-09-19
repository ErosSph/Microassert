from dateassertion.pipeline.feedback_work_selection import select_current_gap_work
from test_feedback_loop import _prop


def entry(pid, anchor):
    return {"property": _prop(pid), "metadata": {"assignment_id": anchor}}


def gap(cid, anchor, **changes):
    return {"cid": cid, "rtl_item_id": str(cid), "official_status": "uncovered_or_unchecked",
            "gap_type": "B_CONTRACT_GAP", "graph_node_ids": [anchor], **changes}


def test_current_gaps_replace_stale_fifo_without_body_dedup():
    entries = [entry("old", "assignment:0"), entry("new", "assignment:1"), entry("dup", "assignment:1")]
    selected, deferred, audit = select_current_gap_work(entries, [gap(1, "assignment:1")], 1)
    assert [e["property"].property_id for e in selected] == ["new"]
    assert [e["property"].property_id for e in deferred] == ["old", "dup"]
    assert audit["fifo_mapped_unchecked_union"] == 0
    assert audit["selected_mapped_unchecked_union"] == 1
    assert audit["predicted_formal_gain"] is None


def test_marginal_union_not_double_counted_and_checked_or_unmapped_ignored():
    entries = [entry("a", "assignment:1"), entry("b", "assignment:1"), entry("c", "assignment:2")]
    rows = [gap(1, "assignment:1"), gap(2, "assignment:2"),
            gap(3, "assignment:1", official_status="covered_and_checked"),
            gap(4, "assignment:1", gap_type="D_NON_ACTIONABLE")]
    selected, deferred, audit = select_current_gap_work(entries, rows, 2)
    assert [e["property"].property_id for e in selected] == ["a", "c"]
    assert len(deferred) == 1 and audit["selected_mapped_unchecked_union"] == 2


def test_no_gap_keeps_fifo_and_zero_budget_preserves_every_record():
    entries = [entry("a", "assignment:1"), entry("b", "assignment:1")]
    assert select_current_gap_work(entries, [], 1)[0] == entries[:1]
    selected, deferred, _ = select_current_gap_work(entries, [], 0)
    assert not selected and deferred == entries
