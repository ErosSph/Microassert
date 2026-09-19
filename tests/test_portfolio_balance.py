"""Tests for the isolated Req12 balanced Local-binding selector."""

from __future__ import annotations

from types import SimpleNamespace

from dateassertion.pipeline.local_region_assertions import LocalCandidateBinding
from dateassertion.pipeline.portfolio_balance import select_balanced_local_bindings


def _binding(
    identifier: str, *, module: str = "dut", kind: str = "DATAPATH", obligation: str = "REGISTER_UPDATE",
    region: str = "region_a", compatible: tuple[str, ...] = ("region_a",),
    scope: tuple[str, ...] = ("assignment:1",), boundary: bool = False, static_score: float = 0.0,
) -> LocalCandidateBinding:
    candidate = SimpleNamespace(
        candidate_id=identifier, module=module, region_kind=kind, obligation=obligation,
        primitive="UPDATE", region_id=region, structural_scope=list(scope),
        # Deliberately present but forbidden to the new selector.
        static_coverage_score=static_score, proofability_score=0.01, vacuity_risk=0.99,
    )
    evidence = {}
    for serial, region_id in enumerate(compatible, 1):
        evidence[region_id] = {
            "binding_level": "TYPED_BOUNDARY" if boundary and serial == 1 else "TYPED_COI_PATH",
            "binding_rank": 3 if region_id == region else 1,
            "path_edge_count": serial,
            "typed_edges": [{"source": f"assignment:{serial}", "target": f"signal:{module}.q"}],
        }
    return LocalCandidateBinding(candidate=candidate, compatible_region_ids=list(compatible), binding_evidence_by_region=evidence)


def test_small_pool_selects_all_and_preserves_one_to_many_binding_metadata():
    first = _binding("small_b", region="region_b", compatible=("region_a", "region_b"), boundary=True)
    second = _binding("small_a", module="other", kind="CONTROL_FSM", obligation="RESET", region="region_c")
    selected, audit = select_balanced_local_bindings([first, second], budget=128, fraction=0.5, minimum=20)

    assert {item.candidate.candidate_id for item in selected} == {"small_a", "small_b"}
    assert audit["target_selected"] == 2
    record = next(item for item in audit["records"] if item["candidate_id"] == "small_b")
    assert record["compatible_region_ids"] == ["region_a", "region_b"]
    assert record["primary_region_id"] == "region_b"  # declared region is compatible; no arbitrary reassignment
    assert record["typed_boundary_regions"] == ["region_a"]
    assert all(item.selection_score is None for item in selected)
    assert all(item["generated_sva"] is False for item in audit["records"])


def test_big_pool_is_budgeted_deterministically_by_structural_diversity_not_old_scores():
    bindings = [
        _binding("z_old_high_score", module="m9", kind="DATAPATH", obligation="UPDATE", static_score=9999.0),
        _binding("a_m0", module="m0", kind="COUNTER", obligation="COUNT", scope=("assignment:10",)),
        _binding("a_m1", module="m1", kind="CONTROL_FSM", obligation="RESET", scope=("assignment:11",)),
        _binding("a_m2", module="m2", kind="ALU", obligation="DATAFLOW", scope=("assignment:12",)),
        _binding("a_m3", module="m3", kind="REGISTER_FILE", obligation="HOLD", scope=("assignment:13",)),
        _binding("a_m4", module="m4", kind="LSU", obligation="PERSIST", scope=("assignment:14",)),
        _binding("later_same", module="m4", kind="LSU", obligation="PERSIST", scope=("assignment:15",)),
    ]
    selected, audit = select_balanced_local_bindings(bindings, budget=4, fraction=0.5, minimum=2)

    # ceil(7*.5)=4 and cap=4.  The first four structurally diverse modules
    # win; the high historical score in m9 has no influence.
    assert audit["target_selected"] == 4
    assert len(selected) == 4
    assert len({item.candidate.module for item in selected}) == 4
    assert selected[0].candidate.candidate_id == "a_m0"
    assert "z_old_high_score" not in {item.candidate.candidate_id for item in selected}
    assert all(item.selection_score is None for item in selected)
    assert all("static_coverage_score" not in item["selection_features"] for item in audit["records"])
    assert sum(item["disposition"] == "DEFERRED" for item in audit["records"]) == 3


def test_identical_candidate_id_is_audited_not_semantically_merged():
    canonical = _binding("same", module="m0", scope=("assignment:1",))
    duplicate = _binding("same", module="m9", scope=("assignment:99",))
    selected, audit = select_balanced_local_bindings([canonical, duplicate], budget=8, fraction=1.0, minimum=0)

    assert len(selected) == 1
    assert audit["unique_candidate_ids"] == 1
    assert audit["duplicate_candidate_ids"] == 1
    deferred = next(item for item in audit["records"] if item["reason"] == "IDENTICAL_CANDIDATE_ID_DEFERRED")
    assert deferred["structural_scope"] == ["assignment:99"]
