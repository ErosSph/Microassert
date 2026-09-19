import pytest

from dateassertion.formal.jaspergold import execution_timeout, generate_tcl, _log_text


def test_wrapper_unlimited_does_not_mean_immediate_timeout():
    assert execution_timeout({}) == 900
    assert execution_timeout({"timeout_seconds": 600}) == 600
    assert execution_timeout({"timeout_seconds": 0}) is None
    assert execution_timeout({"timeout_seconds": None}) is None
    with pytest.raises(ValueError):
        execution_timeout({"timeout_seconds": -1})


def test_unlimited_core_preserves_finite_assertion_and_cover_budgets(tmp_path):
    tcl = generate_tcl([], str(tmp_path / "assertions.sv"), "dut", tmp_path,
                       {"proof_scope": "asserts", "prove_time_limit": "600s",
                        "precondition_probe_time_limit": "60s", "coverage_time_limit": "0s"}).read_text()
    assert "prove -all -asserts -time_limit 600s" in tcl
    assert "prove -all -covers -time_limit 60s" in tcl
    assert tcl.index("prove -all -covers") < tcl.index("set_prove_time_limit 0s") < tcl.index("check_cov -measure -type proof -time_limit 0s")


def test_timeout_captured_bytes_are_decoded():
    assert _log_text(b"partial output") == "partial output"
    assert _log_text(None) == ""
