from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

from dateassertion.ir.schema import ObjectType, PropertyIR
from dateassertion.pipeline.native_measurements import (
    collect_measurements,
    generate_native_mutation_tcl,
    generate_proof_coi_core_tcl,
    run_measurements,
    _global_timeout_evidence,
)


def _property() -> PropertyIR:
    return PropertyIR(
        property_id="measurement.local", region_id="r", object_type=ObjectType.DATAPATH,
        family="DATA", template="DATA", bindings={}, signals=["a", "q"],
        source="test", llm_confidence=1.0, body="a |-> q", disable_iff="!rst_n", target_module="dut",
    )


def _record(cid: int, kind: str) -> str:
    return f"cid {{{cid}}} source_location {{(1,1)-(1,2)}} cover_item_type {{{kind}}}"


def _inputs(tmp_path: Path):
    rtl = tmp_path / "dut.sv"
    rtl.write_text("module dut(input clk, input rst_n, input a, output q); assign q=a; endmodule\n")
    sva = tmp_path / "fresh.sv"
    sva.write_text("p_measurement_local: assert property (@(posedge clk) disable iff (!rst_n) a |-> q);\n")
    target = {"design_id": "unit", "top": "dut", "clock": "clk", "reset": "rst_n", "reset_active_low": True,
              "rtl_files": [str(rtl)], "include_dirs": []}
    formal = {"executable": "/bin/true", "prove_orchestration": True, "proofgrid_max_local_jobs": 4,
              "engine_mode": "", "coverage_engine_mode": ""}
    return rtl, sva, target, {"formal": formal}


def test_final_tcls_have_exact_budgets_native_reporter_and_no_stale_sva(tmp_path):
    rtl, sva, target, cfg = _inputs(tmp_path)
    formal = cfg["formal"]
    proof = generate_proof_coi_core_tcl([str(rtl)], sva, target, formal, tmp_path / "proof").read_text()
    mutation = generate_native_mutation_tcl([str(rtl)], sva, target, formal, tmp_path / "mutation").read_text()
    for text in (proof, mutation):
        assert f"analyze -sv {{{sva.resolve()}}}" in text
        assert "set_prove_orchestration on" in text
        assert "set_proofgrid_max_local_jobs 4" in text
    assert "prove -all -asserts -time_limit 3600s" in proof
    assert "prove -all -covers -time_limit 60s" in proof
    assert "check_cov -measure -type coi -time_limit 3600s" in proof
    assert "-enable_prove_based_proof_core -proof_core_include_failing" in proof
    assert "set_prove_time_limit 0s" in proof
    assert "check_cov -measure -type proof -time_limit 0s" in proof
    assert "proof_core_unprocessed_audit.tsv" in proof
    assert "check_cov -measure -type mutation -time_limit 28800s" in mutation
    assert "report_effective.tcl" in mutation
    assert "mutate" not in mutation.lower()


def test_run_collects_normalized_coverage_and_keeps_baseline_cex(tmp_path):
    rtl, sva, target, cfg = _inputs(tmp_path)

    def fake_executor(command, cwd, **_kwargs):
        directory = Path(cwd); tcl = Path(command[-1]).read_text()
        if "MEASUREMENT_CORE_BEGIN" in tcl:
            (directory / "proof_formal_report.txt").write_text("[1] dut.p_measurement_local proven 1 s\n")
            (directory / "coi_coverage_report.txt").write_text("coi\n")
            (directory / "coi_items.tsv").write_text(
                f"covered_and_checked\tformal_status {{Covered and Checked}} checker_status {{Checked}} {_record(1, 'statement')}\n"
                f"unprocessed\tformal_status {{Covered and Checked}} checker_status {{Checked}} {_record(1, 'statement')}\n"
                f"unprocessed\tformal_status {{Unprocessed}} checker_status {{Unprocessed}} {_record(2, 'toggle')}\n"
            )
            (directory / "proof_core_items.tsv").write_text(f"covered_and_checked\t{_record(1, 'statement')}\n")
            (directory / "proof_core_unprocessed_audit.tsv").write_text(f"unprocessed\t{_record(2, 'toggle')}\n")
            (directory / "proof_core_coverage_report.txt").write_text("core\n")
            (directory / "proof_core_report.txt").write_text("core\n")
            return SimpleNamespace(returncode=0, stdout="ICD005 global time_limit 3600s\nMEASUREMENT_PROOF_DONE\nMEASUREMENT_COI_DONE\nMEASUREMENT_CORE_DONE\n", stderr="")
        if "MEASUREMENT_MUTATION_BASELINE_BEGIN" in tcl:
            (directory / "baseline_formal_report.txt").write_text("[1] dut.p_measurement_local cex 1 s\n")
            (directory / "mutation_items.tsv").write_text(f"uncovered_or_unchecked\t{_record(3, 'branch')}\n")
            (directory / "effective_formal_report.txt").write_text("effective\n")
            (directory / "mutation_coverage_report.txt").write_text("mutation\n")
            (directory / "mutation_effective.tsv").write_text("metrics\n")
            (directory / "mutation_effective_report.txt").write_text("metrics\n")
            return SimpleNamespace(returncode=0, stdout="MEASUREMENT_MUTATION_BASELINE_DONE\nMEASUREMENT_MUTATION_8H_DONE\n", stderr="")
        # This is the independent DUT-only stimuli Tcl; it must not contain SVA.
        assert str(sva.resolve()) not in tcl
        (directory / "coverage_statuses.tsv").write_text(f"covered\t{_record(4, 'branch')}\n")
        (directory / "reachability_report.txt").write_text("stimuli\n")
        return SimpleNamespace(returncode=0, stdout="MEASUREMENT_STIMULI_DONE\n", stderr="")

    result = run_measurements(SimpleNamespace(files=[str(rtl)]), target, cfg, sva, [_property()], tmp_path / "out", executor=fake_executor)
    assert result["status"] == "COMPLETE"
    coi = result["coi"]["by_cover_item_type"]
    assert coi["all"]["unprocessed"] == 1  # genuine item, not dropped with the overlapping CID
    assert coi["all"]["raw_denominator"] == 2
    assert coi["all"]["primary_effective_denominator"] == 2
    assert result["proof"]["actual"]["budget_accepted"] == 1
    assert result["native_mutation"]["eligibility"]["interpretation"] == "OBSERVED_WITH_BASELINE_LIMITATIONS"
    assert result["stimuli"]["branch"]["covered"] == 1
    assert (tmp_path / "out" / "proof_coi_core" / "stage_exit.json").is_file()


def test_exit_zero_without_required_artifacts_is_error_not_complete(tmp_path):
    out = tmp_path / "out"; proof = out / "proof_coi_core"; proof.mkdir(parents=True)
    (out / "properties.json").write_text(json.dumps([]))
    (proof / "stage_exit.json").write_text(json.dumps({"status": "EXITED", "return_code": 0}))
    (proof / "jaspergold.stdout.log").write_text("MEASUREMENT_PROOF_DONE\nMEASUREMENT_COI_DONE\nMEASUREMENT_CORE_DONE\n")
    result = collect_measurements(out)
    assert result["stages"]["proof_coi_core"]["state"] == "ERROR"
    assert result["status"] == "ERROR"


def test_collector_marks_missing_session_unfinished_not_zero(tmp_path):
    out = tmp_path / "out"; out.mkdir()
    (out / "properties.json").write_text(json.dumps([]))
    result = collect_measurements(out)
    assert result["status"] == "UNFINISHED"
    assert result["coi"] is None
    assert result["native_mutation"]["coverage"] is None


def test_proof_result_never_inherits_later_core_target_status(tmp_path):
    out = tmp_path / "out"; proof = out / "proof_coi_core"; proof.mkdir(parents=True)
    (proof / "proof_formal_report.txt").write_text("No property evaluated yet\n")
    (proof / "proof_core_report.txt").write_text("Name: dut.p_measurement_local\nProve status: proven\nPROOF_CORE: 42\n")
    result = collect_measurements(out, [_property()])
    assert result["proof"]["actual"]["proven"] == 0
    assert result["proof"]["actual"]["not_evaluated"] == 1


def test_global_budget_requires_expiry_not_just_command_or_later_core(tmp_path):
    log = tmp_path / "jaspergold.stdout.log"
    command = "[0.0] % prove -all -asserts -time_limit 3600s\n"
    log.write_text(command + "time_limit\n[3600.1] % puts MEASUREMENT_PROOF_DONE\nMEASUREMENT_PROOF_DONE\n")
    assert _global_timeout_evidence(tmp_path)["confirmed"]
    log.write_text(command + "Per property time limit expired (3600s)\nMEASUREMENT_PROOF_DONE\nICD005 global time_limit 3600s\n")
    assert not _global_timeout_evidence(tmp_path)["confirmed"]
    log.write_text(command + "time_limit\nMEASUREMENT_MUTATION_BASELINE_DONE\n")
    assert _global_timeout_evidence(tmp_path, "baseline_formal_report.txt")["confirmed"]
