"""Final, lossless Jasper measurements for a freshly generated portfolio.

This module intentionally does not decide which generated assertions are in a
portfolio.  Its only job is to measure the exact supplied SVA in three
independent Jasper projects and to collect evidence while those projects are
still running.  In particular, it never treats a missing export as zero
coverage and never turns an unresolved assertion into a proof merely because a
requested budget was present in Tcl.
"""

from __future__ import annotations

from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import threading
import time
from typing import Any, Callable, Iterable

from dateassertion.coverage_analysis.proof_core import stimuli_coverage_summary
from dateassertion.formal.jaspergold import generate_reachability_tcl
from dateassertion.formal.result_parser import parse_jasper_results
from dateassertion.ir.schema import PropertyIR, dump_json, properties_from_dict
from dateassertion.pipeline.checker_coverage import parse_checker_coverage_items, summarize_checker_items
from dateassertion.pipeline.design_flow import _resolve


SCHEMA = "measurement-final-e203-measurements.v1"
_NATIVE_REPORT = Path(__file__).resolve().parents[1] / "formal" / "report_effective.tcl"


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json(path: Path, default: Any) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8")) if path.is_file() else default
    except (OSError, json.JSONDecodeError):
        return default


def _atomic_dump_json(path: Path, value: Any) -> None:
    """Publish collector/stage state atomically while Jasper is writing files."""
    temporary = path.with_suffix(path.suffix + f".{os.getpid()}.{threading.get_ident()}.tmp")
    dump_json(temporary, value)
    temporary.replace(path)


def _formal_config(target: dict[str, Any], cfg: dict[str, Any]) -> dict[str, Any]:
    result = dict(cfg.get("formal", {}))
    # Requirement14 may be placed under measurement without changing the
    # established formal configuration surface.
    result.update(cfg.get("measurement", {}).get("formal", {}))
    result.update({
        "clock": target["clock"], "reset": target["reset"],
        "reset_active_low": bool(target.get("reset_active_low", True)),
        "include_dirs": [str(_resolve(value)) for value in target.get("include_dirs", [])],
    })
    return result


def _rtl_files(design: Any, target: dict[str, Any]) -> list[str]:
    files = list(getattr(design, "files", []) or [])
    if not files:
        files = [str(_resolve(value)) for value in target.get("rtl_files", [])]
    if not files:
        raise ValueError("Requirement14 measurement requires resolved RTL files")
    return [str(Path(value).resolve()) for value in files]


def _properties(values: Iterable[Any]) -> list[PropertyIR]:
    rows = list(values)
    return rows if all(isinstance(item, PropertyIR) for item in rows) else properties_from_dict(rows)


def _preamble(rtl_files: list[str], sva_path: Path, target: dict[str, Any], formal: dict[str, Any], coverage_type: str) -> list[str]:
    include_args = " ".join(f"-incdir {{{Path(value).resolve()}}}" for value in formal.get("include_dirs", []))
    proof_core_options = " -enable_prove_based_proof_core -proof_core_include_failing" if "proof" in coverage_type else ""
    lines = [
        "# Requirement14 exact fresh-portfolio measurement; generated records are not deduplicated.",
        "clear -all",
        "set_elaborate_single_run_mode off",
        f"check_cov -init -model {{branch statement expression toggle functional}} -type {coverage_type} -toggle_ports_only -exclude_bind_hierarchies{proof_core_options}",
    ]
    for rtl in rtl_files:
        lines.append("analyze -sv" + (f" {include_args}" if include_args else "") + f" {{{rtl}}}")
    lines.extend((
        f"analyze -sv {{{sva_path}}}",
        f"elaborate -top {target['top']}",
        f"clock {formal.get('clock', target['clock'])}",
        f"reset -expression {{{'!' if formal.get('reset_active_low', target.get('reset_active_low', True)) else ''}{formal.get('reset', target['reset'])}}}",
    ))
    if formal.get("prove_orchestration") is False:
        lines.append("set_prove_orchestration off")
    elif formal.get("prove_orchestration") is True:
        # Do not inherit a historical forced-off setting.  Requirement14's
        # fresh final portfolio deliberately uses Jasper's orchestration.
        lines.append("set_prove_orchestration on")
    if int(formal.get("proofgrid_max_local_jobs", 0)) > 0:
        lines.append(f"set_proofgrid_max_local_jobs {int(formal['proofgrid_max_local_jobs'])}")
    if formal.get("engine_mode"):
        lines.append(f"set_engine_mode {{{formal['engine_mode']}}}")
    return lines


def generate_proof_coi_core_tcl(
    rtl_files: list[str], sva_path: str | Path, target: dict[str, Any], formal: dict[str, Any], output_dir: str | Path,
) -> Path:
    """One independent session: 3600s assertions, COI, then unlimited core."""
    output = Path(output_dir).resolve(); output.mkdir(parents=True, exist_ok=True)
    lines = _preamble(rtl_files, Path(sva_path).resolve(), target, formal, "{proof coi}")
    lines.extend((
        "puts MEASUREMENT_PROOF_BEGIN",
        "prove -all -asserts -time_limit 3600s",
        # Covers are diagnostic only.  They are deliberately not allowed to
        # replace the assertion result in the collector.
        "prove -all -covers -time_limit 60s",
        "report -force -result -file {proof_formal_report.txt}",
        "puts MEASUREMENT_PROOF_DONE",
        "puts MEASUREMENT_COI_BEGIN",
        "check_cov -measure -type coi -time_limit 3600s",
        "check_cov -report -type formal -checker_mode coi -report_file {coi_coverage_report.txt} -force",
        "redirect -file {coi_items.tsv} -force { foreach s {covered_and_checked uncovered_or_unchecked unreachable_or_undetectable unprocessed} { foreach i [check_cov -list -status $s -checker_mode coi -silent] { puts \"$s\\t$i\" } } }",
        "puts MEASUREMENT_COI_DONE",
        "puts MEASUREMENT_CORE_BEGIN",
        "set_prove_time_limit 0s",
        "check_cov -measure -type proof -time_limit 0s",
        "check_cov -report -type formal -report_file {proof_core_coverage_report.txt} -force",
        # Jasper's list queries overlap.  Keep all four raw query rows, then
        # normalize by native CID/checker outcome in the collector so genuine
        # unprocessed items remain in the raw denominator without double count.
        "redirect -file {proof_core_items.tsv} -force { foreach s {covered_and_checked uncovered_or_unchecked unreachable_or_undetectable unprocessed} { foreach i [check_cov -list -status $s -silent] { puts \"$s\\t$i\" } } }",
        "redirect -file {proof_core_unprocessed_audit.tsv} -force { foreach i [check_cov -list -status unprocessed -silent] { puts \"unprocessed\\t$i\" } }",
        "set measurement_targets [check_cov -get_assert_id]",
        "redirect -file {proof_core_report.txt} -force {check_cov -get_target_info $measurement_targets -name -prove_status -proof_core}",
        "report -force -result -file {core_formal_report.txt}",
        "puts MEASUREMENT_CORE_DONE",
        "exit", "",
    ))
    path = output / "run_proof_coi_core.tcl"; path.write_text("\n".join(lines), encoding="utf-8")
    return path


def generate_native_mutation_tcl(
    rtl_files: list[str], sva_path: str | Path, target: dict[str, Any], formal: dict[str, Any], output_dir: str | Path,
) -> Path:
    """Native-only 8h mutation measurement; RTL and SVA are never modified."""
    if not _NATIVE_REPORT.is_file():
        raise RuntimeError(f"immutable native mutation reporter missing: {_NATIVE_REPORT}")
    output = Path(output_dir).resolve(); output.mkdir(parents=True, exist_ok=True)
    lines = _preamble(rtl_files, Path(sva_path).resolve(), target, formal, "mutation")
    lines.extend((
        "puts MEASUREMENT_MUTATION_BASELINE_BEGIN",
        "prove -all -asserts -time_limit 3600s",
        "report -force -result -file {baseline_formal_report.txt}",
        "puts MEASUREMENT_MUTATION_BASELINE_DONE",
        "set_prove_time_limit 0s",
        "puts MEASUREMENT_MUTATION_8H_BEGIN",
        "check_cov -measure -type mutation -time_limit 28800s",
        "check_cov -report -type formal -report_file {mutation_coverage_report.txt} -force",
        "report -force -result -file {effective_formal_report.txt}",
        f"source {{{_NATIVE_REPORT}}}",
        "puts MEASUREMENT_MUTATION_8H_DONE",
        "exit", "",
    ))
    path = output / "run_native_mutation.tcl"; path.write_text("\n".join(lines), encoding="utf-8")
    return path


def _generate_stimuli_tcl(rtl_files: list[str], target: dict[str, Any], formal: dict[str, Any], output: Path) -> Path:
    config = dict(formal)
    config["coverage_time_limit"] = "0s"
    # Explicit unlimited core/stimuli setting is needed even if a prior formal
    # default has an engineering cap.  This project intentionally has no SVA.
    path = generate_reachability_tcl(rtl_files, str(target["top"]), output, config)
    text = path.read_text(encoding="utf-8")
    text = text.replace(
        "check_cov -measure -type stimuli -time_limit 0s",
        "puts MEASUREMENT_STIMULI_BEGIN\nset_prove_time_limit 0s\ncheck_cov -measure -type stimuli -time_limit 0s",
    )
    text = text.replace("\nexit\n", "\nputs MEASUREMENT_STIMULI_DONE\nexit\n")
    path.write_text(text, encoding="utf-8")
    return path


def _measurement_checker_summary(items: list[Any], measurement_type: str) -> dict[str, Any]:
    """Coverage with Req14's primary denominator: total minus undetectable.

    The older final-measurement helper is retained as a diagnostic because its
    effective denominator excludes both unprocessed and undetectable.  Here a
    genuine ``unprocessed`` CID is known evidence and must remain counted.
    """
    legacy = summarize_checker_items(items, measurement_type)
    types = ("statement", "branch", "expression", "toggle", "functional")

    def one(group: list[Any]) -> dict[str, Any]:
        counts = Counter(item.status for item in group)
        checked = counts["covered_and_checked"]
        unchecked = counts["uncovered_or_unchecked"]
        undetectable = counts["unreachable_or_undetectable"]
        unprocessed = counts["unprocessed"]
        total = len(group)
        denominator = total - undetectable
        return {
            "checked": checked, "unchecked": unchecked,
            "unreachable_or_undetectable": undetectable, "unprocessed": unprocessed,
            "raw_denominator": total,
            "primary_effective_denominator": denominator,
            "primary_effective_percent": round(100 * checked / denominator, 2) if denominator else 0.0,
            "legacy_reachable_only_denominator": checked + unchecked,
            "legacy_reachable_only_percent": round(100 * checked / (checked + unchecked), 2) if checked + unchecked else 0.0,
        }

    summary = {kind: one([item for item in items if item.cover_item_type.lower() == kind]) for kind in types}
    summary["all"] = one(items)
    return {
        "measurement_type": measurement_type,
        "denominator_definition": "primary effective = checked / (all normalized CIDs - unreachable_or_undetectable); genuine unprocessed CIDs remain in the denominator.",
        "by_cover_item_type": summary,
        "legacy_diagnostic_excluding_unprocessed": legacy,
    }


def _measurement_stimuli_summary(path: Path) -> dict[str, Any]:
    """Add the primary effective denominator without hiding unprocessed RTL."""
    result = stimuli_coverage_summary(path)
    for kind, item in result.items():
        total = item["total"]
        denominator = total - item["unreachable_or_deadcode"]
        item["primary_effective_denominator"] = denominator
        item["primary_effective_percent"] = round(100 * item["covered"] / denominator, 2) if denominator else 0.0
        item["denominator_definition"] = "total minus confirmed unreachable/deadcode; unprocessed remains included"
    return result


def _command(tcl: Path, formal: dict[str, Any], project_name: str) -> tuple[list[str], dict[str, str]]:
    executable = formal.get("executable")
    if not executable:
        raise ValueError("formal.executable is required for Requirement14 measurement")
    env = os.environ.copy()
    if formal.get("license_file"):
        env[str(formal.get("license_env", "CDS_LIC_FILE"))] = str(formal["license_file"])
    return [str(Path(executable).resolve()), "-allow_unsupported_OS", "-batch", "-proj", str(tcl.parent / project_name), str(tcl)], env


def _run_session(name: str, tcl: Path, formal: dict[str, Any], executor: Callable[..., Any] | None) -> dict[str, Any]:
    """Run without a wrapper timeout, continuously writing the two log files."""
    directory = tcl.parent
    started = time.monotonic(); started_at = _now()
    try:
        command, env = _command(tcl, formal, f"jgproject_{name}")
        _atomic_dump_json(directory / "stage_running.json", {
            "stage": name, "status": "RUNNING", "pid": None, "started_at": started_at,
            "tcl": str(tcl), "project": str(directory / f"jgproject_{name}"),
        })
        if executor is not None:
            completed = executor(command, cwd=directory, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
            stdout, stderr, return_code = completed.stdout or "", completed.stderr or "", int(completed.returncode)
            (directory / "jaspergold.stdout.log").write_text(str(stdout), encoding="utf-8", errors="replace")
            (directory / "jaspergold.stderr.log").write_text(str(stderr), encoding="utf-8", errors="replace")
        else:
            # File handles make logs visible as Jasper runs.  No `timeout=` is
            # passed: a zero/unlimited formal budget must not be killed by us.
            with (directory / "jaspergold.stdout.log").open("w", encoding="utf-8") as stdout, (directory / "jaspergold.stderr.log").open("w", encoding="utf-8") as stderr:
                proc = subprocess.Popen(command, cwd=directory, env=env, stdout=stdout, stderr=stderr, text=True)
                _atomic_dump_json(directory / "stage_running.json", {
                    "stage": name, "status": "RUNNING", "pid": proc.pid, "started_at": started_at,
                    "tcl": str(tcl), "project": str(directory / f"jgproject_{name}"),
                })
                return_code = proc.wait()
        result = {"stage": name, "status": "EXITED", "return_code": return_code,
                  "started_at": started_at, "ended_at": _now(), "runtime_seconds": round(time.monotonic() - started, 3),
                  "tcl": str(tcl), "project": str(directory / f"jgproject_{name}"),
                  "stdout": str(directory / "jaspergold.stdout.log"), "stderr": str(directory / "jaspergold.stderr.log")}
    except Exception as exc:
        result = {"stage": name, "status": "ERROR", "return_code": None, "started_at": started_at,
                  "ended_at": _now(), "runtime_seconds": round(time.monotonic() - started, 3), "tcl": str(tcl),
                  "error": f"{type(exc).__name__}: {exc}"}
    _atomic_dump_json(directory / "stage_exit.json", result)
    return result


def _global_timeout_evidence(directory: Path, report: str = "proof_formal_report.txt") -> dict[str, Any]:
    logs = "\n".join((directory / name).read_text(encoding="utf-8", errors="replace")
                     for name in ("jaspergold.stdout.log", "jaspergold.stderr.log") if (directory / name).is_file())
    proof_report = (directory / report).read_text(encoding="utf-8", errors="replace") if (directory / report).is_file() else ""
    marker = "MEASUREMENT_MUTATION_BASELINE_DONE" if report == "baseline_formal_report.txt" else "MEASUREMENT_PROOF_DONE"
    # Only inspect the proof phase.  A proof/core project can spend days in
    # unlimited core after its proof report and marker have already landed.
    proof_text = logs.split(marker, 1)[0] + "\n" + proof_report
    remaining = "\n".join(line for line in proof_text.splitlines() if "per property time limit" not in line.lower())
    matched = bool(re.search(
        r"(?:ICD005[^\n]*?(?:time[_ ]limit)?[^\n]*?3600|time\s*limit\s*(?:expired|exceeded).*?3600(?:\.0+)?\s*s)",
        remaining, re.I,
    ))
    command = re.search(r"(?m)^\[.*?\]\s+%\s+prove\s+-all\s+-asserts\s+-time_limit\s+3600s\s*$", proof_text)
    returned_limit = False
    if command:
        after = proof_text[command.end():]
        next_prompt = re.search(r"(?m)^\[.*?\]\s+%", after)
        execution = after[:next_prompt.start()] if next_prompt else after
        returned_limit = bool(re.search(r"(?m)^time_limit\s*$", execution))
    matched = matched or returned_limit
    proof_done = marker in logs
    return {"confirmed": bool(proof_done and matched), "global_3600_marker": matched,
            "proof_phase_complete_marker": proof_done,
            "excludes_per_property_slices": True}


def _formal_metrics(properties: list[PropertyIR], directory: Path, report: str, core: str, coverage: str, *, use_log: bool = True) -> dict[str, Any]:
    # Baseline mutation proof must be read in isolation.  In particular it
    # must not inherit proof-core status text emitted later in its session.
    log_path = directory / "jaspergold.stdout.log" if use_log else directory / "baseline_phase_only_no_log.txt"
    parsed, summary, _coverage = parse_jasper_results(properties, directory / report, directory / core, directory / coverage, log_path)
    evidence = _global_timeout_evidence(directory, report)
    # parse_jasper_results uses TIMEOUT_ACCEPTED as an intentionally generic
    # parser label.  Requirement14 calls it accepted only with concrete global
    # budget evidence, keeping actual proof and accepted timeout separate.
    accepted = summary["proven"] + (summary["timeout_accepted"] if evidence["confirmed"] else 0)
    return {"actual": {"proven": summary["proven"], "cex": summary["failed"], "unresolved": summary["timeout_accepted"],
                       "not_evaluated": summary["not_evaluated"], "errors": summary["errors"],
                       "budget_accepted": accepted, "confirmed_timeout_unresolved": summary["timeout_accepted"] if evidence["confirmed"] else 0},
            "per_property": [asdict(item) for item in parsed], "budget_timeout_evidence": evidence}


def _stage_state(directory: Path, *, markers: tuple[str, ...], artifacts: tuple[str, ...]) -> str:
    exit_data = _read_json(directory / "stage_exit.json", None)
    if not isinstance(exit_data, dict):
        return "UNFINISHED"
    if exit_data.get("status") == "ERROR" or exit_data.get("return_code") not in (0, None):
        return "ERROR"
    if exit_data.get("return_code") is None:
        return "UNFINISHED"
    text = "\n".join((directory / name).read_text(encoding="utf-8", errors="replace")
                     for name in ("jaspergold.stdout.log", "jaspergold.stderr.log") if (directory / name).is_file())
    missing_markers = [marker for marker in markers if marker not in text]
    missing_artifacts = [name for name in artifacts if not (directory / name).is_file()]
    return "EXITED" if not missing_markers and not missing_artifacts else "ERROR"


def _safe(errors: list[dict[str, str]], context: str, func: Callable[..., Any], *args: Any, **kwargs: Any) -> Any:
    try:
        return func(*args, **kwargs)
    except Exception as exc:
        errors.append({"context": context, "error": f"{type(exc).__name__}: {exc}"})
        return None


def _render_report(metrics: dict[str, Any]) -> str:
    """Small live-readable companion to metrics.json (no inference from blanks)."""
    lines = ["# Requirement 14 final measurement", "", f"Status: {metrics['status']}",
             f"Generated records: {metrics['generated_property_count']} (no deduplication; no proof-status filter).", ""]
    proof = metrics.get("proof") or {}; actual = proof.get("actual", {})
    lines += ["## Assertion proof", "",
              f"Actual proven: {actual.get('proven', 'UNFINISHED')}; CEX: {actual.get('cex', 'UNFINISHED')}; unresolved: {actual.get('unresolved', 'UNFINISHED')}; budget-accepted: {actual.get('budget_accepted', 'UNFINISHED')}."]
    mutation = metrics.get("native_mutation", {}).get("eligibility") or {}
    lines += ["", "## Native mutation", "", f"Eligibility: {mutation.get('interpretation', 'UNFINISHED')}; baseline CEX: {mutation.get('cex', 'UNFINISHED')}.",
              "", "## Session state", ""]
    lines += [f"- {name}: {value['state']} ({value['directory']})" for name, value in metrics["stages"].items()]
    if metrics["collector_errors"]:
        lines += ["", "## Collector errors", "", *[f"- {item['context']}: {item['error']}" for item in metrics["collector_errors"]]]
    return "\n".join(lines) + "\n"


def collect_measurements(output_root: str | Path, properties: Iterable[Any] | None = None) -> dict[str, Any]:
    """Read artifacts safely during execution; it never launches or alters Jasper."""
    root = Path(output_root).resolve(); manifest = _read_json(root / "measurement_manifest.json", {})
    if properties is None:
        properties = _read_json(root / "properties.json", [])
    props = _properties(properties)
    errors: list[dict[str, str]] = []
    stages: dict[str, Any] = {}
    proof_dir, mutation_dir, stimuli_dir = root / "proof_coi_core", root / "native_mutation", root / "stimuli"
    proof: dict[str, Any] = {"state": _stage_state(
        proof_dir, markers=("MEASUREMENT_PROOF_DONE", "MEASUREMENT_COI_DONE", "MEASUREMENT_CORE_DONE"),
        artifacts=("proof_formal_report.txt", "coi_coverage_report.txt", "coi_items.tsv", "proof_core_coverage_report.txt", "proof_core_items.tsv", "proof_core_report.txt"),
    ), "directory": str(proof_dir)}
    if proof_dir.is_dir():
        if (proof_dir / "proof_formal_report.txt").is_file():
            proof["formal"] = _safe(errors, "proof.formal", _formal_metrics, props, proof_dir, "proof_formal_report.txt", "unused_core.txt", "unused_coverage.txt", use_log=False)
        if (proof_dir / "coi_items.tsv").is_file():
            parsed = _safe(errors, "coi.items", parse_checker_coverage_items, proof_dir / "coi_items.tsv")
            if parsed is not None:
                items, audit = parsed; proof["coi"] = _measurement_checker_summary(items, "coi") | {"cid_query_normalization_audit": audit}
        if (proof_dir / "proof_core_items.tsv").is_file():
            parsed = _safe(errors, "core.items", parse_checker_coverage_items, proof_dir / "proof_core_items.tsv")
            if parsed is not None:
                items, audit = parsed
                core = _measurement_checker_summary(items, "proof")
                proof["effective_proof_core"] = core | {
                    "primary_percent": core["by_cover_item_type"]["all"]["primary_effective_percent"],
                    "cid_query_normalization_audit": audit,
                    "unprocessed_query_rows_audit": sum("\t" in row for row in (proof_dir / "proof_core_unprocessed_audit.tsv").read_text(encoding="utf-8", errors="replace").splitlines()) if (proof_dir / "proof_core_unprocessed_audit.tsv").is_file() else None,
                }
    stages["proof_coi_core"] = proof
    mutation: dict[str, Any] = {"state": _stage_state(
        mutation_dir, markers=("MEASUREMENT_MUTATION_BASELINE_DONE", "MEASUREMENT_MUTATION_8H_DONE"),
        artifacts=("baseline_formal_report.txt", "effective_formal_report.txt", "mutation_coverage_report.txt", "mutation_items.tsv", "mutation_effective.tsv", "mutation_effective_report.txt"),
    ), "directory": str(mutation_dir)}
    if mutation_dir.is_dir():
        mutation["baseline"] = _safe(errors, "mutation.baseline", _formal_metrics, props, mutation_dir, "baseline_formal_report.txt", "unused_core.txt", "unused_coverage.txt", use_log=False)
        baseline = mutation.get("baseline") or {}; actual = baseline.get("actual", {})
        participation = "MEASUREMENT_MUTATION_8H_DONE" in "\n".join(
            (mutation_dir / name).read_text(encoding="utf-8", errors="replace")
            for name in ("jaspergold.stdout.log", "jaspergold.stderr.log") if (mutation_dir / name).is_file()
        )
        mutation["eligibility"] = {
            "all_assertions_proven": bool(props) and actual.get("proven") == len(props),
            "cex": actual.get("cex"), "unresolved": actual.get("unresolved"), "errors": actual.get("errors"),
            "jasper_mutation_participation_evidence": participation,
            "baseline_limitations": [] if bool(props) and actual.get("proven") == len(props) else ["Baseline contains CEX, unresolved, errors, or no completed proof evidence; native mutation observation is retained but not a clean-baseline fault-detection claim."],
            "interpretation": "CLEAN_BASELINE" if bool(props) and actual.get("proven") == len(props) else "OBSERVED_WITH_BASELINE_LIMITATIONS",
        }
        if (mutation_dir / "mutation_items.tsv").is_file():
            parsed = _safe(errors, "mutation.items", parse_checker_coverage_items, mutation_dir / "mutation_items.tsv")
            if parsed is not None:
                items, audit = parsed; mutation["effective_native_mutation"] = _measurement_checker_summary(items, "mutation") | {"cid_query_normalization_audit": audit}
    stages["native_mutation"] = mutation
    stimuli: dict[str, Any] = {"state": _stage_state(
        stimuli_dir, markers=("MEASUREMENT_STIMULI_DONE",),
        artifacts=("coverage_statuses.tsv", "reachability_report.txt"),
    ), "directory": str(stimuli_dir)}
    if (stimuli_dir / "coverage_statuses.tsv").is_file():
        # The generic reachability generator has this stable filename.
        stimuli["coverage"] = _safe(errors, "stimuli.items", _measurement_stimuli_summary, stimuli_dir / "coverage_statuses.tsv")
    stages["stimuli"] = stimuli
    states = [value["state"] for value in stages.values()]
    status = "COMPLETE" if states == ["EXITED"] * 3 and not errors else "ERROR" if "ERROR" in states or errors else "UNFINISHED"
    result = {"schema": SCHEMA, "collected_at": _now(), "status": status, "manifest": manifest,
              "generated_property_count": len(props), "stages": stages, "collector_errors": errors,
              "proof": proof.get("formal"), "coi": proof.get("coi"), "effective_proof_core": proof.get("effective_proof_core"),
              "native_mutation": {"eligibility": mutation.get("eligibility"), "coverage": mutation.get("effective_native_mutation")},
              "stimuli": stimuli.get("coverage")}
    _atomic_dump_json(root / "metrics.json", result)
    _atomic_dump_json(root / "measurement_report.json", result)
    report_temp = root / f"measurement_report.md.{os.getpid()}.{threading.get_ident()}.tmp"
    report_temp.write_text(_render_report(result), encoding="utf-8")
    report_temp.replace(root / "measurement_report.md")
    return result


def run_measurements(
    design: Any, target: dict[str, Any], cfg: dict[str, Any], sva_path: str | Path,
    properties: Iterable[Any], output_root: str | Path, *, executor: Callable[..., Any] | None = None,
) -> dict[str, Any]:
    """Generate and run three concurrent independent final measurement sessions.

    The public six-argument form is used by the Requirement14 driver.  The
    optional executor exists solely for deterministic unit tests; unlike a
    subprocess timeout it cannot impose an accidental wrapper deadline.
    """
    root = Path(output_root).resolve(); root.mkdir(parents=True, exist_ok=True)
    sva = Path(sva_path).resolve()
    if not sva.is_file():
        raise FileNotFoundError(f"fresh SVA does not exist: {sva}")
    props = _properties(properties)
    rtl = _rtl_files(design, target); formal = _formal_config(target, cfg)
    if (root / "measurement_manifest.json").exists():
        raise RuntimeError(f"refusing to overwrite Requirement14 measurement evidence: {root}")
    dump_json(root / "properties.json", [asdict(item) for item in props])
    manifest = {"schema": SCHEMA, "status": "PREPARED", "created_at": _now(), "design_id": target.get("design_id"),
                "top": target["top"], "rtl_files": rtl, "rtl_sha256": {path: _sha256(Path(path)) for path in rtl},
                "sva_path": str(sva), "sva_sha256": _sha256(sva), "property_ids": [item.property_id for item in props],
                "deduplicated": False, "proof_status_filter": None,
                "budgets": {"assert_prove": "3600s", "cover_diagnostic": "60s", "coi": "3600s", "core": "0s", "native_mutation": "28800s", "stimuli": "0s"},
                "preservation": "Independent projects; no source or SVA mutation; intermediate reports remain in each session directory."}
    dump_json(root / "measurement_manifest.json", manifest)
    tcls = {
        "proof_coi_core": generate_proof_coi_core_tcl(rtl, sva, target, formal, root / "proof_coi_core"),
        "native_mutation": generate_native_mutation_tcl(rtl, sva, target, formal, root / "native_mutation"),
        "stimuli": _generate_stimuli_tcl(rtl, target, formal, root / "stimuli"),
    }
    # Launch only when this public function is called by the driver.  Workers
    # share no project directory and deliberately have no host-side deadline.
    with ThreadPoolExecutor(max_workers=3, thread_name_prefix="measurement-jasper") as pool:
        futures = {pool.submit(_run_session, name, tcl, formal, executor): name for name, tcl in tcls.items()}
        exits = {futures[future]: future.result() for future in as_completed(futures)}
    manifest["status"] = "EXITED"; manifest["stage_exits"] = exits; manifest["completed_at"] = _now()
    dump_json(root / "measurement_manifest.json", manifest)
    return collect_measurements(root, props)
