"""Isolated final checker-coverage measurements for Requirement 12.

COI is measured by JasperGold as the union of the *final assertion
portfolio's* cones of influence.  It is never approximated by summing the
per-property COI files, which would double-count shared RTL cover items.
Native Jasper mutation coverage is an independent checker-coverage experiment;
it complements, but is not conflated with, the source-level sampled mutation
campaign in :mod:`dateassertion.pipeline.feedback_mutation`.
"""

from __future__ import annotations

from collections import Counter
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from typing import Any, Callable

from dateassertion.coverage_analysis.proof_core import CoverItem, split_tcl_list
from dateassertion.formal.result_parser import parse_jasper_results
from dateassertion.ir.schema import dump_json, properties_from_dict
from dateassertion.pipeline.design_flow import _resolve
from dateassertion.rtl_frontend.parser import parse_rtl


SCHEMA = "feedback-final-measurements.v1"
USER_AUTHORIZED_FINALIZATION_SCHEMA = "feedback-user-authorized-finalization.v1"
USER_AUTHORIZED_FINALIZATION_FILE = "user_authorized_finalization.json"
_STATUSES = (
    "covered_and_checked", "uncovered_or_unchecked",
    "unreachable_or_undetectable", "unprocessed",
)


class CheckerCoverageExportError(ValueError):
    """The isolated checker export contains irreconcilable item evidence."""


def _checker_status(raw_status: str, formal_status: str, checker_status: str) -> str:
    """Normalize a Jasper item using its own checker/formal result.

    ``check_cov -list -status unprocessed`` is an overlapping query in
    JasperGold 21.12: it may return an item that was already emitted under
    ``covered_and_checked`` while retaining ``checker_status {Checked}``.
    The list selector is therefore not an outcome field.  The per-item
    checker/formal fields are.  We retain a raw-query audit and only merge
    duplicate CID rows when their literal source fingerprint and normalized
    checker outcome agree.
    """

    checker = checker_status.strip().lower()
    formal = formal_status.strip().lower()
    checker_outcome = {
        "checked": "covered_and_checked", "unchecked": "uncovered_or_unchecked",
        "undetectable": "unreachable_or_undetectable", "unreachable": "unreachable_or_undetectable",
        "unprocessed": "unprocessed",
    }.get(checker)
    formal_outcome = {
        "covered and checked": "covered_and_checked", "uncovered or unchecked": "uncovered_or_unchecked",
        "unreachable or undetectable": "unreachable_or_undetectable", "unprocessed": "unprocessed",
    }.get(formal)
    # The actual V2 exports show these two fields agree.  Do not hide a
    # checker/formal disagreement behind an ``or``: it would make an
    # ambiguous Jasper result look like a valid coverage outcome.
    if checker_outcome and formal_outcome and checker_outcome != formal_outcome:
        raise CheckerCoverageExportError(
            "checker_status and formal_status disagree "
            f"({checker_status!r} versus {formal_status!r})"
        )
    return checker_outcome or formal_outcome or raw_status


def _checker_export_record(payload: str, path: Path, line_number: int, raw_status: str) -> CoverItem:
    """Parse one list row without the proof-core parser's strict status rule."""

    values = split_tcl_list(payload.strip())
    if len(values) % 2:
        raise CheckerCoverageExportError(
            f"odd Jasper checker-coverage record at {path}:{line_number}"
        )
    raw = dict(zip(values[0::2], values[1::2]))
    try:
        location = re.fullmatch(r"\((\d+),(\d+)\)-\((\d+),(\d+)\)", raw["source_location"])
        if not location:
            raise ValueError("missing/invalid source_location")
        return CoverItem(
            cid=int(raw["cid"]),
            status=_checker_status(raw_status, raw.get("formal_status", ""), raw.get("checker_status", "")),
            formal_status=raw.get("formal_status", ""), checker_status=raw.get("checker_status", ""),
            cover_item_type=raw.get("cover_item_type", ""), description=raw.get("description", ""),
            expression=raw.get("expression", ""), module=raw.get("module", ""),
            instance=raw.get("instance", ""), file=raw.get("file", ""),
            line_start=int(location.group(1)), column_start=int(location.group(2)),
            line_end=int(location.group(3)), column_end=int(location.group(4)),
        )
    except (KeyError, ValueError) as exc:
        raise CheckerCoverageExportError(
            f"invalid Jasper checker-coverage record at {path}:{line_number}: {exc}"
        ) from exc


def _item_fingerprint(item: CoverItem) -> tuple[Any, ...]:
    return (
        item.file, item.line_start, item.column_start, item.line_end, item.column_end,
        item.cover_item_type, item.description, item.expression, item.module, item.instance,
    )


def parse_checker_coverage_items(path: str | Path) -> tuple[list[CoverItem], dict[str, Any]]:
    """Parse an isolated COI/native-mutation export with safe overlap merging.

    This function is intentionally local to final measurements.  The generic
    proof-core parser remains strict because a duplicate proof-core status is
    an evidence error there.  Here Jasper's documented list queries overlap,
    so duplicates are admissible only after the row's own formal/checker
    fields establish one identical outcome.
    """

    source = Path(path)
    if not source.is_file():
        return [], {"raw_rows": 0, "unique_items": 0, "duplicate_rows": 0,
                    "normalized_query_rows": 0, "query_status_counts": {},
                    "canonical_status_counts": {}}
    by_id: dict[int, CoverItem] = {}
    raw_statuses: Counter[str] = Counter()
    canonical_statuses: Counter[str] = Counter()
    duplicates = normalized = rows = 0
    for line_number, line in enumerate(source.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if "\t" not in line:
            continue
        raw_status, payload = line.split("\t", 1)
        if raw_status not in _STATUSES:
            raise CheckerCoverageExportError(
                f"unknown Jasper checker-coverage list status {raw_status!r} at {source}:{line_number}"
            )
        item = _checker_export_record(payload, source, line_number, raw_status)
        rows += 1
        raw_statuses[raw_status] += 1
        canonical_statuses[item.status] += 1
        normalized += int(raw_status != item.status)
        previous = by_id.get(item.cid)
        if previous is not None:
            duplicates += 1
            if _item_fingerprint(previous) != _item_fingerprint(item):
                raise CheckerCoverageExportError(
                    f"CID {item.cid} has conflicting source evidence in {source}:{line_number}"
                )
            if previous.status != item.status:
                raise CheckerCoverageExportError(
                    f"CID {item.cid} has conflicting intrinsic checker outcomes in {source}:{line_number}"
                )
            continue
        by_id[item.cid] = item
    items = sorted(by_id.values(), key=lambda item: item.cid)
    return items, {
        "raw_rows": rows, "unique_items": len(items), "duplicate_rows": duplicates,
        "normalized_query_rows": normalized, "query_status_counts": dict(sorted(raw_statuses.items())),
        "canonical_status_counts": dict(sorted(Counter(item.status for item in items).items())),
    }


def _read(path: Path, default: Any = None) -> Any:
    return json.loads(path.read_text(encoding="utf-8")) if path.is_file() else deepcopy(default)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _property_label(property_id: str) -> str:
    return "p_" + re.sub(r"[^A-Za-z0-9_$]", "_", property_id)


def _final_round_root(root: Path, summary: dict[str, Any]) -> Path:
    # ``final_portfolio_round`` differs from ``rounds_completed`` only for a
    # separately audited user-authorized cutoff.  It is deliberately not
    # written into feedback_summary.json, which remains the historical record
    # of the interrupted ten-round feedback run.
    return root / "rounds" / f"round_{int(summary.get('final_portfolio_round', summary['rounds_completed'])):02d}"


def _strict_round_portfolio(round_root: Path) -> tuple[Path, Path, list[Any], dict[str, Any]]:
    """Validate the exact strict portfolio emitted by one completed round."""

    round_summary = _read(round_root / "round_summary.json")
    if round_summary.get("status") != "COMPLETE":
        raise RuntimeError(f"final feedback round is not complete: {round_root}")
    properties_path = round_root / "active_properties.json"
    assertions_path = round_root / "formal" / "cumulative" / "assertions.sv"
    if not properties_path.is_file() or not assertions_path.is_file():
        raise RuntimeError(
            "completed feedback round lacks exact final properties/assertions: "
            f"{properties_path}, {assertions_path}"
        )
    properties = properties_from_dict(_read(properties_path, []))
    if not properties:
        raise RuntimeError("final feedback portfolio is empty")
    assertion_text = assertions_path.read_text(encoding="utf-8", errors="replace")
    missing = [item.property_id for item in properties if _property_label(item.property_id) not in assertion_text]
    if missing:
        raise RuntimeError(f"final assertions do not contain final portfolio labels: {missing[:8]}")
    formal_root = round_root / "formal" / "cumulative" / "formal"
    result = _read(formal_root / "formal_results.json")
    expected_ids = {item.property_id for item in properties}
    result_ids = {item.get("property_id") for item in result.get("results", [])}
    bad = [
        item.get("property_id") for item in result.get("results", [])
        if item.get("property_id") in expected_ids
        and not (item.get("result") == "PASS" and item.get("vacuity") == "NON_VACUOUS")
    ]
    if result.get("status") != "PASS" or result_ids != expected_ids or bad:
        raise RuntimeError(
            "final cumulative Formal result is not the exact strict portfolio: "
            f"status={result.get('status')}, missing={sorted(expected_ids - result_ids)[:8]}, "
            f"extra={sorted(result_ids - expected_ids)[:8]}, bad={bad[:8]}"
        )
    identity = _read(formal_root / "input_identity.json")
    if not identity or identity.get("sva_sha256") != _sha256(assertions_path):
        raise RuntimeError("final formal input identity is absent or its saved SVA digest does not match assertions.sv")
    return assertions_path, properties_path, properties, round_summary


def create_user_authorized_finalization(
    feedback_root: str | Path, cutoff_round: int, *, authorization: str,
) -> dict[str, Any]:
    """Create an additive, hash-bound record for an explicit early cutoff.

    This is intentionally not a feedback summary and does not change the
    feedback manifest or retry the failed round.  The next round must already
    contain an external-service failure record, so a local algorithm failure
    cannot be silently relabelled as a user cutoff.
    """

    root = Path(feedback_root).resolve()
    if not authorization.strip():
        raise ValueError("an explicit user authorization string is required")
    selected = root / "rounds" / f"round_{int(cutoff_round):02d}"
    assertions, properties, _items, round_summary = _strict_round_portfolio(selected)
    next_root = root / "rounds" / f"round_{int(cutoff_round) + 1:02d}"
    failed = _read(next_root / "round_failure.json")
    service_failure = _read(next_root / "external_service_failure.json")
    if failed.get("status") != "FAILED" or failed.get("reason") != "LLM_UNAVAILABLE_EXTERNAL_SERVICE" or not service_failure:
        raise RuntimeError("user cutoff is allowed only when the immediately following round records an external LLM-service failure")
    formal_root = selected / "formal" / "cumulative" / "formal"
    hashes = {
        "round_summary_sha256": _sha256(selected / "round_summary.json"),
        "active_properties_sha256": _sha256(properties),
        "assertions_sha256": _sha256(assertions),
        "formal_results_sha256": _sha256(formal_root / "formal_results.json"),
        "input_identity_sha256": _sha256(formal_root / "input_identity.json"),
        "next_round_failure_sha256": _sha256(next_root / "round_failure.json"),
        "next_external_service_failure_sha256": _sha256(next_root / "external_service_failure.json"),
    }
    audit = {
        "schema": USER_AUTHORIZED_FINALIZATION_SCHEMA,
        "status": "USER_AUTHORIZED_CUTOFF",
        "authorization": authorization,
        "cutoff_round": int(cutoff_round),
        "selected_round_status": round_summary.get("status"),
        "next_round": int(cutoff_round) + 1,
        "next_round_status": failed.get("status"),
        "next_round_reason": failed.get("reason"),
        "next_round_error": failed.get("error"),
        "selected_round": str(selected),
        "next_failed_round": str(next_root),
        "hashes": hashes,
        "preservation": "The failed next round is retained as evidence; no feedback artifacts were regenerated or rewritten.",
    }
    dump_json(root / USER_AUTHORIZED_FINALIZATION_FILE, audit)
    return audit


def _user_authorized_cutoff_summary(root: Path) -> dict[str, Any] | None:
    """Return a synthetic selection descriptor only after rechecking its audit."""

    audit_path = root / USER_AUTHORIZED_FINALIZATION_FILE
    audit = _read(audit_path)
    if not audit:
        return None
    if audit.get("schema") != USER_AUTHORIZED_FINALIZATION_SCHEMA or audit.get("status") != "USER_AUTHORIZED_CUTOFF":
        raise RuntimeError("invalid user-authorized finalization audit")
    cutoff = int(audit.get("cutoff_round", 0))
    selected = root / "rounds" / f"round_{cutoff:02d}"
    next_root = root / "rounds" / f"round_{cutoff + 1:02d}"
    expected = audit.get("hashes", {})
    actual_paths = {
        "round_summary_sha256": selected / "round_summary.json",
        "active_properties_sha256": selected / "active_properties.json",
        "assertions_sha256": selected / "formal" / "cumulative" / "assertions.sv",
        "formal_results_sha256": selected / "formal" / "cumulative" / "formal" / "formal_results.json",
        "input_identity_sha256": selected / "formal" / "cumulative" / "formal" / "input_identity.json",
        "next_round_failure_sha256": next_root / "round_failure.json",
        "next_external_service_failure_sha256": next_root / "external_service_failure.json",
    }
    mismatched = [key for key, path in actual_paths.items() if not path.is_file() or expected.get(key) != _sha256(path)]
    if mismatched:
        raise RuntimeError(f"user-authorized finalization audit no longer matches saved artifacts: {mismatched}")
    failed = _read(next_root / "round_failure.json")
    if failed.get("status") != "FAILED" or failed.get("reason") != "LLM_UNAVAILABLE_EXTERNAL_SERVICE":
        raise RuntimeError("user-authorized finalization no longer has the required next-round external-service failure")
    selected_summary = _read(selected / "round_summary.json")
    return {
        "schema": USER_AUTHORIZED_FINALIZATION_SCHEMA,
        "status": "USER_AUTHORIZED_CUTOFF",
        "rounds_requested": cutoff + 1,
        "rounds_completed": cutoff,
        "final_portfolio_round": cutoff,
        "final_effective_proof_core": selected_summary.get("effective_proof_core"),
        "user_authorized_finalization": str(audit_path),
    }


def resolve_final_portfolio(
    feedback_root: str | Path,
) -> tuple[Path, Path, list[Any], dict[str, Any]]:
    """Return exact final assertions and properties from a completed ten-round run."""

    root = Path(feedback_root).resolve()
    summary = _read(root / "feedback_summary.json")
    if not summary or int(summary.get("rounds_completed", 0)) < int(summary.get("rounds_requested", 1)):
        summary = _user_authorized_cutoff_summary(root)
    if not summary:
        raise RuntimeError("feedback_root has no completed final feedback summary")
    rounds = int(summary["final_portfolio_round"] if "final_portfolio_round" in summary else summary["rounds_completed"])
    round_root = _final_round_root(root, summary)
    assertions_path, properties_path, properties, _round_summary = _strict_round_portfolio(round_root)
    return assertions_path, properties_path, properties, summary


def _formal_config(target: dict[str, Any], cfg: dict[str, Any]) -> dict[str, Any]:
    result = deepcopy(cfg.get("formal", {}))
    result.update({
        "clock": target["clock"], "reset": target["reset"],
        "reset_active_low": bool(target.get("reset_active_low", True)),
        "include_dirs": [str(_resolve(item)) for item in target.get("include_dirs", [])],
    })
    return result


def _validate_fresh_identity(
    feedback_root: Path, feedback_summary: dict[str, Any], assertions: Path,
    design: Any, target: dict[str, Any], cfg: dict[str, Any], formal_config: dict[str, Any],
) -> dict[str, Any]:
    """Ensure final evidence and fresh checker inputs describe the same DUT."""

    formal_root = _final_round_root(feedback_root, feedback_summary) / "formal" / "cumulative" / "formal"
    identity = _read(formal_root / "input_identity.json")
    inputs = identity.get("inputs", {})
    expected = {
        "source_digest": design.source_digest,
        "top": str(target["top"]), "clock": str(target["clock"]),
        "reset": str(target["reset"]), "reset_active_low": bool(target.get("reset_active_low", True)),
        "include_dirs": [str(Path(item).resolve()) for item in formal_config.get("include_dirs", [])],
    }
    mismatch = {
        key: {"saved": inputs.get(key), "fresh": value}
        for key, value in expected.items() if inputs.get(key) != value
    }
    saved_formal = inputs.get("formal", {})
    current_formal = cfg.get("formal", {})
    missing_formal_keys = sorted(key for key in current_formal if key not in saved_formal)
    config_mismatch = {
        key: {"saved": saved_formal.get(key), "fresh": value}
        for key, value in current_formal.items()
        if key in saved_formal and saved_formal.get(key) != value
    }
    if mismatch or missing_formal_keys or config_mismatch or identity.get("sva_sha256") != _sha256(assertions):
        raise RuntimeError(
            "final formal identity does not match fresh final measurement inputs: "
            f"input_mismatch={mismatch}, missing_formal_keys={missing_formal_keys}, "
            f"formal_config_mismatch={config_mismatch}"
        )
    return {"identity_path": str(formal_root / "input_identity.json"), "identity_sha256": identity.get("sha256"),
            "sva_sha256": identity.get("sva_sha256"), "source_digest": design.source_digest}


def generate_checker_coverage_tcl(
    rtl_files: list[str], property_file: str, top_module: str, output_dir: str | Path,
    formal_config: dict[str, Any], measurement_type: str,
) -> Path:
    """Generate one isolated Jasper checker-coverage session (COI or mutation)."""

    if measurement_type not in {"coi", "mutation"}:
        raise ValueError("measurement_type must be 'coi' or 'mutation'")
    output = Path(output_dir).resolve()
    output.mkdir(parents=True, exist_ok=True)
    coverage_limit = str(formal_config.get("coverage_time_limit", formal_config.get("prove_time_limit", "300s")))
    include_args = " ".join(f"-incdir {{{Path(item).resolve()}}}" for item in formal_config.get("include_dirs", []))
    lines = [
        "# Req12 isolated final checker-coverage session; never writes proof-core artifacts.",
        "clear -all",
        "set_elaborate_single_run_mode off",
        f"check_cov -init -model {{branch statement expression toggle functional}} -type {measurement_type} -toggle_ports_only -exclude_bind_hierarchies",
    ]
    for rtl in rtl_files:
        lines.append("analyze -sv" + (f" {include_args}" if include_args else "") + f" {{{Path(rtl).resolve()}}}")
    lines += [
        f"analyze -sv {{{Path(property_file).resolve()}}}",
        f"elaborate -top {top_module}",
        f"clock {formal_config.get('clock', 'clk')}",
    ]
    reset = str(formal_config.get("reset", "resetn"))
    reset_expr = f"!{reset}" if bool(formal_config.get("reset_active_low", True)) else reset
    checker_mode = " -checker_mode coi" if measurement_type == "coi" else ""
    if formal_config.get("prove_orchestration") is False:
        lines.append("set_prove_orchestration off")
    if int(formal_config.get("proofgrid_max_local_jobs", 0)) > 0:
        lines.append(f"set_proofgrid_max_local_jobs {int(formal_config['proofgrid_max_local_jobs'])}")
    if formal_config.get("engine_mode"):
        lines.append(f"set_engine_mode {{{formal_config['engine_mode']}}}")
    lines += [
        f"reset -expression {{{reset_expr}}}",
        f"prove -all -time_limit {formal_config.get('prove_time_limit', '300s')}",
        f"check_cov -measure -type {measurement_type} -time_limit {coverage_limit}",
        f"check_cov -report -type formal{checker_mode} -report_file {{{measurement_type}_coverage_report.txt}} -force",
        f"redirect -file {{{measurement_type}_items.tsv}} -force {{",
        f"    foreach status {{{' '.join(_STATUSES)}}} {{",
        f"        foreach item [check_cov -list -status $status{checker_mode} -silent] {{",
        "            puts \"$status\\t$item\"",
        "        }",
        "    }",
        "}",
        "report -force -result -file {formal_report.txt}",
        "exit",
        "",
    ]
    path = output / f"run_{measurement_type}.tcl"
    path.write_text("\n".join(lines), encoding="utf-8")
    return path


def summarize_checker_items(items: list[CoverItem], measurement_type: str) -> dict[str, Any]:
    """Full-union COI/mutation denominator, split by Jasper cover-item type."""

    def one(group: list[CoverItem]) -> dict[str, Any]:
        counts = Counter(item.status for item in group)
        checked = counts["covered_and_checked"]
        unchecked = counts["uncovered_or_unchecked"]
        excluded = counts["unreachable_or_undetectable"]
        unprocessed = counts["unprocessed"]
        total = len(group)
        effective = checked + unchecked
        return {
            "checked": checked,
            "unchecked": unchecked,
            "unreachable_or_undetectable": excluded,
            "unprocessed": unprocessed,
            "raw_denominator": total,
            "raw_coverage_percent": round(100 * checked / total, 2) if total else 0.0,
            "effective_denominator": effective,
            "effective_coverage_percent": round(100 * checked / effective, 2) if effective else 0.0,
        }

    types = ("statement", "branch", "expression", "toggle", "functional")
    summary = {kind: one([item for item in items if item.cover_item_type.lower() == kind]) for kind in types}
    summary["all"] = one(items)
    return {
        "measurement_type": measurement_type,
        "denominator_definition": (
            "raw = checked + unchecked + unreachable_or_undetectable + unprocessed; "
            "effective = checked + unchecked.  Values are one Jasper full-portfolio union, never summed per assertion."
        ),
        "by_cover_item_type": summary,
    }


def _run_checker_session(
    rtl_files: list[str], property_file: Path, top_module: str, output_dir: Path,
    formal_config: dict[str, Any], measurement_type: str, properties: list[Any],
    executor: Callable[..., Any] | None = None,
) -> dict[str, Any]:
    # Do not reuse a fixed items TSV: a failed rerun must never parse a
    # previous successful export as if it belonged to this session.
    session_dir = output_dir / "sessions" / f"session_{time.time_ns()}_{os.getpid()}"
    session_dir.mkdir(parents=True, exist_ok=False)
    tcl = generate_checker_coverage_tcl(rtl_files, str(property_file), top_module, session_dir, formal_config, measurement_type)
    executable = Path(formal_config["executable"]).resolve()
    project = session_dir / f"jgproject_{measurement_type}"
    command = [str(executable), "-allow_unsupported_OS", "-batch", "-proj", str(project), str(tcl)]
    env = os.environ.copy()
    if formal_config.get("license_file"):
        env[str(formal_config.get("license_env", "CDS_LIC_FILE"))] = str(formal_config["license_file"])
    start = time.monotonic()
    try:
        completed = (executor or subprocess.run)(
            command, cwd=session_dir, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=int(formal_config.get("timeout_seconds", 1800)), check=False,
        )
        return_code = int(completed.returncode)
        stdout, stderr = completed.stdout or "", completed.stderr or ""
    except subprocess.TimeoutExpired as exc:
        return_code = -1
        stdout, stderr = exc.stdout or "", exc.stderr or ""
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", errors="replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", errors="replace")
        stderr += "\nJasperGold checker coverage execution timed out"
    (session_dir / "jaspergold.stdout.log").write_text(stdout, encoding="utf-8", errors="replace")
    (session_dir / "jaspergold.stderr.log").write_text(stderr, encoding="utf-8", errors="replace")
    items_path = session_dir / f"{measurement_type}_items.tsv"
    export_audit: dict[str, Any] | None = None
    export_error: str | None = None
    if items_path.is_file():
        try:
            items, export_audit = parse_checker_coverage_items(items_path)
        except CheckerCoverageExportError as exc:
            # Preserve the raw session evidence and make the measurement
            # explicitly unavailable; never silently fabricate a denominator.
            items, export_error = [], str(exc)
    else:
        items = []
    proof_results, proof_summary, _proof_coverage = parse_jasper_results(
        properties, session_dir / "formal_report.txt", session_dir / "proof_core_report.txt",
        session_dir / f"{measurement_type}_coverage_report.txt", session_dir / "jaspergold.stdout.log",
    )
    preproof = {
        "property_results": [{"property_id": item.property_id, "result": item.result} for item in proof_results],
        "summary": proof_summary,
        "all_targets_proven": len(proof_results) == len(properties) and all(item.result == "PASS" for item in proof_results),
    }
    status = (
        "EXPORT_CONFLICT" if export_error
        else "COMPLETE" if return_code == 0 and items_path.is_file() and bool(items)
        else "EMPTY_ARTIFACT" if return_code == 0 and items_path.is_file()
        else "UNAVAILABLE_OR_FAILED"
    )
    result = {
        "measurement_type": measurement_type, "session_dir": str(session_dir), "tcl": str(tcl), "project": str(project),
        "return_code": return_code, "runtime_seconds": round(time.monotonic() - start, 3),
        "items_path": str(items_path), "report_path": str(session_dir / f"{measurement_type}_coverage_report.txt"),
        "status": status, "preproof": preproof, "export_audit": export_audit,
        "export_error": export_error,
        # A malformed/conflicting export is not a zero-denominator result.
        "summary": summarize_checker_items(items, measurement_type)
        if items_path.is_file() and not export_error else None,
    }
    dump_json(session_dir / f"{measurement_type}_measurement.json", result)
    return result


def run_final_measurements(
    target: dict[str, Any], cfg: dict[str, Any], initial_root: str | Path,
    feedback_root: str | Path, output_root: str | Path, *,
    executor: Callable[..., Any] | None = None,
) -> dict[str, Any]:
    """Run final COI and native mutation coverage in independent Jasper sessions."""

    initial_root, feedback_root, output_root = (Path(item).resolve() for item in (initial_root, feedback_root, output_root))
    assertions, properties_path, properties, feedback_summary = resolve_final_portfolio(feedback_root)
    # Parse source fresh; this ensures the exact original RTL paths/configuration
    # are used, without copying or modifying any prior proof-core session.
    rtl_inputs = [str(_resolve(item)) for item in target.get("rtl_files", [])]
    include_dirs = [str(_resolve(item)) for item in target.get("include_dirs", [])]
    design = parse_rtl(rtl_inputs, include_dirs=include_dirs)
    if not design.files:
        raise RuntimeError("no RTL files resolved for final checker coverage")
    formal_config = _formal_config(target, cfg)
    identity_audit = _validate_fresh_identity(
        feedback_root, feedback_summary, assertions, design, target, cfg, formal_config,
    )
    output_root.mkdir(parents=True, exist_ok=True)
    manifest = {
        "schema": SCHEMA, "design_id": target["design_id"], "top_module": target["top"],
        "initial_root": str(initial_root), "feedback_root": str(feedback_root),
        "exact_final_assertions": str(assertions), "assertions_sha256": _sha256(assertions),
        "exact_final_properties": str(properties_path), "property_ids": [item.property_id for item in properties],
        "rtl_files": design.files, "rtl_sha256": {str(Path(item)): _sha256(Path(item)) for item in design.files},
        "previous_effective_proof_core_reference": feedback_summary.get("final_effective_proof_core"),
        "portfolio_selection": {
            "status": feedback_summary.get("status", "COMPLETED_FEEDBACK"),
            "round": int(feedback_summary.get("final_portfolio_round", feedback_summary.get("rounds_completed", 0))),
            "user_authorized_finalization": feedback_summary.get("user_authorized_finalization"),
            "interpretation": (
                "User-authorized cutoff; this is an explicitly audited round selection, not a completed requested feedback run."
                if feedback_summary.get("status") == "USER_AUTHORIZED_CUTOFF"
                else "Completed feedback final portfolio."
            ),
        },
        "final_identity": identity_audit,
        "preservation": "This isolated measurement never overwrites feedback/initial proof-core coverage artifacts.",
    }
    dump_json(output_root / "final_measurements_manifest.json", manifest)
    coi = _run_checker_session(design.files, assertions, str(target["top"]), output_root / "coi", formal_config, "coi", properties, executor)
    native_mutation = _run_checker_session(design.files, assertions, str(target["top"]), output_root / "native_mutation", formal_config, "mutation", properties, executor)
    if not native_mutation["preproof"]["all_targets_proven"]:
        native_mutation["interpretation"] = (
            "INCOMPLETE: native mutation checker coverage is not interpreted as a final mutation metric because its own pre-proof did not prove every final assertion."
        )
    else:
        native_mutation["interpretation"] = "VALID: all final assertions were proven in the native-mutation session before measurement."
    # COI is the mandatory measurement.  An empty/failed export is never a
    # valid 0% observation; keep its diagnostics but make the run incomplete.
    manifest.update({
        "status": "COMPLETE" if coi["status"] == "COMPLETE" else "COI_INCOMPLETE",
        "coi": coi, "native_mutation": native_mutation,
    })
    dump_json(output_root / "final_measurements_manifest.json", manifest)
    native_valid = native_mutation["status"] == "COMPLETE" and native_mutation["preproof"]["all_targets_proven"]
    dump_json(output_root / "final_measurements_summary.json", {
        "design_id": target["design_id"], "status": manifest["status"],
        "coi_status": coi["status"],
        # Only a non-empty full-union COI is a reportable coverage metric.
        "coi": coi.get("summary") if coi["status"] == "COMPLETE" else None,
        "native_mutation": native_mutation.get("summary") if native_valid else None,
        "native_mutation_status": native_mutation["status"],
        "native_mutation_metric_valid": native_valid,
    })
    return manifest
