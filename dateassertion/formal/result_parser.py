"""Parse JasperGold reports into strict and budget-accepted outcomes.

Req9 uses a 300-second engineering acceptance rule: an elaborated target that
JasperGold leaves undetermined/unprocessed at the proof time limit is reported
as ``TIMEOUT_ACCEPTED`` instead of the ambiguous ``UNKNOWN`` label.  This is
deliberately distinct from ``PASS`` so the strict Trusted gate can continue to
require an actual proof and non-vacuity evidence.
"""

from __future__ import annotations

from pathlib import Path
import re
from collections import defaultdict
from typing import Any

from dateassertion.ir.schema import FormalPropertyResult, PropertyIR


def _normalize_status(value: str) -> str:
    lowered = value.lower()
    if "proven" in lowered or lowered == "pass":
        return "PASS"
    if "cex" in lowered or "fail" in lowered or "falsified" in lowered:
        return "FAIL"
    if "error" in lowered:
        return "ERROR"
    if any(token in lowered for token in ("undetermined", "unknown", "unprocessed")):
        return "TIMEOUT_ACCEPTED"
    return "NOT_EVALUATED"


def _has_trivial_true_antecedent(body: str) -> bool:
    """Identify an implication whose antecedent is unconditionally true.

    JasperGold does not emit a ``:precondition`` cover target for
    ``1'b1 |-> ...``.  In this narrow case absence means "not applicable",
    rather than unknown vacuity.
    """

    compact = re.sub(r"\s+", "", body)
    return bool(re.match(r"^\(*1'b1\)*\|[-=]>", compact))


def parse_jasper_results(
    properties: list[PropertyIR],
    formal_report: str | Path,
    proof_core_report: str | Path,
    coverage_report: str | Path,
    log_path: str | Path,
) -> tuple[list[FormalPropertyResult], dict[str, Any], dict[str, Any]]:
    formal_text = Path(formal_report).read_text(encoding="utf-8", errors="replace") if Path(formal_report).is_file() else ""
    core_text = Path(proof_core_report).read_text(encoding="utf-8", errors="replace") if Path(proof_core_report).is_file() else ""
    coverage_text = Path(coverage_report).read_text(encoding="utf-8", errors="replace") if Path(coverage_report).is_file() else ""
    log_text = Path(log_path).read_text(encoding="utf-8", errors="replace") if Path(log_path).is_file() else ""
    searchable = "\n".join((formal_text, core_text, log_text))

    formal_targets: dict[str, list[dict[str, Any]]] = defaultdict(list)
    formal_preconditions: dict[str, list[str]] = defaultdict(list)
    precondition_pattern = re.compile(r"^(.*):precondition\d+$", re.I)
    for line in formal_text.splitlines():
        fields = line.split()
        if len(fields) < 4 or not re.fullmatch(r"\[\d+\]", fields[0]):
            continue
        target, tool_status = fields[1:3]
        if tool_status.lower() not in {
            "proven", "cex", "falsified", "undetermined", "unknown",
            "unprocessed", "error", "covered", "unreachable",
        }:
            continue
        try:
            seconds_index = len(fields) - 1 - fields[::-1].index("s")
            runtime = float(fields[seconds_index - 1])
        except (ValueError, IndexError):
            runtime = 0.0
        suffix = target.rsplit(".", 1)[-1]
        precondition = precondition_pattern.match(suffix)
        if precondition:
            formal_preconditions[precondition.group(1)].append(tool_status.lower())
            continue
        formal_targets[suffix].append({
            "target": target,
            "result": _normalize_status(tool_status),
            "tool_status": tool_status.lower(),
            "runtime_seconds": runtime,
        })

    core_targets: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for match in re.finditer(
        r"Name:\s*([^\n]+)\s*\nProve status:\s*([^\n]+)\s*\nPROOF_CORE:\s*(-?\d+)",
        core_text, re.I,
    ):
        target, tool_status, core_value = match.groups()
        suffix = target.strip().rsplit(".", 1)[-1]
        core_targets[suffix].append({
            "target": target.strip(),
            "result": _normalize_status(tool_status.strip()),
            "tool_status": tool_status.strip().lower(),
            "proof_core_items": int(core_value),
        })

    results: list[FormalPropertyResult] = []
    for prop in properties:
        label = "p_" + re.sub(r"[^A-Za-z0-9_$]", "_", prop.property_id)
        status = "NOT_EVALUATED"
        core_items = None
        runtime_seconds = None
        vacuity = None
        core_matches = core_targets.get(label, [])
        if core_matches:
            status = core_matches[0]["result"]
            value = core_matches[0]["proof_core_items"]
            core_items = value if value >= 0 else None
        target_results = list(formal_targets.get(label, []))
        target_counts = {
            name: sum(item["result"] == name for item in target_results)
            for name in ("PASS", "FAIL", "TIMEOUT_ACCEPTED", "ERROR", "NOT_EVALUATED")
        }
        if target_results:
            # A source Property is trusted only if every elaborated target is
            # Proven.  This prevents a shared module checker from inheriting
            # the first matching instance's result.
            if target_counts["FAIL"]:
                status = "FAIL"
            elif target_counts["ERROR"]:
                status = "ERROR"
            elif target_counts["PASS"] == len(target_results):
                status = "PASS"
            elif target_counts["TIMEOUT_ACCEPTED"] and (
                target_counts["PASS"] + target_counts["TIMEOUT_ACCEPTED"]
                == len(target_results)
            ):
                status = "TIMEOUT_ACCEPTED"
            else:
                status = "NOT_EVALUATED"
            runtime_seconds = round(sum(item["runtime_seconds"] for item in target_results), 6)

        preconditions = formal_preconditions.get(label, [])
        target_vacuity = {
            "NON_VACUOUS": sum(value.lower() == "covered" for value in preconditions),
            "VACUOUS": sum(value.lower() == "unreachable" for value in preconditions),
            "NOT_EVALUATED": sum(value.lower() not in {"covered", "unreachable"} for value in preconditions),
        }
        if target_vacuity["VACUOUS"]:
            vacuity = "VACUOUS"
        elif preconditions and target_vacuity["NON_VACUOUS"] == len(preconditions):
            vacuity = "NON_VACUOUS"
        elif preconditions:
            vacuity = "NOT_EVALUATED"
        elif status == "PASS" and _has_trivial_true_antecedent(prop.body):
            vacuity = "NON_VACUOUS"
            target_vacuity["NON_VACUOUS"] = max(1, len(target_results))
        results.append(
            FormalPropertyResult(
                property_id=prop.property_id,
                result=status,
                runtime_seconds=runtime_seconds,
                proof_core_items=core_items,
                vacuity=vacuity,
                classification=(
                    "PROVEN_NONVACUOUS" if status == "PASS" and vacuity == "NON_VACUOUS" else
                    "PROVEN_VACUOUS" if status == "PASS" and vacuity == "VACUOUS" else
                    "PROVEN_VACUITY_UNKNOWN" if status == "PASS" else
                    "CEX" if status == "FAIL" else status
                ),
                source_classification=prop.source_classification,
                review_status="NEEDS_REVIEW" if status == "FAIL" and prop.source_classification == "LLM_HYPOTHESIS" else "NONE",
                target_count=len(target_results),
                target_summary=target_counts,
                target_results=target_results,
                target_vacuity_summary=target_vacuity,
            )
        )

    counts = {
        name: sum(item.result == name for item in results)
        for name in ("PASS", "FAIL", "TIMEOUT_ACCEPTED", "ERROR", "NOT_EVALUATED")
    }
    total = len(results)
    accepted_correct = counts["PASS"] + counts["TIMEOUT_ACCEPTED"]
    summary = {
        "total": total,
        "proven": counts["PASS"],
        "failed": counts["FAIL"],
        "timeout_accepted": counts["TIMEOUT_ACCEPTED"],
        "not_evaluated": counts["NOT_EVALUATED"],
        "errors": counts["ERROR"],
        "accepted_correct": accepted_correct,
        "accepted_correct_rate": round(100.0 * accepted_correct / total, 2) if total else 0.0,
        "proven_rate": round(100.0 * counts["PASS"] / total, 2) if total else 0.0,
        "vacuous": sum(item.vacuity == "VACUOUS" for item in results),
        "non_vacuous": sum(item.vacuity == "NON_VACUOUS" for item in results),
        "elaborated_targets": sum(item.target_count for item in results),
        "elaborated_targets_proven": sum(item.target_summary.get("PASS", 0) for item in results),
        "elaborated_targets_failed": sum(item.target_summary.get("FAIL", 0) for item in results),
        "elaborated_targets_timeout_accepted": sum(
            item.target_summary.get("TIMEOUT_ACCEPTED", 0) for item in results
        ),
        "elaborated_targets_not_evaluated": sum(
            item.target_summary.get("NOT_EVALUATED", 0) for item in results
        ),
    }

    coverage: dict[str, Any] = {}
    top_line = re.search(r"^\|?\s*([A-Za-z_][\w$]*)\s*\|\s*([0-9.]+)%\s*\((\d+)/(\d+)\)", coverage_text, re.M)
    if top_line:
        coverage = {
            "instance": top_line.group(1),
            "proof_core_coverage_percent": float(top_line.group(2)),
            "covered_items": int(top_line.group(3)),
            "total_items": int(top_line.group(4)),
        }
    multi_core = re.search(r"Multi Target PROOF_CORE:\s*(-?\d+)", core_text, re.I)
    if multi_core:
        coverage["multi_target_proof_core_items"] = int(multi_core.group(1))
    return results, summary, coverage
