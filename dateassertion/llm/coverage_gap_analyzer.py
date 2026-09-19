"""Coverage-guided DeepSeek analysis with strict evidence and symbol validation."""

from __future__ import annotations

from pathlib import Path
import hashlib
import json
import re
from typing import Any

from dateassertion.ir.schema import PropertyIR, PropertySource, dump_json, load_json
from dateassertion.ontology.property_families import PropertyFamily
from dateassertion.rtl_frontend.parser import RTLDesign
from .client import DeepSeekClient


SYSTEM_FUNCTIONS = {"past", "stable", "rose", "fell", "changed", "signed", "unsigned", "onehot", "onehot0", "isunknown"}
DISALLOWED_SVA = re.compile(r"\|->|\|=>|##|\b(?:assert|assume|cover|disable)\b", re.I)


def _expression_names(expression: str) -> set[str]:
    cleaned = re.sub(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+", " ", expression)
    return {
        name for name in re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", cleaned)
        if name.lower() not in SYSTEM_FUNCTIONS and name.lower() not in {"true", "false"}
    }


def _rtl_symbols(design: RTLDesign) -> set[str]:
    result = set(design.signals)
    for file in design.files:
        text = Path(file).read_text(encoding="utf-8", errors="replace")
        result.update(re.findall(r"\b(?:localparam|parameter)\b(?:\s+\[[^]]+\])?\s+([A-Za-z_][A-Za-z0-9_$]*)", text))
        result.update(re.findall(r"\b([A-Za-z_][A-Za-z0-9_$]*)\s*=\s*(?:\d+)?'[bBoOdDhH][0-9a-fA-FxXzZ_]+", text))
    return result


def _symbol_values(design: RTLDesign) -> dict[str, str]:
    values: dict[str, str] = {}
    declaration = re.compile(
        r"\b(?:localparam|parameter)\b(?:\s+(?:signed|integer|logic|reg|wire))*"
        r"(?:\s*\[[^]]+\])?\s+([A-Za-z_][A-Za-z0-9_$]*)\s*=\s*([^,;\n]+)"
    )
    for file in design.files:
        text = Path(file).read_text(encoding="utf-8", errors="replace")
        for name, value in declaration.findall(text):
            values[name] = " ".join(value.split())
    return values


def _resolve_constants(expression: str, known_signals: set[str], values: dict[str, str]) -> str:
    result = expression
    for _ in range(4):
        changed = False
        for name in _expression_names(result) - known_signals:
            if name in values:
                result, count = re.subn(rf"\b{re.escape(name)}\b", f"({values[name]})", result)
                changed |= bool(count)
        if not changed:
            break
    return result


def _source_windows(region: dict[str, Any], radius: int = 3, limit: int = 50) -> list[dict[str, Any]]:
    by_file: dict[str, list[int]] = {}
    for item in region.get("uncovered_logic", [])[:80]:
        by_file.setdefault(item["file"], []).append(int(item["line_start"]))
    windows: list[dict[str, Any]] = []
    used = 0
    for file, raw_lines in by_file.items():
        source = Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
        pending = sorted(set(raw_lines))
        while pending and used < limit:
            anchor = pending.pop(0)
            start = max(1, anchor - radius)
            end = min(len(source), anchor + radius)
            while pending and pending[0] <= end + radius:
                end = min(len(source), pending.pop(0) + radius)
            if used + end - start + 1 > limit:
                end = start + max(0, limit - used - 1)
            numbered = "\n".join(f"{line_no}: {source[line_no - 1]}" for line_no in range(start, end + 1))
            windows.append({"file": file, "line_start": start, "line_end": end, "rtl": numbered})
            used += end - start + 1
    return windows


def _relevant_assignments(region: dict[str, Any], design: RTLDesign, limit: int = 25) -> list[dict[str, Any]]:
    signals = set(region.get("uncovered_signals", []))
    lines = set(region.get("uncovered_lines", []))
    result = []
    for assignment in design.assignments:
        if assignment.module != region.get("module"):
            continue
        if assignment.line in lines or assignment.lhs in signals or set(assignment.dependencies) & signals:
            result.append({
                "lhs": assignment.lhs,
                "rhs": assignment.rhs,
                "guard": assignment.guard,
                "file": assignment.file,
                "line": assignment.line,
                "kind": assignment.kind,
                "dependencies": assignment.dependencies,
            })
    return result[:limit]


def _normalise_contracts(
    raw: dict[str, Any],
    region: dict[str, Any],
    design: RTLDesign,
    min_confidence: float,
    observation_helpers: list[dict[str, Any]] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    accepted: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    allowed_families = set(region.get("missing_property_families", []))
    helpers = observation_helpers or []
    helper_names = {str(item.get("helper_id", "")) for item in helpers}
    symbols = _rtl_symbols(design) | helper_names
    known_signals = set(design.signals) | helper_names
    actual_signals = set(design.signals)
    symbol_values = _symbol_values(design)
    allowed_files = set(region.get("source_files", [])) | set(design.files)
    source_lines: dict[str, list[str]] = {
        file: Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
        for file in allowed_files if Path(file).is_file()
    }
    for index, proposal in enumerate(raw.get("property_gaps", []) if isinstance(raw.get("property_gaps"), list) else []):
        reasons: list[str] = []
        if not isinstance(proposal, dict):
            rejected.append({"proposal": proposal, "reasons": ["not an object"]})
            continue
        family = str(proposal.get("family", ""))
        antecedent = str(proposal.get("antecedent", "")).strip()
        consequent = str(proposal.get("consequent", "")).strip()
        temporal = str(proposal.get("temporal_relation", "")).upper()
        confidence = float(proposal.get("confidence", 0.0) or 0.0)
        if family not in allowed_families or family not in {item.value for item in PropertyFamily}:
            reasons.append("family is not an allowed missing family")
        if not antecedent or not consequent or DISALLOWED_SVA.search(antecedent + " " + consequent):
            reasons.append("expressions are empty or contain direct SVA/assume syntax")
        if temporal not in {"SAME_CYCLE", "NEXT_CYCLE"}:
            reasons.append("unsupported temporal_relation")
        if confidence < min_confidence:
            reasons.append("confidence below threshold")
        names = _expression_names(antecedent) | _expression_names(consequent)
        invented = names - symbols
        if invented:
            reasons.append(f"invented or unavailable RTL symbols: {sorted(invented)}")
        target_signals = set(region.get("hard_gap_target_signals", []))
        target_overlap = names & target_signals
        if target_signals and len(target_overlap) < min(2, len(target_signals)):
            reasons.append(
                f"contract touches only {sorted(target_overlap)}; hard-gap recovery requires at least two target-cone signals"
            )
        if re.sub(r"\s+", "", antecedent) == re.sub(r"\s+", "", consequent):
            reasons.append("tautological A implies A contract")
        expanded_antecedent = antecedent
        expanded_consequent = consequent
        for helper in helpers:
            helper_id = str(helper.get("helper_id", ""))
            helper_expression = str(helper.get("expression", ""))
            expanded_antecedent = re.sub(rf"\b{re.escape(helper_id)}\b", f"({helper_expression})", expanded_antecedent)
            expanded_consequent = re.sub(rf"\b{re.escape(helper_id)}\b", f"({helper_expression})", expanded_consequent)
        if re.sub(r"[\s()]", "", expanded_antecedent) == re.sub(r"[\s()]", "", expanded_consequent):
            reasons.append("tautological contract after expanding observation helpers")
        evidence = proposal.get("evidence", [])
        evidence_ok = False
        normalized_evidence = []
        all_evidence_signals: set[str] = set()
        nonblocking_evidence = False
        case_labels: list[str] = []
        assigned_lhs: set[str] = set()
        assigned_dependencies: dict[str, set[str]] = {}
        if isinstance(evidence, list):
            for entry in evidence:
                if not isinstance(entry, dict):
                    continue
                file = str(entry.get("file", ""))
                try:
                    line = int(entry.get("line", 0))
                except (TypeError, ValueError):
                    line = 0
                kind = str(entry.get("kind", "")).upper()
                lines = source_lines.get(file, [])
                text = lines[line - 1] if 1 <= line <= len(lines) else ""
                evidence_signals = _expression_names(text) & actual_signals
                assignment_match = re.search(
                    r"(?:^|\s)(?:assign\s+)?(?:wire\s+|logic\s+|reg\s+)?"
                    r"([A-Za-z_][A-Za-z0-9_$]*)(?:\s*\[[^]]+\])?\s*(<=|=)",
                    text,
                )
                case_match = re.match(
                    r"\s*([^:]+):\s*([A-Za-z_][A-Za-z0-9_$]*)"
                    r"(?:\s*\[[^]]+\])?\s*(<=|=)",
                    text,
                )
                kind_matches = (
                    (kind == "ASSIGNMENT" and bool(assignment_match) and not case_match)
                    or (kind == "CASE_BRANCH" and bool(case_match))
                    or (kind == "INLINE_ASSERTION" and bool(re.search(r"\bassert\b", text)))
                    or (kind == "CONDITION" and bool(re.search(r"\b(?:if|case)\s*\(", text)))
                    or kind == "SPEC"
                )
                if file in allowed_files and text and names & evidence_signals and kind_matches:
                    evidence_ok = True
                    all_evidence_signals.update(evidence_signals)
                    normalized_evidence.append({"file": file, "line": line, "kind": kind, "source": text.strip()})
                    match = case_match or assignment_match
                    if match:
                        lhs = match.group(2) if case_match else match.group(1)
                        assigned_lhs.add(lhs)
                        assigned_dependencies[lhs] = _expression_names(text[match.end():]) & actual_signals
                        operator = match.group(3) if case_match else match.group(2)
                        nonblocking_evidence |= operator == "<="
                    if case_match:
                        case_labels.append(case_match.group(1).strip())
        if not evidence_ok:
            reasons.append("no cited source line has the claimed evidence kind and supports a contract signal")
        antecedent_names = _expression_names(antecedent) & actual_signals
        consequent_names = _expression_names(consequent) & actual_signals
        if antecedent_names and not antecedent_names & all_evidence_signals:
            reasons.append("evidence does not support any antecedent signal")
        if consequent_names and not consequent_names & all_evidence_signals:
            reasons.append("evidence does not support any consequent signal")
        if re.search(r"!\s*(?:resetn|reset_n|rst_n)\b", antecedent, re.I):
            reasons.append("active-low reset antecedent conflicts with the checker's disable-iff policy")
        if nonblocking_evidence and temporal != "NEXT_CYCLE":
            reasons.append("nonblocking assignment evidence requires NEXT_CYCLE")
        for label in case_labels:
            if label != "default" and re.sub(r"\s+", "", label) not in re.sub(r"\s+", "", antecedent):
                reasons.append(f"antecedent does not select cited case label {label}")
        if len(assigned_lhs) > 1 and "&&" in consequent and assigned_lhs <= _expression_names(consequent):
            reasons.append("contract incorrectly conjoins outputs assigned by mutually exclusive branches")
        source_classification = str(proposal.get("source_classification", PropertySource.LLM_HYPOTHESIS.value)).upper()
        if source_classification not in {item.value for item in PropertySource}:
            source_classification = PropertySource.LLM_HYPOTHESIS.value
        if source_classification == PropertySource.SPEC_BACKED.value and not any(item["kind"] == "SPEC" for item in normalized_evidence):
            reasons.append("SPEC_BACKED proposal lacks SPEC evidence")
        if source_classification == PropertySource.RTL_STRUCTURAL.value:
            contract_signals = antecedent_names | consequent_names
            ignored_dependencies = {"reset", "resetn", "reset_n", "rst", "rst_n"}
            for lhs in sorted(consequent_names & assigned_lhs):
                skipped = assigned_dependencies.get(lhs, set()) - contract_signals - assigned_lhs - ignored_dependencies
                if skipped:
                    reasons.append(
                        f"RTL structural evidence for {lhs} skips intermediate dependencies: {sorted(skipped)}"
                    )
        evidence_blocks: set[tuple[str, int, int]] = set()
        for evidence_item in normalized_evidence:
            for block in design.always_blocks:
                if (
                    block.file == evidence_item["file"]
                    and block.module == region.get("module")
                    and block.line_start <= evidence_item["line"] <= block.line_end
                ):
                    evidence_blocks.add((block.file, block.line_start, block.line_end))
        if (
            source_classification == PropertySource.RTL_STRUCTURAL.value
            and temporal == "NEXT_CYCLE"
            and len(evidence_blocks) > 1
            and family != "CROSS_REGION_CAUSALITY"
        ):
            reasons.append(
                "one-cycle RTL_STRUCTURAL contract spans multiple always blocks without an evidenced intermediate event"
            )
        if reasons:
            rejected.append({"proposal": proposal, "reasons": reasons})
            continue
        accepted.append({
            "contract_id": f"{region['region_id']}_gap_{index + 1}",
            "coverage_region_id": region["region_id"],
            "region": region["region"],
            "module": region["module"],
            "anchor_region_id": (region.get("existing_region_ids") or [region["region_id"]])[0],
            "family": family,
            "reason": str(proposal.get("reason", "")),
            "antecedent": _resolve_constants(antecedent, known_signals, symbol_values),
            "consequent": _resolve_constants(consequent, known_signals, symbol_values),
            "temporal_relation": temporal,
            "signals": sorted(names & known_signals),
            "source_classification": source_classification,
            "confidence": confidence,
            "evidence": normalized_evidence,
            "cross_regions": [str(item) for item in proposal.get("cross_regions", []) if isinstance(item, str)],
            "observation_helpers": [item for item in helpers if item.get("helper_id") in names],
        })
    return accepted, rejected


class CoverageGapAnalyzer:
    def __init__(self, client: DeepSeekClient, prompt_path: str | Path):
        self.client = client
        self.system_prompt = Path(prompt_path).read_text(encoding="utf-8")

    def analyze(
        self,
        region: dict[str, Any],
        design: RTLDesign,
        properties: list[PropertyIR],
        proof_core: dict[str, Any],
        output_path: str | Path,
        min_confidence: float = 0.65,
        formal_context: dict[str, Any] | None = None,
    ) -> tuple[list[dict[str, Any]], dict[str, Any]]:
        assignments = _relevant_assignments(region, design)
        request = {
            "prompt_digest": hashlib.sha256(self.system_prompt.encode("utf-8")).hexdigest(),
            "validator_version": "rtl-evidence-v2",
            "region_id": region["region_id"],
            "region_type": region["region"],
            "module": region["module"],
            "proof_core": proof_core,
            "region_coverage": {key: region[key] for key in (
                "total_elements", "covered_elements", "reachable_uncovered_elements",
                "unreachable_or_undetectable_elements", "coverage_percent",
            )},
            "available_property_families": region.get("missing_property_families", [])[:5],
            "existing_properties": [
                {"property_id": prop.property_id, "family": prop.family, "body": prop.body, "signals": prop.signals}
                for prop in properties if prop.property_id in region.get("existing_properties", [])
            ],
            "uncovered_logic": [
                {**item, "expression": str(item.get("expression", ""))[:240]}
                for item in region.get("uncovered_logic", [])[:8]
            ],
            "local_rtl": _source_windows(region),
            "structural_assignments": assignments,
            "previous_formal_results": (formal_context or {}).get("previous_formal_results", []),
            "previous_coverage_gain": (formal_context or {}).get("previous_coverage_gain"),
            "region_history": (formal_context or {}).get("region_history", []),
            "candidate_limit": int((formal_context or {}).get("candidate_limit", 3)),
        }
        cached_path = Path(output_path)
        if cached_path.is_file():
            cached = load_json(cached_path)
            if (
                cached.get("status") == "ok"
                and isinstance(cached.get("accepted"), list)
                and cached.get("request") == request
            ):
                return cached["accepted"], cached
        record: dict[str, Any] = {"request": request}
        dump_json(output_path, {**record, "status": "request_prepared"})
        try:
            raw, metadata = self.client.complete_json(self.system_prompt, json.dumps(request, ensure_ascii=False))
            if str(raw.get("region_id", "")) != region["region_id"]:
                raise ValueError("LLM changed region_id")
            accepted, rejected = _normalise_contracts(raw, region, design, min_confidence)
            record.update({"status": "ok", "response": raw, "accepted": accepted, "rejected": rejected, "metadata": metadata})
        except Exception as exc:
            accepted = []
            record.update({"status": "safe_failure", "error": str(exc), "accepted": [], "rejected": []})
        dump_json(output_path, record)
        return accepted, record
