"""Candidate-at-a-time LLM analysis with validation and UNKNOWN fallback."""

from __future__ import annotations

from pathlib import Path
from typing import Any
import json

from dateassertion.ir.schema import MicroarchitectureIR, ObjectType, RegionIR, VerificationRegion, dump_json
from dateassertion.ir.validation import ValidationError, validate_region_ir
from .client import DeepSeekClient


def _null_sentinels(value: Any) -> Any:
    """Normalize prose placeholders before they can reach deterministic SVA."""
    if isinstance(value, str) and value.strip().lower() in {"none", "null", "n/a", "na", "unknown", "unsupported"}:
        return None
    if isinstance(value, list):
        return [_null_sentinels(item) for item in value]
    if isinstance(value, dict):
        return {key: _null_sentinels(item) for key, item in value.items()}
    return value


def _unknown(candidate: VerificationRegion, reason: str) -> RegionIR:
    return RegionIR(
        region_id=candidate.region_id,
        type=ObjectType.UNKNOWN,
        name=candidate.region_id,
        module=candidate.module,
        signals={},
        events={},
        attributes={},
        evidence=candidate.evidence,
        confidence=0.0,
        analysis_source="fallback",
        details={},
        notes=[reason],
    )


def _read_specs(paths: list[str]) -> str:
    chunks = []
    for value in paths:
        path = Path(value)
        if path.is_file():
            chunks.append(f"SOURCE: {path}\n{path.read_text(encoding='utf-8', errors='replace')[:12000]}")
    return "\n\n".join(chunks)


def _normalize(candidate: VerificationRegion, raw: dict[str, Any]) -> RegionIR:
    raw = _null_sentinels(raw)
    classification = str(raw.get("classification", "CORE_OBJECT")).upper()
    if classification == "NEW_OBJECT_CANDIDATE":
        object_type = ObjectType.EXTENSION
    else:
        object_type = ObjectType(str(raw.get("object_type", raw.get("type", "UNKNOWN"))).upper())
    details = dict(candidate.metadata)
    if isinstance(raw.get("details"), dict):
        # LLM fields take precedence except for deterministic state literals,
        # which are the source-location-backed representation used by SVA.
        details.update(raw["details"])
        if candidate.metadata.get("states"):
            details["states"] = candidate.metadata["states"]
        if candidate.metadata.get("transfers"):
            details["transfers"] = candidate.metadata["transfers"]
    events = dict(candidate.metadata.get("events", {}))
    if isinstance(raw.get("events"), dict):
        events.update({str(k): v for k, v in raw["events"].items()})
    if classification == "NEW_OBJECT_CANDIDATE":
        payload = {
            key: raw.get(key)
            for key in (
                "candidate_name", "reason", "signals", "state", "events", "inputs", "outputs",
                "dependencies", "invariants", "update_rules", "hold_rules", "ordering",
                "causality", "stability", "data_integrity", "mutual_exclusion",
                "reset_behavior", "assumptions", "related_regions",
                "new_property_family_candidates",
            )
            if key in raw
        }
        details["extension_candidate"] = payload
        raw_signals = raw.get("signals", [])
        signals = raw_signals if isinstance(raw_signals, dict) else {"related": raw_signals if isinstance(raw_signals, list) else []}
        for role in ("state", "inputs", "outputs"):
            if role in raw:
                signals[role] = raw[role]
    else:
        signals = raw.get("signals", {}) if isinstance(raw.get("signals"), dict) else {}
    notes = raw.get("notes", [])
    if isinstance(notes, str):
        notes = [notes]
    return RegionIR(
        region_id=str(raw.get("region_id", "")),
        type=object_type,
        name=str(raw.get("candidate_name") or raw.get("name") or candidate.region_id),
        module=candidate.module,
        signals=signals,
        events=events,
        attributes=raw.get("attributes", {}) if isinstance(raw.get("attributes"), dict) else {},
        evidence=candidate.evidence,
        confidence=float(raw.get("confidence", 0.0)),
        analysis_source="deepseek",
        details=details,
        notes=[str(item) for item in notes],
        ontology_classification=classification,
        extension_type=(str(raw.get("candidate_name")) if classification == "NEW_OBJECT_CANDIDATE" else None),
    )


class MicroarchitectureAnalyzer:
    def __init__(self, client: DeepSeekClient, prompt_path: str | Path):
        self.client = client
        self.system_prompt = Path(prompt_path).read_text(encoding="utf-8")

    def analyze(
        self,
        candidates: list[VerificationRegion],
        known_signals: set[str],
        design: str,
        top: str,
        output_dir: str | Path,
    ) -> MicroarchitectureIR:
        llm_dir = Path(output_dir) / "llm"
        llm_dir.mkdir(parents=True, exist_ok=True)
        regions: list[RegionIR] = []
        for candidate in candidates:
            request = {
                "region_id": candidate.region_id,
                "deterministic_hint": candidate.suggested_type.value,
                "module": candidate.module,
                "available_signals": candidate.signals,
                "dependency_summary": candidate.dependencies,
                "structural_metadata": candidate.metadata,
                "rtl_evidence": {
                    "file": candidate.evidence.rtl_files,
                    "lines": [candidate.evidence.line_start, candidate.evidence.line_end],
                    "snippet": candidate.evidence.snippet,
                },
                "correctness_sources": _read_specs(candidate.evidence.correctness_sources),
            }
            record: dict[str, Any] = {"request": request}
            raw: dict[str, Any] | None = None
            metadata: dict[str, Any] = {}
            try:
                raw, metadata = self.client.complete_json(self.system_prompt, json.dumps(request, ensure_ascii=False))
                region = _normalize(candidate, raw)
                validate_region_ir(region, candidate, known_signals)
                record.update({"status": "ok", "response": raw, "metadata": metadata})
            except (Exception, ValidationError) as exc:
                region = _unknown(candidate, f"LLM analysis failed safely: {exc}")
                record.update({
                    "status": "fallback_unknown",
                    "error": str(exc),
                    "response": raw,
                    "metadata": metadata,
                })
            dump_json(llm_dir / f"{candidate.region_id}.json", record)
            regions.append(region)
        return MicroarchitectureIR(
            design=design,
            top_module=top,
            regions=regions,
            rtl_files=sorted({file for candidate in candidates for file in candidate.evidence.rtl_files}),
        )
