"""Persistent, evidence-backed registry for discovered ontology extensions."""

from __future__ import annotations

from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import ContractIR, dump_json, load_json


REGISTRY_SCHEMA = "extension-registry.v1"


def _normalized_name(value: str) -> str:
    return re.sub(r"[^A-Z0-9]+", "_", value.upper()).strip("_") or "UNNAMED_EXTENSION"


def _semantics(contract: ContractIR) -> dict[str, Any]:
    return {
        "stateful": bool(contract.state),
        "event_roles": sorted(contract.events),
        "input_count": len(contract.inputs),
        "output_count": len(contract.outputs),
        "primitives": sorted(contract.reused_primitives),
    }


def _signal_support(contract: ContractIR) -> list[str]:
    signals = list(contract.state) + list(contract.inputs) + list(contract.outputs)
    def collect(value: Any) -> None:
        if isinstance(value, str):
            signals.extend(re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", value))
        elif isinstance(value, list):
            for item in value:
                collect(item)
        elif isinstance(value, dict):
            for item in value.values():
                collect(item)
    collect(contract.events)
    ignored = {"true", "false", "past", "stable"}
    return list(dict.fromkeys(signal for signal in signals if isinstance(signal, str) and signal not in ignored))


def update_extension_registry(
    registry_path: str | Path,
    contracts: list[ContractIR],
    source_design: str,
) -> dict[str, Any]:
    path = Path(registry_path)
    raw = load_json(path) if path.is_file() else {"schema": REGISTRY_SCHEMA, "entries": []}
    if raw.get("schema") != REGISTRY_SCHEMA or not isinstance(raw.get("entries"), list):
        raise ValueError(f"unsupported extension registry: {path}")
    entries: list[dict[str, Any]] = raw["entries"]
    for contract in contracts:
        if contract.ontology_classification != "NEW_OBJECT_CANDIDATE":
            continue
        name = _normalized_name(contract.object_type)
        entry = next((item for item in entries if item.get("candidate_name") == name), None)
        if entry is None:
            entry = {
                "candidate_name": name,
                "normalized_semantics": _semantics(contract),
                "occurrences": [],
                "source_designs": [],
                "source_regions": [],
                "supporting_signals": [],
                "reused_primitives": [],
                "formal_status": "NOT_RUN",
                "occurrence_count": 0,
                "similar_candidates": [],
                "promotion_candidate": False,
            }
            entries.append(entry)
        key = (source_design, contract.region)
        existing = {(item.get("source_design"), item.get("source_region")) for item in entry["occurrences"]}
        if key not in existing:
            entry["occurrences"].append({
                "source_design": source_design,
                "source_region": contract.region,
                "module": contract.module,
                "evidence": contract.evidence,
            })
        entry["source_designs"] = sorted({item["source_design"] for item in entry["occurrences"]})
        entry["source_regions"] = sorted({item["source_region"] for item in entry["occurrences"]})
        prior_signals = {
            token for value in entry.get("supporting_signals", [])
            for token in re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", str(value))
        }
        entry["supporting_signals"] = sorted(prior_signals | set(_signal_support(contract)))
        entry["reused_primitives"] = sorted(set(entry.get("reused_primitives", [])) | set(contract.reused_primitives))
        entry["occurrence_count"] = len(entry["occurrences"])
        # Promotion requires independent design support, not repeated runs.
        entry["promotion_candidate"] = len(entry["source_designs"]) >= 2

    for entry in entries:
        primitives = set(entry.get("reused_primitives", []))
        similar = []
        for other in entries:
            if other is entry:
                continue
            other_primitives = set(other.get("reused_primitives", []))
            if primitives and other_primitives and primitives & other_primitives:
                similar.append(other["candidate_name"])
        entry["similar_candidates"] = sorted(similar)
    entries.sort(key=lambda item: item["candidate_name"])
    dump_json(path, raw)
    return raw


def apply_formal_status(registry: dict[str, Any], properties: list[Any], formal_results: list[Any]) -> None:
    result_by_id = {item.property_id: item.result for item in formal_results}
    by_name: dict[str, list[str]] = {}
    for prop in properties:
        if prop.object_type.value != "EXTENSION":
            continue
        # Region is sufficient because registry occurrence records retain it.
        by_name.setdefault(prop.region_id, []).append(result_by_id.get(prop.property_id, "UNKNOWN"))
    for entry in registry.get("entries", []):
        statuses = [status for occurrence in entry.get("occurrences", []) for status in by_name.get(occurrence.get("source_region"), [])]
        if statuses:
            entry["formal_status"] = "PROVEN" if all(status == "PASS" for status in statuses) else ("CEX" if any(status == "FAIL" for status in statuses) else "UNKNOWN")
            entry["formal_summary"] = {
                "total": len(statuses),
                "proven": sum(status == "PASS" for status in statuses),
                "cex": sum(status == "FAIL" for status in statuses),
                "unknown": sum(status not in {"PASS", "FAIL"} for status in statuses),
            }
