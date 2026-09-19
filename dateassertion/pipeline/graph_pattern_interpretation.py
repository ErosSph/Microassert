"""Bounded LLM interpretation for ambiguous graph-pattern candidates."""

from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path
from typing import Any

from dateassertion.ir.schema import dump_json
from dateassertion.llm.client import DeepSeekClient
from dateassertion.pipeline.semantic_slicing import expand_region_context


ALLOWED = {
    "FSM", "DECODE", "HANDSHAKE", "REQUEST_RESPONSE", "PIPELINE",
    "REGISTER_UPDATE", "DATAPATH", "UNKNOWN",
}


class PatternInterpretationError(ValueError):
    pass


def package_ambiguous_pattern(region: dict[str, Any], attempt: int) -> dict[str, Any]:
    nodes = []
    for item in region.get("coi", {}).get("nodes", []):
        if item.get("kind") == "signal":
            nodes.append({key: item.get(key) for key in (
                "id", "kind", "module", "name", "width", "direction", "signal_kind",
            )})
        elif item.get("kind") == "assignment":
            nodes.append({key: item.get(key) for key in (
                "id", "kind", "module", "lhs", "rhs", "guard", "timing", "clock", "reset", "source",
            )})
    return {
        "schema": "region_flow.4-ambiguous-pattern-context.v1",
        "region_id": region["region_id"],
        "attempt": attempt,
        "candidate_kind": region["kind"],
        "pattern_scores": region.get("pattern_scores", {}),
        "matched_features": region.get("matched_features", []),
        "core_node_ids": region.get("core_node_ids", []),
        "local_nodes": nodes[:96],
        "typed_directed_edges": region.get("coi", {}).get("edges", [])[:160],
        "traversal_policy": region.get("coi", {}).get("policy", {}),
        "rtl_context": region.get("coi", {}).get("rtl_context", [])[:6],
        "boundary": {
            "imported_signals": region.get("boundary", {}).get("imported_signals", []),
            "exported_signals": region.get("boundary", {}).get("exported_signals", []),
            "semantic_cut_edges": region.get("boundary", {}).get("semantic_cut_edges", [])[:80],
            "unresolved_dependencies": region.get("boundary", {}).get("unresolved_dependencies", []),
        },
    }


def validate_interpretation(response: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    if not isinstance(response, dict) or response.get("region_id") != context["region_id"]:
        raise PatternInterpretationError("response region_id does not match supplied candidate")
    status = str(response.get("status", "")).upper()
    classification = str(response.get("classification", "UNKNOWN")).upper()
    if status not in {"CLASSIFIED", "UNKNOWN", "NEED_CONTEXT"}:
        raise PatternInterpretationError("invalid status")
    if classification not in ALLOWED:
        raise PatternInterpretationError("invalid classification")
    known_nodes = {item.get("id") for item in context.get("local_nodes", [])}
    evidence_nodes = response.get("evidence_nodes", [])
    if not isinstance(evidence_nodes, list) or any(item not in known_nodes for item in evidence_nodes):
        raise PatternInterpretationError("evidence_nodes must be supplied local node ids")
    signal_aliases: dict[str, str] = {}
    def add_signal_alias(value: Any) -> None:
        node_id = str(value or "")
        if not node_id.startswith("signal:") or "." not in node_id:
            return
        qualified = node_id[len("signal:"):]
        bare = qualified.split(".", 1)[1]
        signal_aliases[node_id] = bare
        signal_aliases[qualified] = bare
        signal_aliases[bare] = bare

    for item in context.get("local_nodes", []):
        if item.get("kind") != "signal" or not item.get("name"):
            continue
        signal_aliases[str(item["name"])] = str(item["name"])
        signal_aliases[str(item.get("id", ""))] = str(item["name"])
        add_signal_alias(item.get("id"))
    for edge in context.get("typed_directed_edges", []):
        add_signal_alias(edge.get("source"))
        add_signal_alias(edge.get("target"))
    for edge in context.get("boundary", {}).get("semantic_cut_edges", []):
        add_signal_alias(edge.get("source"))
        add_signal_alias(edge.get("target"))
    for item in context.get("boundary", {}).get("imported_signals", []):
        signal_aliases[str(item)] = str(item)
    for item in context.get("boundary", {}).get("exported_signals", []):
        signal_aliases[str(item)] = str(item)
    needs = response.get("needs_context", [])
    if not isinstance(needs, list):
        raise PatternInterpretationError("needs_context must be a list")
    if any(not isinstance(item, dict) or item.get("signal") not in signal_aliases or not item.get("reason") for item in needs):
        raise PatternInterpretationError("NEED_CONTEXT may request only supplied signals with a reason")
    normalized_needs = [
        {**item, "signal": signal_aliases[str(item["signal"])]} for item in needs
    ]
    if status == "CLASSIFIED":
        if classification == "UNKNOWN" or not evidence_nodes or needs:
            raise PatternInterpretationError("CLASSIFIED requires evidence and no context request")
    elif status == "UNKNOWN":
        if classification != "UNKNOWN" or needs:
            raise PatternInterpretationError("UNKNOWN must not speculate or request context")
    else:
        if classification != "UNKNOWN" or not needs:
            raise PatternInterpretationError("NEED_CONTEXT requires one or more requests")
    confidence = float(response.get("confidence", 0.0))
    if not 0.0 <= confidence <= 1.0:
        raise PatternInterpretationError("confidence must be within [0,1]")
    return {
        "region_id": context["region_id"], "status": status,
        "classification": classification, "confidence": confidence,
        "rationale": str(response.get("rationale", "")),
        "evidence_nodes": list(evidence_nodes), "needs_context": normalized_needs,
    }


def resolve_ambiguous_regions(
    regions_doc: dict[str, Any], graph: dict[str, Any], design_map: dict[str, Any],
    client: DeepSeekClient, prompt: str, *, limit: int = 4, max_attempts: int = 2,
    artifact_dir: str | Path | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Interpret only ambiguous regions; deterministic MATCH facts are immutable."""
    result = deepcopy(regions_doc)
    selected = [
        item for item in result.get("regions", [])
        if item.get("detection_status") == "AMBIGUOUS"
    ][:limit]
    calls = []
    expansions = 0
    classified = 0
    unknown = 0
    output = Path(artifact_dir) if artifact_dir else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    for region in selected:
        current = region
        final: dict[str, Any] | None = None
        validation_error = ""
        for attempt in range(1, max_attempts + 1):
            context = package_ambiguous_pattern(current, attempt)
            response: dict[str, Any] = {}
            metadata: dict[str, Any] = {}
            payload: dict[str, Any] = context
            if validation_error:
                payload = {
                    "context": context,
                    "previous_validation_error": validation_error,
                    "instruction": "Return corrected JSON using only signals and node ids present in context.",
                }
            try:
                response, metadata = client.complete_json(prompt, json.dumps(payload, ensure_ascii=False))
                validated = validate_interpretation(response, context)
            except Exception as exc:
                validation_error = str(exc)
                record = {
                    "region_id": region["region_id"], "attempt": attempt,
                    "context": context, "response": response,
                    "validation_error": validation_error,
                    "metadata": {
                        key: value for key, value in metadata.items()
                        if key != "raw_content"
                    },
                }
                calls.append(record)
                if output:
                    dump_json(output / f"{region['region_id']}_attempt{attempt}.json", record)
                continue
            record = {
                "region_id": region["region_id"], "attempt": attempt,
                "context": context, "response": validated,
                "metadata": {key: value for key, value in metadata.items() if key != "raw_content"},
            }
            calls.append(record)
            if output:
                dump_json(output / f"{region['region_id']}_attempt{attempt}.json", record)
            if validated["status"] == "NEED_CONTEXT" and attempt < max_attempts:
                current = expand_region_context(
                    current, graph, design_map,
                    [item["signal"] for item in validated["needs_context"]],
                )
                expansions += 1
                validation_error = ""
                continue
            final = validated
            break
        if final is None or final["status"] == "NEED_CONTEXT":
            region["detection_status"] = "LLM_UNRESOLVED"
            unknown += 1
        elif final["status"] == "UNKNOWN":
            region["detection_status"] = "LLM_UNKNOWN"
            unknown += 1
        else:
            region["kind"] = final["classification"]
            region["detection_status"] = "LLM_VALIDATED"
            region["llm_interpretation"] = final
            region["coi"] = current["coi"]
            region["boundary"] = current["boundary"]
            region["signals"] = current["signals"]
            if current.get("context_expansion"):
                region["context_expansion"] = current["context_expansion"]
            classified += 1
    result["ambiguity_interpretation"] = {
        "selected": len(selected), "classified": classified, "unknown_or_unresolved": unknown,
        "context_expansions": expansions, "deterministic_match_regions_sent_to_llm": 0,
        "calls": calls,
    }
    result["summary"]["llm_validated_regions"] = classified
    result["summary"]["llm_unknown_or_unresolved_regions"] = unknown
    return result, result["ambiguity_interpretation"]
