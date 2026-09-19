"""Bounded LLM fallback for Req8.5 functional-path meaning ambiguity."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from dateassertion.ir.schema import dump_json


def _validate(response: dict[str, Any], context: dict[str, Any]) -> dict[str, Any]:
    path_id = context["path_id"]
    regions = set(context["regions"])
    if response.get("path_id") != path_id:
        raise ValueError("functional path response changed path_id")
    status = response.get("status")
    if status not in {"CLASSIFIED", "UNKNOWN", "NEED_CONTEXT"}:
        raise ValueError("invalid functional path semantic status")
    evidence = response.get("evidence_region_ids", [])
    if not isinstance(evidence, list) or not set(evidence) <= regions:
        raise ValueError("functional path response invented evidence region")
    roles = response.get("region_roles", [])
    if not isinstance(roles, list) or any(item.get("region_id") not in regions for item in roles):
        raise ValueError("functional path response invented role region")
    if status == "CLASSIFIED":
        if {item.get("region_id") for item in roles} != regions:
            raise ValueError("CLASSIFIED response must assign every supplied region")
        if not response.get("function_context") or response.get("function_context") == "UNKNOWN":
            raise ValueError("CLASSIFIED response lacks functional context")
    if status == "NEED_CONTEXT":
        requests = response.get("needs_context", [])
        if not requests or any(item.get("region_id") not in regions for item in requests):
            raise ValueError("NEED_CONTEXT requested an unsupplied region")
    return response


def resolve_path_meanings(
    validated_doc: dict[str, Any], region_graph: dict[str, Any], client: Any,
    prompt: str, *, limit: int = 2, artifact_dir: str | Path | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Let an LLM explain ambiguity, never validate dynamic relations."""

    output = Path(artifact_dir) if artifact_dir else None
    if output:
        output.mkdir(parents=True, exist_ok=True)
    node_by_id = {item["region_id"]: item for item in region_graph["nodes"]}
    selected = validated_doc.get("paths", [])[:limit]
    calls = []
    classified = 0
    unresolved = 0
    cached_calls = 0
    for path in selected:
        context = {
            "path_id": path["path_id"],
            "regions": path["regions"],
            "region_records": [
                {
                    "region_id": region_id,
                    "kind": node_by_id[region_id]["kind"],
                    "activation": node_by_id[region_id]["activation"],
                    "evidence": node_by_id[region_id]["evidence"],
                }
                for region_id in path["regions"]
            ],
            "region_edges": path["static_evidence"],
            "formal_validation": {
                "status": path["validation_status"],
                "formal_confidence": path["formal_confidence"],
                "reachability_query_ids": path["reachability_results"],
                "ordering_query_ids": path["ordering_results"],
                "dominance_query_ids": path["dominance_results"],
            },
            "prohibited_decisions": ["reachability", "ordering", "dominance", "exclusivity", "path membership"],
        }
        artifact_path = output / f"{path['path_id']}.json" if output else None
        cached = None
        if artifact_path and artifact_path.is_file():
            try:
                candidate = json.loads(artifact_path.read_text(encoding="utf-8"))
                cached_response = _validate(candidate["response"], context)
                cached = (cached_response, candidate.get("metadata", {}))
            except (KeyError, TypeError, ValueError, json.JSONDecodeError):
                cached = None
        if cached is not None:
            validated, metadata = cached
            cached_calls += 1
        else:
            response, metadata = client.complete_json(prompt, json.dumps(context, ensure_ascii=False))
            validated = _validate(response, context)
        safe_meta = {key: value for key, value in metadata.items() if key != "raw_content"}
        if cached is not None:
            safe_meta = {**safe_meta, "reused_exact_path_artifact": True}
        calls.append({"path_id": path["path_id"], "response": validated, "metadata": safe_meta})
        if artifact_path:
            dump_json(artifact_path, calls[-1])
        if validated["status"] == "CLASSIFIED":
            path["function_context"] = validated["function_context"]
            path["semantic_interpretation"] = validated
            classified += 1
        else:
            path["semantic_interpretation"] = validated
            unresolved += 1
    real_artifacts = sum(
        bool(item["metadata"].get("request_id"))
        and item["metadata"].get("response_model") not in {None, "", "fake"}
        for item in calls
    )
    artifact_total_tokens = sum(
        int(item["metadata"].get("usage", {}).get("total_tokens", 0) or 0)
        for item in calls
    )
    return validated_doc, {
        "provider": "deepseek", "selected": len(selected), "calls": len(calls),
        "api_calls_this_run": len(calls) - cached_calls,
        "cached_exact_path_calls": cached_calls,
        "real_api_response_artifacts": real_artifacts,
        "artifact_total_tokens": artifact_total_tokens,
        "classified": classified, "unknown_or_need_context": unresolved,
        "formal_decisions_delegated_to_llm": 0,
        "records": calls,
    }
