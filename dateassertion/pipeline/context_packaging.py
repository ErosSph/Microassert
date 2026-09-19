"""Bounded semantic context packaging and LLM response validation."""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any

from dateassertion.ontology.contracts import PRIMITIVES
from dateassertion.ontology.primitives import expression_signals


class ContextResponseError(ValueError):
    pass


_PRIMITIVE_SIGNATURES = {
    "UPDATE": ["CONDITION", "TARGET", "VALUE", "DELAY"],
    "HOLD": ["CONDITION", "TARGET"],
    "CAUSALITY": ["CAUSE", "EFFECT", "DELAY"],
    "ORDERING": ["FIRST", "SECOND", "DELAY"],
    "STABILITY": ["CONDITION", "SIGNALS"],
    "DATA_INTEGRITY": ["CONDITION", "SOURCE", "TARGET", "DELAY"],
    "MUTUAL_EXCLUSION": ["SIGNALS"],
    "PERSISTENCE": ["START", "END"],
    "CONSERVATION": ["CONDITION", "BEFORE", "AFTER"],
    "RESET": ["RESET", "TARGET", "VALUE"],
    "PROGRESS": ["START", "END", "MAX_DELAY"],
}


def _compact_import_node(item: dict[str, Any]) -> dict[str, Any]:
    kind = item.get("kind")
    if kind == "assignment":
        return {
            "id": item.get("id"), "kind": kind, "module": item.get("module"),
            "lhs": item.get("lhs"), "rhs": str(item.get("rhs", ""))[:280],
            "guard": str(item.get("guard", ""))[:280],
            "timing": item.get("timing"), "source": item.get("source"),
        }
    return {
        key: item.get(key) for key in ("id", "kind", "module", "name", "width", "role", "source")
        if key in item
    }


def _compact_cross_edge(edge: dict[str, Any]) -> dict[str, Any]:
    return {
        "edge_id": edge["id"],
        "semantic_kind": edge["semantic_kind"],
        "source": edge["source"],
        "target": edge["target"],
        "port": edge["port"],
        "parent_expression": edge["parent_expression"],
        "evidence": edge["evidence"],
    }


def _global_summary(design_map: dict[str, Any]) -> dict[str, Any]:
    modules = sorted(
        design_map.get("modules", []),
        key=lambda item: (-(item["assignment_count"] + item["instance_count"]), item["module"]),
    )
    return {
        "top_module": design_map["top_module"],
        "reachable_module_count": design_map["summary"]["reachable_modules"],
        "concrete_instance_count": design_map["summary"]["concrete_instances"],
        "cross_module_dependency_count": design_map["summary"]["cross_module_dependencies"],
        "major_modules": [
            {
                "module": item["module"],
                "instances": item["instance_count"],
                "assignments": item["assignment_count"],
                "state_registers": len(item["owned_state_registers"]),
            }
            for item in modules[:16]
        ],
        "major_control_dataflow": [
            {**item, "signals": item.get("signals", [])[:8]}
            for item in design_map.get("major_control_dataflow", [])[:8]
        ],
    }


def package_region_context(
    design_map: dict[str, Any],
    region: dict[str, Any],
    *,
    attempt: int,
    max_chars: int = 18000,
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Build Global Summary + Target Region + Boundary Context only."""

    coi = region.get("coi", {})
    local_nodes = []
    for item in coi.get("nodes", []):
        if item.get("kind") == "assignment":
            local_nodes.append({
                "id": item["id"], "kind": "assignment", "lhs": item["lhs"],
                "rhs": item["rhs"], "guard": item["guard"],
                "timing": item["timing"], "source": item["source"],
            })
        elif item.get("kind") == "signal":
            local_nodes.append({
                "id": item["id"], "kind": "signal", "name": item["name"],
                "width": item.get("width"), "role": item.get("role"),
                "source": item.get("source"),
            })
    cross_edges = region.get("boundary", {}).get("cross_edges", [])
    expanded_edges = region.get("boundary", {}).get("expanded_cross_edges", [])
    combined_edges = {item["id"]: item for item in cross_edges + expanded_edges}
    imported_semantic_context = []
    ordered_imports = sorted(
        region["boundary"].get("imported_semantic_context", []),
        key=lambda item: (
            not item.get("terminal_semantics_found", False),
            len(item.get("cross_edge_path", [])),
            item.get("requested_local_signal", ""),
        ),
    )
    terminal_exists = any(item.get("terminal_semantics_found", False) for item in ordered_imports)
    seen_imports: set[tuple[str, str, str, bool]] = set()
    for item in ordered_imports:
        if terminal_exists and not item.get("terminal_semantics_found", False):
            continue
        endpoint = item.get("external_endpoint", {})
        signature = (
            item.get("requested_local_signal", ""), endpoint.get("module", ""),
            endpoint.get("signal", ""), bool(item.get("terminal_semantics_found", False)),
        )
        if signature in seen_imports:
            continue
        seen_imports.add(signature)
        copied = dict(item)
        nodes = copied.get("semantic_nodes", [])
        endpoint_signal = endpoint.get("signal", "")
        assignments = sorted(
            (node for node in nodes if node.get("kind") == "assignment"),
            key=lambda node: (node.get("lhs") != endpoint_signal, node.get("id", "")),
        )[:2]
        signals = [node for node in nodes if node.get("kind") == "signal"][:1]
        copied["semantic_nodes"] = [
            _compact_import_node(node) for node in assignments + signals
        ]
        copied["semantic_edges"] = [
            {key: edge.get(key) for key in ("type", "source", "target", "clock") if key in edge}
            for edge in copied.get("semantic_edges", [])[:4]
        ]
        copied["rtl_context"] = [
            {**rtl, "snippet": rtl.get("snippet", "")[:450]}
            for rtl in copied.get("rtl_context", [])[:1]
        ]
        imported_semantic_context.append(copied)
    payload = {
        "schema": "region_flow-context-package.v1",
        "instruction": (
            "Analyze only this verification region. Do not infer a missing producer or consumer. "
            "Return NEED_CONTEXT for every semantic dependency that is required but not supplied."
        ),
        "allowed_fixed_primitives": _PRIMITIVE_SIGNATURES,
        "global_design_summary": _global_summary(design_map),
        "target_region": {
            "region_id": region["region_id"],
            "kind": region["kind"],
            "module": region["module"],
            "seed_signals": region["seed_signals"],
            "signals": region.get("signals", []),
            "local_semantic_nodes": local_nodes,
            "local_semantic_edges": coi.get("edges", []),
            "rtl_context": coi.get("rtl_context", []),
        },
        "boundary_cross_region_context": {
            "imported_signals": region["boundary"].get("imported_signals", []),
            "exported_signals": region["boundary"].get("exported_signals", []),
            "imported_dependencies": [
                _compact_cross_edge(item) for item in combined_edges.values()
            ],
            "imported_semantic_context": imported_semantic_context,
            "unresolved_dependencies": region["boundary"].get("unresolved_dependencies", []),
        },
        "context_expansion": region.get("context_expansion"),
        "attempt": attempt,
    }
    encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True)
    truncated = False
    if len(encoded) > max_chars:
        truncated = True
        # Preserve semantic summaries and dependencies; trim verbose RTL first.
        payload["target_region"]["rtl_context"] = [
            {**item, "snippet": item.get("snippet", "")[:1000]}
            for item in payload["target_region"]["rtl_context"][:4]
        ]
        payload["target_region"]["local_semantic_nodes"] = local_nodes[:64]
        payload["target_region"]["local_semantic_edges"] = coi.get("edges", [])[:96]
        payload["boundary_cross_region_context"]["imported_dependencies"] = payload[
            "boundary_cross_region_context"
        ]["imported_dependencies"][:80]
        payload["boundary_cross_region_context"]["imported_semantic_context"] = payload[
            "boundary_cross_region_context"
        ]["imported_semantic_context"][:8]
        encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True)
    if len(encoded) > max_chars:
        payload["target_region"]["local_semantic_nodes"] = payload["target_region"][
            "local_semantic_nodes"
        ][:24]
        payload["target_region"]["local_semantic_edges"] = payload["target_region"][
            "local_semantic_edges"
        ][:32]
        payload["boundary_cross_region_context"]["imported_semantic_context"] = [
            {
                **item,
                "semantic_nodes": item.get("semantic_nodes", [])[:8],
                "semantic_edges": item.get("semantic_edges", [])[:8],
                "rtl_context": [],
            }
            for item in payload["boundary_cross_region_context"]["imported_semantic_context"][:4]
        ]
        encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True)
    while len(encoded) > max_chars:
        target = payload["target_region"]
        boundary = payload["boundary_cross_region_context"]
        if target["local_semantic_edges"]:
            target["local_semantic_edges"].pop()
        elif target["local_semantic_nodes"]:
            target["local_semantic_nodes"].pop()
        elif len(boundary["imported_dependencies"]) > 4:
            boundary["imported_dependencies"].pop()
        elif len(payload["global_design_summary"]["major_control_dataflow"]) > 4:
            payload["global_design_summary"]["major_control_dataflow"].pop()
        elif len(payload["global_design_summary"]["major_modules"]) > 4:
            payload["global_design_summary"]["major_modules"].pop()
        elif len(boundary["imported_semantic_context"]) > 4:
            boundary["imported_semantic_context"].pop()
        else:
            break
        encoded = json.dumps(payload, ensure_ascii=False, sort_keys=True)
    if len(encoded) > max_chars:
        raise ValueError(
            f"semantic context cannot be represented within max_chars={max_chars}; got {len(encoded)}"
        )
    digest = hashlib.sha256(encoded.encode("utf-8")).hexdigest()
    stats = {
        "region_id": region["region_id"],
        "attempt": attempt,
        "context_chars": len(encoded),
        "estimated_tokens": (len(encoded) + 3) // 4,
        "max_chars": max_chars,
        "truncated": truncated,
        "context_sha256": digest,
        "imported_dependencies": len(payload["boundary_cross_region_context"]["imported_dependencies"]),
        "unresolved_dependencies": len(payload["boundary_cross_region_context"]["unresolved_dependencies"]),
        "whole_design_rtl_supplied": False,
    }
    return payload, stats


def validate_region_response(
    response: dict[str, Any], context: dict[str, Any]
) -> dict[str, Any]:
    """Fail closed on guessed signals, SVA, or malformed context requests."""

    if not isinstance(response, dict):
        raise ContextResponseError("response must be a JSON object")
    expected_region = context["target_region"]["region_id"]
    if response.get("region_id") != expected_region:
        raise ContextResponseError("response region_id does not match supplied context")
    status = response.get("status")
    if status not in {"COMPLETE", "NEED_CONTEXT"}:
        raise ContextResponseError("status must be COMPLETE or NEED_CONTEXT")
    needs = response.get("needs_context", [])
    contracts = response.get("contracts", [])
    if not isinstance(needs, list) or not isinstance(contracts, list):
        raise ContextResponseError("needs_context and contracts must be arrays")
    known = set(context["target_region"].get("signals", []))
    known.update(context["boundary_cross_region_context"].get("imported_signals", []))
    known.update(context["boundary_cross_region_context"].get("exported_signals", []))
    if status == "NEED_CONTEXT":
        if not needs:
            raise ContextResponseError("NEED_CONTEXT requires at least one signal and reason")
        for item in needs:
            if not isinstance(item, dict) or not isinstance(item.get("signal"), str):
                raise ContextResponseError("context request needs a signal")
            if item["signal"] not in known:
                raise ContextResponseError(f"context request guesses unknown signal {item['signal']!r}")
            if not isinstance(item.get("reason"), str) or not item["reason"].strip():
                raise ContextResponseError("context request needs a reason")
        if contracts:
            raise ContextResponseError("NEED_CONTEXT cannot also emit contracts")
    else:
        if needs:
            raise ContextResponseError("COMPLETE cannot retain unresolved context requests")
        for contract in contracts:
            if not isinstance(contract, dict):
                raise ContextResponseError("each contract must be an object")
            if contract.get("scope") not in {"LOCAL", "CROSS_REGION"}:
                raise ContextResponseError("contract scope must be LOCAL or CROSS_REGION")
            primitive = str(contract.get("primitive", "")).upper()
            if primitive not in PRIMITIVES:
                raise ContextResponseError(f"unknown fixed primitive {primitive!r}")
            roles = contract.get("roles")
            if not isinstance(roles, dict):
                raise ContextResponseError("contract roles must be an object")
            if any(
                isinstance(value, str) and re.search(r"\b(assert|property|endproperty)\b", value, re.I)
                for value in roles.values()
            ):
                raise ContextResponseError("LLM response contains SVA instead of semantic roles")
            referenced: set[str] = set()
            for value in roles.values():
                values = value if isinstance(value, list) else [value]
                for expression in values:
                    if isinstance(expression, str):
                        referenced.update(expression_signals(expression))
            invalid = referenced - known
            if invalid:
                raise ContextResponseError(f"contract guesses signals absent from context: {sorted(invalid)}")
            evidence = contract.get("evidence_signals")
            if not isinstance(evidence, list) or not evidence or not set(evidence) <= known:
                raise ContextResponseError("contract must cite supplied evidence_signals")
            confidence = contract.get("confidence")
            if not isinstance(confidence, (int, float)) or not 0 <= confidence <= 1:
                raise ContextResponseError("contract confidence must be in [0, 1]")
    return response
