"""Structured DeepSeek task for recoverable hard-gap clusters."""

from __future__ import annotations

import json
import hashlib
import re
from pathlib import Path
from typing import Any

from dateassertion.coverage_analysis.observation import validate_observation_helpers
from dateassertion.ir.schema import PropertyIR, dump_json, load_json
from dateassertion.rtl_frontend.parser import RTLDesign
from .client import DeepSeekClient
from .coverage_gap_analyzer import _normalise_contracts


def _windows(cluster: dict[str, Any], radius: int = 3, limit: int = 60) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    used = 0
    for file in cluster.get("source_files", []):
        if not Path(file).is_file():
            continue
        lines = Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
        for anchor in cluster.get("source_lines", []):
            if used >= limit:
                break
            start = max(1, int(anchor) - radius)
            end = min(len(lines), int(anchor) + radius, start + limit - used - 1)
            result.append(
                {
                    "file": file,
                    "line_start": start,
                    "line_end": end,
                    "rtl": "\n".join(f"{line}: {lines[line - 1]}" for line in range(start, end + 1)),
                }
            )
            used += end - start + 1
    return result


def _region_view(cluster: dict[str, Any]) -> dict[str, Any]:
    return {
        "region_id": cluster["cluster_id"],
        "region": cluster.get("semantic_function", "OTHER_CONTROL").upper(),
        "module": cluster["module"],
        "source_files": cluster.get("source_files", []),
        "missing_property_families": cluster.get("available_property_families", []),
        "existing_region_ids": [cluster.get("recovered_region_id", cluster["cluster_id"])],
        "hard_gap_target_signals": cluster.get("signals", []),
        "hard_gap_target_source_lines": cluster.get("source_lines", []),
    }


def _expand_case_branch_proposals(raw: dict[str, Any]) -> dict[str, Any]:
    """Deterministically split an LLM multi-branch proposal into local case contracts."""
    proposals = raw.get("property_gaps", [])
    if not isinstance(proposals, list):
        return raw
    expanded: list[dict[str, Any]] = []
    for proposal in proposals:
        if not isinstance(proposal, dict):
            continue
        branches = []
        conditions = []
        for evidence in proposal.get("evidence", []) if isinstance(proposal.get("evidence"), list) else []:
            if not isinstance(evidence, dict):
                continue
            kind = str(evidence.get("kind", "")).upper()
            if kind == "CONDITION":
                conditions.append(evidence)
            if kind not in {"CASE_BRANCH", "ASSIGNMENT"}:
                continue
            file = str(evidence.get("file", ""))
            try:
                line = int(evidence.get("line", 0))
            except (TypeError, ValueError):
                continue
            if not Path(file).is_file() or line < 1:
                continue
            source = Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
            if line > len(source):
                continue
            match = re.match(
                r"\s*([^:]+):\s*([A-Za-z_][A-Za-z0-9_$]*)"
                r"(?:\s*\[[^]]+\])?\s*(<=|=)\s*(.*?);?\s*$",
                source[line - 1],
            )
            if not match:
                continue
            selector = ""
            selector_line = 0
            for previous in range(line - 1, max(0, line - 25), -1):
                selector_match = re.search(r"\bcase[xz]?\s*\((.*?)\)", source[previous - 1])
                if selector_match:
                    selector = selector_match.group(1).strip()
                    selector_line = previous
                    break
            if selector:
                branches.append(
                    {
                        "label": match.group(1).strip(),
                        "lhs": match.group(2),
                        "operator": match.group(3),
                        "rhs": match.group(4).strip(),
                        "selector": selector,
                        "selector_evidence": {"file": file, "line": selector_line, "kind": "CONDITION"},
                        "branch_evidence": {"file": file, "line": line, "kind": "CASE_BRANCH"},
                    }
                )
        if len(branches) < 2:
            continue
        consequent_names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", str(proposal.get("consequent", ""))))
        if not {branch["lhs"] for branch in branches} <= consequent_names:
            continue
        for branch in branches:
            rhs_compact = re.sub(r"\s+", "", branch["rhs"])
            if rhs_compact in {"1", "1'b1", "1'd1"}:
                consequent = branch["lhs"]
            elif rhs_compact in {"0", "1'b0", "1'd0"}:
                consequent = f"!{branch['lhs']}"
            else:
                consequent = f"{branch['lhs']} == ({branch['rhs']})"
            expanded.append(
                {
                    **proposal,
                    "reason": f"{proposal.get('reason', '')} [deterministically split case {branch['label']}]",
                    "antecedent": (
                        f"({proposal.get('antecedent', '')}) && "
                        f"({branch['selector']} == {branch['label']})"
                    ),
                    "consequent": consequent,
                    "temporal_relation": "NEXT_CYCLE" if branch["operator"] == "<=" else proposal.get("temporal_relation"),
                    "evidence": conditions + [branch["selector_evidence"], branch["branch_evidence"]],
                    "deterministic_case_split": True,
                }
            )
    if not expanded:
        return raw
    return {**raw, "property_gaps": proposals + expanded}


def _assignments(cluster: dict[str, Any], design: RTLDesign, limit: int = 40) -> list[dict[str, Any]]:
    signals = set(cluster.get("signals", [])) | set(cluster.get("fanin", [])) | set(cluster.get("fanout", []))
    result = []
    for assignment in design.assignments:
        if assignment.module != cluster.get("module"):
            continue
        if assignment.lhs in signals or set(assignment.dependencies) & signals:
            guard_line = None
            guard_source = ""
            if assignment.guard and Path(assignment.file).is_file():
                source = Path(assignment.file).read_text(encoding="utf-8", errors="replace").splitlines()
                guard_names = set(
                    name for name in re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", assignment.guard)
                    if name in design.signals
                )
                for line_number in range(assignment.line - 1, max(0, assignment.line - 25), -1):
                    text = source[line_number - 1] if line_number <= len(source) else ""
                    if "if" in text and guard_names & set(re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", text)):
                        guard_line = line_number
                        guard_source = text.strip()
                        break
            result.append(
                {
                    "lhs": assignment.lhs,
                    "rhs": assignment.rhs,
                    "guard": assignment.guard,
                    "kind": assignment.kind,
                    "file": assignment.file,
                    "line": assignment.line,
                    "dependencies": assignment.dependencies,
                    "guard_source_line": guard_line,
                    "guard_source": guard_source,
                }
            )
    return result[:limit]


class HardGapAnalyzer:
    def __init__(self, client: DeepSeekClient, prompt_path: str | Path):
        self.client = client
        self.system_prompt = Path(prompt_path).read_text(encoding="utf-8")

    def analyze(
        self,
        cluster: dict[str, Any],
        item_records: list[dict[str, Any]],
        design: RTLDesign,
        properties: list[PropertyIR],
        output_path: str | Path,
        min_confidence: float = 0.65,
        candidate_limit: int = 3,
    ) -> tuple[list[dict[str, Any]], list[dict[str, Any]], dict[str, Any]]:
        member_ids = set(cluster.get("remaining_item_ids", []))
        evidence_items = [item for item in item_records if item["cid"] in member_ids][:12]
        request = {
            "prompt_digest": hashlib.sha256(self.system_prompt.encode("utf-8")).hexdigest(),
            "validator_version": "hard-gap-evidence-v2",
            "target_type": "HARD_GAP",
            "target_id": cluster["cluster_id"],
            "hard_gap_classification": cluster["hard_gap_classification"],
            "classification_reason": cluster["recoverability_reason"],
            "module": cluster["module"],
            "hierarchy_paths": cluster["hierarchy_paths"],
            "verification_region": cluster["verification_region"],
            "recovered_region_id": cluster["recovered_region_id"],
            "remaining_items": cluster["remaining_items"],
            "signals": cluster["signals"],
            "target_source_lines": cluster["source_lines"],
            "fanin": cluster["fanin"],
            "fanout": cluster["fanout"],
            "available_property_families": cluster["available_property_families"],
            "related_properties": [
                {"property_id": prop.property_id, "family": prop.family, "body": prop.body}
                for prop in properties if prop.property_id in cluster["related_properties"]
            ],
            "item_evidence": evidence_items,
            "local_rtl": _windows(cluster),
            "structural_assignments": _assignments(cluster, design),
            "candidate_limit": candidate_limit,
        }
        path = Path(output_path)
        if path.is_file():
            cached = load_json(path)
            if cached.get("status") == "ok" and cached.get("request") == request:
                return cached.get("accepted", []), cached.get("helpers", []), cached
        dump_json(path, {"status": "request_prepared", "request": request})
        record: dict[str, Any] = {"request": request}
        try:
            attempts: list[dict[str, Any]] = []
            raw: dict[str, Any] = {}
            metadata: dict[str, Any] = {}
            helpers: list[dict[str, Any]] = []
            helper_rejected: list[dict[str, Any]] = []
            contracts: list[dict[str, Any]] = []
            rejected: list[dict[str, Any]] = []
            next_request: dict[str, Any] = request
            for attempt in range(2):
                raw, metadata = self.client.complete_json(
                    self.system_prompt, json.dumps(next_request, ensure_ascii=False)
                )
                if str(raw.get("target_id", "")) != cluster["cluster_id"]:
                    raise ValueError("LLM changed hard-gap target_id")
                normalized_raw = _expand_case_branch_proposals(raw)
                helpers, helper_rejected = validate_observation_helpers(
                    raw.get("observation_helpers", []), set(design.signals), set(design.files)
                )
                contracts, rejected = _normalise_contracts(
                    normalized_raw, _region_view(cluster), design, min_confidence, helpers
                )
                attempts.append(
                    {
                        "attempt": attempt + 1,
                        "response": raw,
                        "accepted_count": len(contracts),
                        "rejected": rejected,
                        "helper_rejected": helper_rejected,
                        "metadata": metadata,
                    }
                )
                if contracts or not raw.get("property_gaps"):
                    break
                next_request = {
                    **request,
                    "correction_attempt": attempt + 1,
                    "previous_response": raw,
                    "validation_feedback": rejected + helper_rejected,
                    "correction_instruction": (
                        "Correct every validation error without weakening the obligation. "
                        "A source line containing ':' before an assignment is CASE_BRANCH, "
                        "and its exact label must appear in the antecedent. Cite the supplied "
                        "guard_source_line as CONDITION. Keep at least two target signals and "
                        "use NEXT_CYCLE for <=. Return the full required JSON object."
                    ),
                }
            for contract in contracts:
                contract["target_module"] = cluster["module"]
                contract["hard_gap_cluster_id"] = cluster["cluster_id"]
                contract["anchor_region_id"] = cluster["recovered_region_id"]
            record.update(
                {
                    "status": "ok",
                    "response": raw,
                    "accepted": contracts,
                    "helpers": helpers,
                    "rejected": rejected,
                    "helper_rejected": helper_rejected,
                    "metadata": metadata,
                    "attempts": attempts,
                }
            )
        except Exception as exc:
            contracts, helpers = [], []
            record.update({"status": "safe_failure", "error": str(exc), "accepted": [], "helpers": [], "rejected": []})
        dump_json(path, record)
        return contracts, helpers, record
