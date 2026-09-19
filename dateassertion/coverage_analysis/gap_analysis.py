"""Cluster uncovered proof-core items into explainable microarchitecture regions."""

from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import MicroarchitectureIR, PropertyIR
from dateassertion.ontology.property_families import PropertyFamily
from dateassertion.rtl_frontend.parser import RTLDesign
from .proof_core import CoverItem, coverage_item_summary


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")

FAMILY_PRIORITY: dict[str, list[str]] = {
    "CPU_CONTROL_FSM": [
        PropertyFamily.FSM_LEGAL_TRANSITION.value,
        PropertyFamily.FSM_STATE_HOLD.value,
        PropertyFamily.FSM_CONTROL_OUTPUT.value,
        PropertyFamily.FSM_EVENT_NEXT_STATE.value,
        PropertyFamily.FSM_FORBIDDEN_TRANSITION.value,
        PropertyFamily.FSM_MUTUAL_EXCLUSION.value,
        PropertyFamily.CROSS_REGION_CAUSALITY.value,
    ],
    "INSTRUCTION_DECODE": [
        PropertyFamily.DECODE_CONSISTENCY.value,
        PropertyFamily.DECODE_MUTUAL_EXCLUSION.value,
        PropertyFamily.CROSS_REGION_CAUSALITY.value,
    ],
    "PC_BRANCH_CONTROL": [
        PropertyFamily.BRANCH_PC_UPDATE.value,
        PropertyFamily.SEQUENTIAL_PC_UPDATE.value,
        PropertyFamily.TRAP_PC_UPDATE.value,
        PropertyFamily.PC_UPDATE_PATH.value,
        PropertyFamily.CROSS_REGION_CAUSALITY.value,
    ],
    "MEMORY_CONTROLLER": [
        PropertyFamily.MEMORY_INTENT_REQUEST.value,
        PropertyFamily.MEMORY_RESPONSE_CAUSALITY.value,
        PropertyFamily.MEMORY_REQUEST_TYPE_CONSISTENCY.value,
        PropertyFamily.MEMORY_COMPLETION_CLEAR.value,
        PropertyFamily.MEMORY_COMPLETION_STATE_TRANSITION.value,
        PropertyFamily.MEMORY_READ_WRITE_EXCLUSION.value,
        PropertyFamily.CROSS_REGION_CAUSALITY.value,
    ],
    "REGISTER_WRITEBACK": [PropertyFamily.EXECUTE_WRITEBACK.value, PropertyFamily.CROSS_REGION_CAUSALITY.value],
    "ALU_SHIFTER": [PropertyFamily.DATAPATH_OPERATION_SELECT.value, PropertyFamily.DATAPATH_STABILITY.value, PropertyFamily.CROSS_REGION_CAUSALITY.value],
    "IRQ_TRAP": [PropertyFamily.TRAP_PC_UPDATE.value, PropertyFamily.FSM_EVENT_NEXT_STATE.value, PropertyFamily.CROSS_REGION_CAUSALITY.value],
    "PCPI": [PropertyFamily.HANDSHAKE_CAUSALITY.value, PropertyFamily.HANDSHAKE_COMPLETION.value, PropertyFamily.CROSS_REGION_CAUSALITY.value],
    "OTHER_CONTROL": [PropertyFamily.CROSS_REGION_CAUSALITY.value],
}


def _line_text(path: str, start: int, end: int, cache: dict[str, list[str]]) -> str:
    if path not in cache:
        try:
            cache[path] = Path(path).read_text(encoding="utf-8", errors="replace").splitlines()
        except OSError:
            cache[path] = []
    lines = cache[path]
    return "\n".join(lines[max(0, start - 1) : min(len(lines), end)])


def _signals(text: str, known: set[str]) -> set[str]:
    return {name for name in IDENT.findall(text) if name in known}


def _semantic_region(signals: set[str], assigned: set[str], module: str) -> str:
    names = {name.lower() for name in signals | assigned}
    scores = Counter()
    for name in names:
        if name.startswith(("mem_", "memory_")):
            scores["MEMORY_CONTROLLER"] += 3
        if name.startswith(("instr_", "decoded_", "decoder_")) or name.startswith("is_"):
            scores["INSTRUCTION_DECODE"] += 2
        if name in {"reg_pc", "next_pc", "current_pc", "reg_next_pc", "latched_branch"} or "branch" in name:
            scores["PC_BRANCH_CONTROL"] += 3
        if name in {"cpu_state", "mem_state", "irq_state"} or name.endswith("_state"):
            scores["CPU_CONTROL_FSM"] += 4
        if name.startswith(("cpuregs_", "reg_out", "latched_rd")) or "writeback" in name:
            scores["REGISTER_WRITEBACK"] += 3
        if name.startswith(("alu_", "reg_op", "reg_sh")) or "shift" in name:
            scores["ALU_SHIFTER"] += 2
        if name.startswith("irq") or name in {"trap", "instr_trap", "eoi"}:
            scores["IRQ_TRAP"] += 3
        if name.startswith("pcpi_"):
            scores["PCPI"] += 4
    for name in {item.lower() for item in assigned}:
        if name.startswith(("instr_", "decoded_", "decoder_", "is_")):
            scores["INSTRUCTION_DECODE"] += 4
        if name in {"reg_pc", "reg_next_pc", "current_pc", "next_pc"}:
            scores["PC_BRANCH_CONTROL"] += 5
        if name in {"cpu_state", "mem_state", "irq_state"}:
            scores["CPU_CONTROL_FSM"] += 5
    if scores:
        return sorted(scores, key=lambda key: (-scores[key], FAMILY_PRIORITY.get(key, []), key))[0]
    return "OTHER_CONTROL" if module else "UNMAPPED"


def build_coverage_gap(
    items: list[CoverItem],
    design: RTLDesign,
    microarchitecture: MicroarchitectureIR,
    properties: list[PropertyIR],
    top_module: str,
) -> dict[str, Any]:
    known = set(design.signals)
    source_cache: dict[str, list[str]] = {}
    assignments_by_location: dict[tuple[str, str, int], list[Any]] = defaultdict(list)
    for assignment in design.assignments:
        assignments_by_location[(assignment.file, assignment.module, assignment.line)].append(assignment)
    clusters: dict[tuple[str, str], dict[str, Any]] = {}
    for item in items:
        source_text = _line_text(item.file, item.line_start, item.line_end, source_cache)
        item_signals = _signals(" ".join((item.expression, item.description, source_text)), known)
        nearby_assignments = []
        for line in range(max(1, item.line_start - 1), item.line_end + 2):
            nearby_assignments.extend(assignments_by_location.get((item.file, item.module, line), []))
        assigned = {assignment.lhs for assignment in nearby_assignments}
        item_signals.update(assigned)
        semantic = _semantic_region(item_signals, assigned, item.module)
        key = (item.module or top_module, semantic)
        if key not in clusters:
            clusters[key] = {
                "region_id": re.sub(r"[^a-z0-9]+", "_", f"{key[0]}_{semantic}".lower()).strip("_"),
                "region": semantic,
                "module": key[0],
                "items": [],
                "signals": set(),
                "covered_lines": set(),
                "uncovered_lines": set(),
                "unreachable_lines": set(),
                "always_blocks": set(),
                "existing_region_ids": set(),
                "source_files": set(),
            }
        cluster = clusters[key]
        cluster["items"].append((item, sorted(item_signals)))
        cluster["signals"].update(item_signals)
        cluster["source_files"].add(item.file)
        lines = set(range(item.line_start, item.line_end + 1))
        if item.status == "covered_and_checked":
            cluster["covered_lines"].update(lines)
        elif item.status == "uncovered_or_unchecked":
            cluster["uncovered_lines"].update(lines)
        else:
            cluster["unreachable_lines"].update(lines)
        for index, block in enumerate(design.always_blocks):
            if block.file == item.file and block.module == item.module and block.line_start <= item.line_start <= block.line_end:
                cluster["always_blocks"].add(f"{block.module}:always_{index}:{block.line_start}-{block.line_end}")
        for region in microarchitecture.regions:
            line_overlap = item.file in region.evidence.rtl_files and not (
                item.line_end < region.evidence.line_start or item.line_start > region.evidence.line_end
            )
            region_signals = set(region.signals.values()) if all(isinstance(value, str) for value in region.signals.values()) else set()
            if line_overlap or item_signals & region_signals:
                cluster["existing_region_ids"].add(region.region_id)

    rendered: list[dict[str, Any]] = []
    for cluster in clusters.values():
        status_counts = Counter(item.status for item, _ in cluster["items"])
        covered = status_counts["covered_and_checked"]
        uncovered = status_counts["uncovered_or_unchecked"]
        unreachable = status_counts["unreachable_or_undetectable"]
        total = covered + uncovered + unreachable
        matching_properties = [
            prop for prop in properties
            if prop.region_id in cluster["existing_region_ids"] or set(prop.signals) & cluster["signals"]
        ]
        existing_families = sorted({prop.family for prop in matching_properties})
        missing = [family for family in FAMILY_PRIORITY.get(cluster["region"], []) if family not in existing_families]
        config_candidates = sum(
            item.status == "unreachable_or_undetectable"
            and not signals
            and bool(re.search(r"\b(?:\d+)?'[bBoOdDhH][0-9a-fA-FxXzZ_]+\b", item.expression))
            for item, signals in cluster["items"]
        )
        uncovered_details = [
            {
                "cid": item.cid,
                "file": item.file,
                "line_start": item.line_start,
                "line_end": item.line_end,
                "type": item.cover_item_type,
                "expression": item.expression,
                "signals": signals,
            }
            for item, signals in cluster["items"] if item.status == "uncovered_or_unchecked"
        ]
        rendered.append({
            "region_id": cluster["region_id"],
            "region": cluster["region"],
            "module": cluster["module"],
            "total_elements": total,
            "covered_elements": covered,
            "reachable_uncovered_elements": uncovered,
            "unreachable_or_undetectable_elements": unreachable,
            "configuration_disabled_candidates": config_candidates,
            "coverage_percent": round(100.0 * covered / total, 2) if total else 0.0,
            "effective_reachable_coverage_percent": round(100.0 * covered / (covered + uncovered), 2) if covered + uncovered else 0.0,
            "uncovered_signals": sorted({signal for detail in uncovered_details for signal in detail["signals"]}),
            "uncovered_lines": sorted(cluster["uncovered_lines"]),
            "unreachable_lines": sorted(cluster["unreachable_lines"]),
            "source_files": sorted(cluster["source_files"]),
            "always_blocks": sorted(cluster["always_blocks"]),
            "existing_region_ids": sorted(cluster["existing_region_ids"]),
            "existing_properties": [prop.property_id for prop in matching_properties],
            "existing_property_families": existing_families,
            "missing_property_families": missing,
            "uncovered_logic": uncovered_details,
            "item_ids": sorted(item.cid for item, _ in cluster["items"]),
            "covered_item_ids": sorted(
                item.cid for item, _ in cluster["items"] if item.status == "covered_and_checked"
            ),
            "uncovered_or_unchecked_item_ids": sorted(
                item.cid for item, _ in cluster["items"] if item.status == "uncovered_or_unchecked"
            ),
            "unreachable_or_undetectable_item_ids": sorted(
                item.cid for item, _ in cluster["items"] if item.status == "unreachable_or_undetectable"
            ),
            "generated_or_submodule": cluster["module"] != top_module,
            "priority_score": uncovered * (2 if cluster["region"] in FAMILY_PRIORITY else 1) + len(missing) * 10,
        })
    rendered.sort(key=lambda region: (-region["priority_score"], region["region_id"]))
    summary = coverage_item_summary(items)
    summary.update({
        "reachable_uncovered": summary["uncovered_or_unchecked"],
        "unreachable_or_configuration_disabled": summary["unreachable_or_undetectable"],
        "configuration_disabled_candidates": sum(region["configuration_disabled_candidates"] for region in rendered),
        "generated_or_submodule_items": sum(region["total_elements"] for region in rendered if region["generated_or_submodule"]),
        "denominator_policy": {
            "official": "All JasperGold cover items (matches tool report).",
            "effective_reachable": "covered_and_checked + uncovered_or_unchecked; unreachable/undetectable reported separately.",
            "configuration_disabled": "Conservative candidates only; never auto-excluded from the official denominator.",
        },
    })
    return {"summary": summary, "regions": rendered}
