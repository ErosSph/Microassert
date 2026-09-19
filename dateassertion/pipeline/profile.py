"""Design-independent microarchitecture profile derived from validated IR."""

from __future__ import annotations

from collections import Counter
from typing import Any

from dateassertion.ir.schema import MicroarchitectureIR, ObjectType, PropertyIR


def _searchable(region: Any) -> str:
    return " ".join(
        [region.region_id, region.name, region.module]
        + [str(value) for value in region.signals.values()]
    ).lower()


def build_microarchitecture_profile(
    ir: MicroarchitectureIR,
    properties: list[PropertyIR] | None = None,
) -> dict[str, Any]:
    regions = ir.regions
    counts = Counter(region.type.value for region in regions)
    categories: dict[str, list[str]] = {
        "pipeline_stage_structure": [],
        "fsm_control": [],
        "handshake_request_response": [],
        "resource_ownership": [],
        "extension_objects": [],
        "register_update": [],
        "datapath": [],
        "decode": [],
        "pc_branch": [],
        "memory_path": [],
        "interrupt_exception": [],
        "other_discovered_regions": [],
    }
    typed = {
        ObjectType.PIPELINE: "pipeline_stage_structure",
        ObjectType.FSM: "fsm_control",
        ObjectType.HANDSHAKE: "handshake_request_response",
        ObjectType.REQUEST_RESPONSE: "handshake_request_response",
        ObjectType.RESOURCE: "resource_ownership",
        ObjectType.EXTENSION: "extension_objects",
        ObjectType.REGISTER_UPDATE: "register_update",
        ObjectType.DATAPATH: "datapath",
        ObjectType.DECODE: "decode",
    }
    for region in regions:
        text = _searchable(region)
        primary = typed.get(region.type)
        if primary:
            categories[primary].append(region.region_id)
        if any(token in text for token in ("decode", "decoder", "instr", "inst_")):
            categories["decode"].append(region.region_id)
        if any(token in text for token in ("pc_", "branch", "jump")):
            categories["pc_branch"].append(region.region_id)
        if any(token in text for token in ("mem", "rib", "load", "store")):
            categories["memory_path"].append(region.region_id)
        if any(token in text for token in ("interrupt", "exception", "irq", "trap", "clint", "int_")):
            categories["interrupt_exception"].append(region.region_id)
        if not primary:
            categories["other_discovered_regions"].append(region.region_id)
    pipeline_stages = [
        {
            "region_id": region.region_id,
            "module": region.module,
            "transfers": region.details.get("transfers", []),
            "stall": region.details.get("stall"),
            "flush": region.details.get("flush"),
            "valid_in": region.details.get("valid_in"),
            "valid_out": region.details.get("valid_out"),
        }
        for region in regions if region.type == ObjectType.PIPELINE
    ]
    props = properties or []
    return {
        "schema": "microarchitecture-profile.v1",
        "design": ir.design,
        "top_module": ir.top_module,
        "microarchitecture_type": "PIPELINED" if pipeline_stages else "CONTROL_OR_UNDETERMINED",
        "detected_region_count": len(regions),
        "valid_region_count": sum(region.type != ObjectType.UNKNOWN for region in regions),
        "unknown_region_count": counts.get(ObjectType.UNKNOWN.value, 0),
        "object_type_counts": dict(sorted(counts.items())),
        "llm_call_count": len(regions),
        "llm_validated_response_count": sum(region.analysis_source == "deepseek" for region in regions),
        "llm_fallback_count": sum(region.analysis_source != "deepseek" for region in regions),
        "pipeline_stages": pipeline_stages,
        "categories": {key: list(dict.fromkeys(value)) for key, value in categories.items()},
        "generated_property_count": len(props),
        "property_families": sorted({prop.family for prop in props}),
    }
