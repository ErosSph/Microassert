"""Compositional Contract generation from formally validated region paths."""

from __future__ import annotations

import hashlib
import json
from typing import Any

from dateassertion.ir.schema import ContractIR, PropertyIR
from dateassertion.ontology.primitives import bind_extension_primitives
from dateassertion.rtl_frontend.parser import RTLDesign


def _contract(
    path: dict[str, Any], level: str, source_index: int, target_index: int,
    bound: int, edge_ids: list[str], *, helper_ids: list[str] | None = None,
    primitive: str = "PROGRESS",
) -> ContractIR:
    source_region = path["regions"][source_index]
    target_region = path["regions"][target_index]
    source = path["activation_predicates"][source_index]
    target = path["activation_predicates"][target_index]
    digest = hashlib.sha1(
        f"{path['path_id']}|{level}|{source_index}|{target_index}".encode()
    ).hexdigest()[:12]
    region = f"req85_{level.lower()}_{digest}"
    roles = (
        {"START": source, "END": target, "MAX_DELAY": bound}
        if primitive == "PROGRESS"
        else {"FIRST": source, "SECOND": target, "MAX_DELAY": bound}
    )
    rule = {
        "primitive": primitive,
        "roles": roles,
        "semantics": (
            f"[{level}] formally validated functional path relation "
            f"{source_region} -> {target_region}."
        ),
        "confidence": float(path.get("formal_confidence", 0.0)),
        "path_analysis_level": level,
        "path_id": path["path_id"],
        "source_region": source_region,
        "target_region": target_region,
        "covered_path_edges": edge_ids,
        "helper_property_ids": helper_ids or [],
        "provenance": "FORMAL_VALIDATED_REGION_PATH_FIXED_TEMPLATE",
    }
    evidence = []
    for item in path.get("static_evidence", []):
        for raw in item.get("source_locations", []):
            if raw.get("file"):
                evidence.append({
                    "files": [raw["file"]],
                    "line_start": int(raw.get("line", 0) or 0),
                    "line_end": int(raw.get("line", 0) or 0),
                    "snippet": str(raw.get("detail", "")),
                    "path_id": path["path_id"],
                    "region_edge_id": item["edge_id"],
                })
    return ContractIR(
        contract_id=f"contract_{region}",
        object_type="FUNCTIONAL_REGION_PATH",
        ontology_classification="NEW_OBJECT_CANDIDATE",
        region=region,
        module=path["module"],
        invariants=[rule],
        evidence=evidence,
        reused_primitives=[primitive],
    )


def generate_compositional_contracts(
    validated_doc: dict[str, Any], *, adjacent_bound: int = 48,
    intermediate_bound: int = 56, end_to_end_bound: int = 64,
) -> tuple[list[ContractIR], dict[str, dict[str, Any]]]:
    """Generate adjacent, intermediate and end-to-end contracts.

    Adjacent contracts reuse whichever mandatory relation was already proved
    non-vacuous: bounded progress or bounded dominance.  Larger contracts
    remain probes until their own Formal run succeeds.
    """

    contracts: list[ContractIR] = []
    metadata: dict[str, dict[str, Any]] = {}
    for path in validated_doc.get("paths", []):
        adjacent_regions: list[str] = []
        for index, relation in enumerate(path.get("mandatory_adjacent_relations", [])):
            if relation.get("causality_type") == "PROGRESS":
                primitive = "PROGRESS"
            else:
                # classify_formal_paths accepts an adjacent relation only when
                # progress or bounded dominance is Proven.  Reuse the exact
                # compiler-owned dominance form when progress timed out.
                primitive = "BOUNDED_DOMINANCE"
            edge_ids = path["region_edges"][index:index + 1]
            contract = _contract(
                path, "ADJACENT", index, index + 1, adjacent_bound, edge_ids,
                primitive=primitive,
            )
            contracts.append(contract)
            adjacent_regions.append(contract.region)
            metadata[contract.region] = {
                "level": "ADJACENT", "path_id": path["path_id"],
                "covered_path_edges": edge_ids, "proof_role": "VERIFICATION_AND_HELPER_CANDIDATE",
            }
        if len(path["regions"]) >= 3:
            target = min(len(path["regions"]) - 1, 2)
            edge_ids = path["region_edges"][:target]
            contract = _contract(
                path, "INTERMEDIATE", 0, target, intermediate_bound, edge_ids,
                helper_ids=adjacent_regions[:target],
            )
            contracts.append(contract)
            metadata[contract.region] = {
                "level": "INTERMEDIATE", "path_id": path["path_id"],
                "covered_path_edges": edge_ids, "helper_contract_regions": adjacent_regions[:target],
                "proof_role": "VERIFICATION",
            }
        if len(path["regions"]) >= 4:
            edge_ids = list(path["region_edges"])
            contract = _contract(
                path, "END_TO_END", 0, len(path["regions"]) - 1,
                end_to_end_bound, edge_ids, helper_ids=adjacent_regions,
            )
            contracts.append(contract)
            metadata[contract.region] = {
                "level": "END_TO_END", "path_id": path["path_id"],
                "covered_path_edges": edge_ids, "helper_contract_regions": adjacent_regions,
                "proof_role": "VERIFICATION",
            }
    deduplicated: list[ContractIR] = []
    seen: set[str] = set()
    for contract in contracts:
        rule = contract.invariants[0]
        key = json.dumps(
            {"module": contract.module, "primitive": rule["primitive"], "roles": rule["roles"]},
            sort_keys=True,
        )
        if key in seen:
            metadata.pop(contract.region, None)
            continue
        seen.add(key)
        deduplicated.append(contract)
    return deduplicated, metadata


def bind_compositional_contracts(
    contracts: list[ContractIR], design: RTLDesign, reset_asserted: str,
) -> tuple[list[PropertyIR], list[Any]]:
    module_signals = {module: set(values) for module, values in design.module_signals.items()}
    properties, bindings = bind_extension_primitives(contracts, module_signals, reset_asserted)
    for prop in properties:
        prop.source = "formal-validated-functional-region-path+fixed-progress-template"
        prop.source_classification = "RTL_STRUCTURAL"
        prop.description = "Req8.5 compositional microarchitecture path assertion."
    return properties, bindings


def split_properties_by_level(
    properties: list[PropertyIR], contract_metadata: dict[str, dict[str, Any]],
) -> dict[str, list[PropertyIR]]:
    result = {"ADJACENT": [], "INTERMEDIATE": [], "END_TO_END": []}
    for prop in properties:
        level = contract_metadata.get(prop.region_id, {}).get("level")
        if level in result:
            result[level].append(prop)
    return result
