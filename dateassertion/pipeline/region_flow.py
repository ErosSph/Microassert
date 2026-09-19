"""Requirement 8: hierarchical semantic decomposition and validation."""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
from dataclasses import replace
import json
from pathlib import Path
import re
import time
from typing import Any

import yaml

from dateassertion.formal.jaspergold import JasperGoldRunner
from dateassertion.generators.sva_generator import generate_sva
from dateassertion.ir.schema import ObjectType, PropertyIR, dump_json
from dateassertion.llm.client import DeepSeekClient
from dateassertion.ontology.primitives import bind_extension_primitives
from dateassertion.pipeline.context_packaging import (
    ContextResponseError,
    package_region_context,
    validate_region_response,
)
from dateassertion.pipeline.graph_pattern_interpretation import resolve_ambiguous_regions
from dateassertion.pipeline.contract_grounding import contract_to_dict, ground_contracts
from dateassertion.pipeline.contract_validation import _formal_config, _llm_config
from dateassertion.pipeline.region_contracts import (
    contract_scope,
    deterministic_region_contracts,
    llm_response_contracts,
)
from dateassertion.pipeline.semantic_slicing import build_verification_regions, expand_region_context
from dateassertion.rtl_frontend.hierarchical_design import build_hierarchical_design_map
from dateassertion.rtl_frontend.parser import RTLDesign, parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def _run_llm_regions(
    design_map: dict[str, Any],
    regions_doc: dict[str, Any],
    graph: dict[str, Any],
    config: dict[str, Any],
    output: Path,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    llm_config = config.get("region_flow", {}).get("llm_regions", {})
    limit = int(llm_config.get("limit", 3))
    candidates = [
        item for item in regions_doc["regions"]
        if item["kind"] in {"HANDSHAKE", "PIPELINE_VALID_FLOW", "FSM"}
    ]
    selected = []
    seen_modules: set[str] = set()
    for region in candidates:
        if region["module"] in seen_modules:
            continue
        selected.append(region)
        seen_modules.add(region["module"])
        if len(selected) >= limit:
            break
    if not selected:
        selected = [
            item for item in regions_doc["regions"]
            if item["kind"] == "MODULE"
        ][:limit]

    prompt = (PROJECT_ROOT / "llm" / "prompts" / "region_contracts.txt").read_text(encoding="utf-8")
    client = DeepSeekClient(_llm_config(config["llm"]))
    responses: list[dict[str, Any]] = []
    call_records: list[dict[str, Any]] = []
    context_records: list[dict[str, Any]] = []
    usage = Counter()
    response_models: set[str] = set()
    expansions = 0
    expanded_regions: set[str] = set()
    unresolved_regions = 0

    for original in selected:
        region = deepcopy(original)
        accepted: dict[str, Any] | None = None
        validation_error = ""
        for attempt in range(1, 4):
            package, context_stats = package_region_context(
                design_map, region, attempt=attempt,
                max_chars=int(llm_config.get("max_context_chars", 18000)),
            )
            context_records.append(context_stats)
            dump_json(output / "llm" / "contexts" / f"{region['region_id']}_attempt{attempt}.json", package)
            user_payload: dict[str, Any] = package
            if validation_error:
                user_payload = {
                    "context": package,
                    "previous_validation_error": validation_error,
                    "instruction": "Return a complete corrected JSON response without changing supplied facts.",
                }
            response, metadata = client.complete_json(prompt, json.dumps(user_payload, ensure_ascii=False))
            safe_metadata = {key: value for key, value in metadata.items() if key != "raw_content"}
            for key in ("prompt_tokens", "completion_tokens", "total_tokens"):
                usage[key] += int(metadata.get("usage", {}).get(key, 0) or 0)
            if metadata.get("response_model"):
                response_models.add(str(metadata["response_model"]))
            record = {
                "region_id": region["region_id"],
                "attempt": attempt,
                "context_sha256": context_stats["context_sha256"],
                "response": response,
                "metadata": safe_metadata,
            }
            call_records.append(record)
            try:
                validated = validate_region_response(response, package)
            except ContextResponseError as exc:
                validation_error = str(exc)
                record["validation_error"] = validation_error
                continue
            if validated["status"] == "NEED_CONTEXT":
                signals = [item["signal"] for item in validated["needs_context"]]
                region = expand_region_context(region, graph, design_map, signals)
                expansions += 1
                expanded_regions.add(region["region_id"])
                validation_error = ""
                continue
            accepted = validated
            break
        if accepted is None:
            unresolved_regions += 1
            responses.append({
                "region_id": original["region_id"],
                "status": "UNRESOLVED",
                "object_summary": "Context remained insufficient or the response failed validation.",
                "needs_context": [],
                "contracts": [],
            })
        else:
            responses.append(accepted)

    dump_json(output / "llm" / "calls.json", call_records)
    actual_prompt_tokens = usage.get("prompt_tokens", 0)
    return responses, {
        "provider": "deepseek",
        "requested_model": config["llm"].get("model"),
        "response_models": sorted(response_models),
        "regions_selected": len(selected),
        "selected_region_ids": [item["region_id"] for item in selected],
        "calls": len(call_records),
        "usage": dict(usage),
        "average_tokens_per_call": round(actual_prompt_tokens / len(call_records), 2) if call_records else 0.0,
        "total_tokens": usage.get("total_tokens", 0),
        "context_expansions": expansions,
        "context_expansion_rate": round(len(expanded_regions) / len(selected), 6) if selected else 0.0,
        "regions_expanded": len(expanded_regions),
        "unresolved_regions": unresolved_regions,
        "contexts": context_records,
    }


def _has_rules(contract: Any) -> bool:
    fields = (
        "invariants", "update_rules", "hold_rules", "ordering", "causality",
        "stability", "data_integrity", "mutual_exclusion", "reset_behavior",
    )
    return any(getattr(contract, field) for field in fields)


def _scope_map(contracts: list[Any]) -> dict[str, str]:
    return {item.region: contract_scope(item) for item in contracts}


def _formal_counts(
    properties: list[PropertyIR], results: list[Any], scopes: dict[str, str]
) -> dict[str, Any]:
    result_by_id = {item.property_id: item for item in results}
    output: dict[str, Any] = {}
    for scope in ("LOCAL", "CROSS_REGION", "ALL"):
        selected = [
            item for item in properties
            if scope == "ALL" or scopes.get(item.region_id, "LOCAL") == scope
        ]
        values = [result_by_id[item.property_id] for item in selected if item.property_id in result_by_id]
        proven = sum(item.result == "PASS" for item in values)
        cex = sum(item.result == "FAIL" for item in values)
        unknown = len(values) - proven - cex
        output[scope.lower()] = {
            "total": len(values),
            "proven": proven,
            "cex": cex,
            "unknown": unknown,
            "vacuous": sum(item.vacuity == "VACUOUS" for item in values),
            "non_vacuous": sum(item.vacuity == "NON_VACUOUS" for item in values),
            "vacuity_unknown": sum(item.vacuity not in {"VACUOUS", "NON_VACUOUS"} for item in values),
            "proven_rate": round(100 * proven / len(values), 2) if values else 0.0,
        }
    return output


def _effective_coverage(formal_dir: Path, selected_modules: set[str]) -> dict[str, Any]:
    path = formal_dir / "coverage_items.tsv"
    counts = Counter()
    module_counts: dict[str, Counter[str]] = {}
    if path.is_file():
        for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
            status = line.split("\t", 1)[0].strip()
            match = re.search(r"\bmodule \{([^}]*)\}", line)
            module = match.group(1) if match else ""
            if module not in selected_modules:
                continue
            counts[status] += 1
            module_counts.setdefault(module, Counter())[status] += 1
    covered = counts["covered_and_checked"]
    uncovered = counts["uncovered_or_unchecked"]
    excluded = counts["unreachable_or_undetectable"]
    denominator = covered + uncovered
    return {
        "definition": (
            "Proof-core items in modules targeted by local/cross-region contracts; "
            "unreachable_or_undetectable items are excluded."
        ),
        "selected_modules": sorted(selected_modules),
        "covered_items": covered,
        "effective_denominator": denominator,
        "excluded_unreachable_or_undetectable": excluded,
        "effective_coverage_percent": round(100 * covered / denominator, 2) if denominator else 0.0,
        "by_module": {module: dict(values) for module, values in sorted(module_counts.items())},
    }


def _reachable_formal_files(design: RTLDesign, design_map: dict[str, Any]) -> list[str]:
    modules = {item["module"] for item in design_map["instances"]}
    return list(dict.fromkeys(
        item.file for item in design.modules if item.name in modules
    ))


def _run_formal(
    design: RTLDesign,
    properties: list[PropertyIR],
    top: str,
    output: Path,
    config: dict[str, Any],
    sva_path: Path,
) -> Any:
    generate_sva(
        properties, design.signals, top, sva_path,
        clock=config.get("clock", "clk"), reset=config.get("reset", "rst_n"),
        module_signals=design.module_signals,
    )
    formal_config = _formal_config(config)
    formal_config["include_dirs"] = config.get("include_dirs", [])
    return JasperGoldRunner().run(
        design.files, str(sva_path), top, properties, output, formal_config
    )


def run(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = yaml.safe_load(Path(args.config).resolve().read_text(encoding="utf-8"))
    zero = Path(args.zero_adaptation).resolve() if args.zero_adaptation else output / "zero_adaptation"
    if (zero / "rtl_structure.json").is_file() and (zero / "rtl_semantic_graph.json").is_file():
        zero_design = RTLDesign.load(zero / "rtl_structure.json")
        zero_graph = json.loads((zero / "rtl_semantic_graph.json").read_text(encoding="utf-8"))
        if config.get("region_flow", {}).get("reparse_with_include_dirs", False):
            zero_summary_path = zero / "summary.json"
            zero_summary = json.loads(zero_summary_path.read_text(encoding="utf-8")) if zero_summary_path.is_file() else {}
            inputs = zero_summary.get("input_roots") or [args.rtl]
            design = parse_rtl(inputs, include_dirs=config.get("include_dirs", []))
            graph = build_semantic_graph(design)
            design.save(output / "rtl_structure.json")
            dump_json(output / "rtl_semantic_graph.json", graph)
            dump_json(output / "generic_parser_fix.json", {
                "schema": "region_flow-generic-parser-fix.v1",
                "rule": "resolve includes through caller-provided include directories",
                "design_specific_condition": False,
                "zero_adaptation": {
                    "modules": len(zero_design.modules),
                    "diagnostics": len(zero_design.diagnostics),
                    "graph_edges": zero_graph.get("edge_count", 0),
                },
                "after_generic_fix": {
                    "modules": len(design.modules),
                    "diagnostics": len(design.diagnostics),
                    "graph_edges": graph.get("edge_count", 0),
                },
            })
        else:
            design, graph = zero_design, zero_graph
    else:
        design = parse_rtl([args.rtl])
        graph = build_semantic_graph(design)
        design.save(zero / "rtl_structure.json")
        dump_json(zero / "rtl_semantic_graph.json", graph)

    design_map = build_hierarchical_design_map(
        design, graph, args.top, include_dirs=config.get("include_dirs", [])
    )
    dump_json(output / "design_map.json", design_map)
    regions_doc = build_verification_regions(
        design, graph, design_map,
        coi_depth=int(config.get("region_flow", {}).get("coi_depth", 2)),
        max_nodes=int(config.get("region_flow", {}).get("max_nodes_per_region", 96)),
        max_candidates_per_kind=config.get("region_flow", {}).get("max_candidates_per_kind_per_module"),
    )
    ambiguity_config = config.get("region_flow", {}).get("graph_pattern_ambiguity_llm", {})
    ambiguity_stats: dict[str, Any] = {
        "enabled": False, "selected": 0, "classified": 0,
        "unknown_or_unresolved": 0, "context_expansions": 0,
        "deterministic_match_regions_sent_to_llm": 0,
    }
    if ambiguity_config.get("enabled", False):
        ambiguity_prompt = (
            PROJECT_ROOT / "llm" / "prompts" / "graph_pattern_ambiguity.txt"
        ).read_text(encoding="utf-8")
        regions_doc, ambiguity_stats = resolve_ambiguous_regions(
            regions_doc, graph, design_map,
            DeepSeekClient(_llm_config(config["llm"])), ambiguity_prompt,
            limit=int(ambiguity_config.get("limit", 4)),
            max_attempts=int(ambiguity_config.get("max_attempts", 2)),
            artifact_dir=output / "llm" / "graph_pattern_ambiguity",
        )
        ambiguity_stats = {"enabled": True, **ambiguity_stats}
    dump_json(output / "regions.json", regions_doc)

    contract_llm_config = config.get("region_flow", {}).get("llm_regions", {})
    if contract_llm_config.get("enabled", True):
        llm_responses, llm_stats = _run_llm_regions(design_map, regions_doc, graph, config, output)
    else:
        llm_responses = []
        llm_stats = {
            "provider": "deepseek", "requested_model": config["llm"].get("model"),
            "response_models": [], "regions_selected": 0, "selected_region_ids": [],
            "calls": 0, "usage": {}, "average_tokens_per_call": 0.0, "total_tokens": 0,
            "context_expansions": 0, "context_expansion_rate": 0.0,
            "regions_expanded": 0, "unresolved_regions": 0, "contexts": [],
            "disabled_reason": "Req8.4 uses LLM only for AMBIGUOUS graph-pattern interpretation",
        }
    region_by_id = {item["region_id"]: item for item in regions_doc["regions"]}
    deterministic_contracts = deterministic_region_contracts(
        design, design_map, regions_doc,
        max_local=int(config.get("region_flow", {}).get("max_local_contracts", 8)),
        max_cross=int(config.get("region_flow", {}).get("max_cross_contracts", 6)),
    )
    llm_contracts = llm_response_contracts(llm_responses, region_by_id)
    candidate_contracts = deterministic_contracts + llm_contracts
    grounded, static_results, grounding_rate = ground_contracts(candidate_contracts, design, graph)
    grounded = [item for item in grounded if _has_rules(item)]
    dump_json(output / "contracts.json", grounded)
    dump_json(output / "contract_candidates.json", candidate_contracts)
    dump_json(output / "static_check_results.json", static_results)
    dump_json(output / "context_stats.json", {**llm_stats, "responses": llm_responses})

    reset_asserted = f"!{config.get('reset', 'rst_n')}" if config.get("reset_active_low", True) else config.get("reset", "rst_n")
    module_signals = {module: set(values) for module, values in design.module_signals.items()}
    properties, bindings = bind_extension_primitives(grounded, module_signals, reset_asserted)
    bound_ids = {item.property_id for item in bindings if item.status == "BOUND"}
    properties = [item for item in properties if item.property_id in bound_ids]
    scopes = _scope_map(grounded)
    deterministic_regions = {item.region for item in deterministic_contracts}
    for prop in properties:
        if prop.region_id in deterministic_regions:
            prop.source = "deterministic-hierarchical-semantic-edge+fixed-template"
            prop.source_classification = "RTL_STRUCTURAL"
        else:
            prop.source = "deepseek-bounded-context+fixed-template"
            prop.source_classification = "LLM_HYPOTHESIS"
    max_properties = int(config.get("region_flow", {}).get("max_formal_properties", 16))
    properties = properties[:max_properties]
    dump_json(output / "template_bindings.json", bindings)

    formal_files = _reachable_formal_files(design, design_map)
    formal_design = replace(design, files=formal_files)
    probe_result = _run_formal(
        formal_design, properties, args.top, output / "formal_probe", config,
        output / "probe_assertions.sv",
    )
    dump_json(output / "probe_formal_results.json", probe_result)
    result_by_id = {item.property_id: item for item in probe_result.results}
    trusted = [
        item for item in properties
        if result_by_id[item.property_id].result == "PASS"
        and result_by_id[item.property_id].vacuity != "VACUOUS"
    ]
    final_result = _run_formal(
        formal_design, trusted, args.top, output / "formal", config,
        output / "assertions.sv",
    )
    dump_json(output / "formal_results.json", final_result)
    dump_json(output / "generated_properties.json", trusted)

    probe_counts = _formal_counts(properties, probe_result.results, scopes)
    final_counts = _formal_counts(trusted, final_result.results, scopes)
    selected_modules = {item.target_module for item in trusted}
    effective = _effective_coverage(output / "formal", selected_modules)
    coverage_summary = {
        "schema": "region_flow-coverage.v1",
        "raw_coverage": {
            "definition": (
                "JasperGold top-level proof-core coverage over the full elaborated "
                f"{args.design} denominator."
            ),
            **final_result.coverage,
        },
        "effective_coverage": effective,
    }
    dump_json(output / "coverage_summary.json", coverage_summary)

    semantic_region_count = sum(
        item["kind"] != "MODULE" for item in regions_doc["regions"]
    )
    llm_fallback_rate = (
        ambiguity_stats.get("selected", 0) / semantic_region_count if semantic_region_count else 0.0
    )
    summary = {
        "schema": "region_flow-summary.v1",
        "design": args.design,
        "top": args.top,
        "source_revision": args.source_revision,
        "zero_adaptation": {
            "preserved": (zero / "summary.json").is_file(),
            "path": str(zero),
            "summary": json.loads((zero / "summary.json").read_text(encoding="utf-8")) if (zero / "summary.json").is_file() else {},
        },
        "design_map": design_map["summary"],
        "slicing": regions_doc["summary"],
        "context": {
            "average_tokens_per_llm_call": llm_stats["average_tokens_per_call"],
            "total_llm_tokens": llm_stats["total_tokens"],
            "llm_fallback_rate": round(llm_fallback_rate, 6),
            "context_expansion_rate": llm_stats["context_expansion_rate"],
            **{key: value for key, value in llm_stats.items() if key not in {"contexts"}},
        },
        "graph_pattern_ambiguity": ambiguity_stats,
        "contracts": {
            "deterministic_candidates": len(deterministic_contracts),
            "llm_candidates": len(llm_contracts),
            "grounded_survivors": len(grounded),
            "bound_properties": len(properties),
            "trusted_properties": len(trusted),
            "deterministic_grounding_rate": grounding_rate,
        },
        "formal": {
            "probe": probe_counts,
            "final": final_counts,
            "proof_core_coverage": final_result.coverage,
            "tool": final_result.tool,
            "runtime_seconds": final_result.runtime_seconds,
        },
        "coverage": coverage_summary,
        "completeness": {
            "state_owner_complete": regions_doc["summary"]["state_registers"] == regions_doc["summary"]["state_registers_with_owner"],
            "cross_edges_complete": regions_doc["summary"]["cross_edges"] == regions_doc["summary"]["cross_edges_assigned"],
            "contract_signals_grounded": all(item.status == "BOUND" for item in bindings if item.property_id in {prop.property_id for prop in properties}),
            "unresolved_context_generated_properties": 0,
        },
        "runtime_seconds": round(time.monotonic() - started, 3),
        "artifacts": {
            "design_map": str(output / "design_map.json"),
            "regions": str(output / "regions.json"),
            "context_stats": str(output / "context_stats.json"),
            "contracts": str(output / "contracts.json"),
            "assertions": str(output / "assertions.sv"),
            "formal_results": str(output / "formal_results.json"),
            "coverage_summary": str(output / "coverage_summary.json"),
        },
    }
    dump_json(output / "region_flow_summary.json", summary)
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Requirement 8 hierarchical semantic decomposition")
    parser.add_argument("--design", required=True)
    parser.add_argument("--rtl", required=True)
    parser.add_argument("--top", required=True)
    parser.add_argument("--config", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--zero-adaptation")
    parser.add_argument("--source-revision", default="unknown")
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        summary = run(args)
    except Exception as exc:
        print(f"Requirement 8 failed: {exc}")
        return 1
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
