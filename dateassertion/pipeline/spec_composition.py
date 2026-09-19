"""Requirement 8.8: Local Contract-Guided Compositional Verification."""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import time
from typing import Any

import yaml

from dateassertion.coverage_analysis.property_attribution import build_property_attribution
from dateassertion.ir.schema import FormalPropertyResult, PropertyIR, dump_json, properties_from_dict
from dateassertion.llm.client import DeepSeekClient, LLMError
from dateassertion.pipeline.contract_validation import _llm_config
from dateassertion.pipeline.local_contract_composition import (
    Requirement88ValidationError,
    build_contract_graph,
    build_local_contracts,
    compile_composition_properties,
    generate_composition_candidates,
    incremental_update_contract_graph,
    package_spec_composition_context,
    relation_coverage,
    select_composition_portfolio,
    validate_spec_composition_response,
)
from dateassertion.pipeline.local_region_assertions import result_counts, spec_lines
from dateassertion.pipeline.region_flow import _reachable_formal_files
from dateassertion.pipeline.spec_extraction import _coverage, _formal, _stable_cover_ids, _trusted
from dateassertion.rtl_frontend.hierarchical_design import build_hierarchical_design_map
from dateassertion.rtl_frontend.parser import RTLDesign, parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def _context_digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False).encode()).hexdigest()


def _usage(records: list[dict[str, Any]]) -> dict[str, int]:
    counter: Counter[str] = Counter()
    for record in records:
        for key, value in record.get("metadata", {}).get("usage", {}).items():
            if isinstance(value, int) and not isinstance(value, bool):
                counter[key] += value
    return dict(counter)


def _validated_llm_constraints(
    client: DeepSeekClient, prompt: str, context: dict[str, Any], path: Path,
    *, attempts: int, maximum_delay: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    digest = _context_digest(context)
    prior = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else []

    def isolate(response: dict[str, Any]) -> dict[str, Any] | None:
        """Keep only individually valid relations and repair event aliases.

        Overlapping RTL Regions can expose the exact same event in multiple
        Local Contracts.  If an LLM chain returns to an earlier contract, move
        that event to an unused, identical-predicate contract.  This changes no
        RTL semantics and is checked again by the strict validator.
        """

        raw_by_id = {str(item.get("constraint_id")): deepcopy(item)
                     for item in response.get("constraints", []) if isinstance(item, dict)}
        individually_valid: dict[str, dict[str, Any]] = {}
        for constraint_id, raw in raw_by_id.items():
            try:
                one = validate_spec_composition_response(
                    {"constraints": [raw], "lifecycle_chains": []}, context,
                    maximum_delay=maximum_delay,
                )
            except (Requirement88ValidationError, ValueError):
                continue
            individually_valid[constraint_id] = one["constraints"][0]
        context_contracts = {item["contract_id"]: item for item in context["contracts"]}
        event_records = [
            (contract["contract_id"], event["event_id"], event)
            for contract in context["contracts"] for event in contract["events"]
        ]

        best_chain: list[dict[str, Any]] = []
        best_raw_chain: dict[str, Any] | None = None
        for raw_chain in response.get("lifecycle_chains", []):
            chain: list[dict[str, Any]] = []
            used_contracts: set[str] = set()
            current_target: tuple[str, str] | None = None
            for constraint_id in raw_chain.get("constraint_ids", []):
                original = individually_valid.get(str(constraint_id))
                if original is None:
                    break
                item = deepcopy(original)
                if current_target is not None:
                    current_contract, current_event = current_target
                    current_predicate = next(
                        event["predicate"] for cid, eid, event in event_records
                        if (cid, eid) == current_target
                    )
                    source_key = (item["source_contract_id"], item["source_event_id"])
                    source_predicate = next(
                        event["predicate"] for cid, eid, event in event_records
                        if (cid, eid) == source_key
                    )
                    if "".join(current_predicate.split()) != "".join(source_predicate.split()):
                        break
                    item["source_contract_id"], item["source_event_id"] = current_contract, current_event
                if not used_contracts:
                    used_contracts.add(item["source_contract_id"])
                target_contract = item["target_contract_id"]
                target_event = item["target_event_id"]
                if target_contract in used_contracts:
                    target_predicate = item["target_predicate"]
                    module = context_contracts[item["source_contract_id"]]["module"]
                    alternatives = sorted((
                        (context_contracts[cid].get("readiness_level", 0), cid, eid)
                        for cid, eid, event in event_records
                        if cid not in used_contracts
                        and context_contracts[cid]["module"] == module
                        and "".join(str(event["predicate"]).split()) == "".join(str(target_predicate).split())
                    ), reverse=True)
                    if not alternatives:
                        break
                    _, target_contract, target_event = alternatives[0]
                    item["target_contract_id"], item["target_event_id"] = target_contract, target_event
                    item["contract_alias_rebound"] = True
                # Revalidate the exact modified IDs and evidence.
                raw_item = {key: value for key, value in item.items()
                            if key not in {"source_predicate", "target_predicate",
                                          "validated_exact_spec_evidence", "contract_alias_rebound"}}
                try:
                    checked = validate_spec_composition_response(
                        {"constraints": [raw_item], "lifecycle_chains": []}, context,
                        maximum_delay=maximum_delay,
                    )["constraints"][0]
                except (Requirement88ValidationError, ValueError):
                    break
                if item.get("contract_alias_rebound"):
                    checked["contract_alias_rebound"] = True
                chain.append(checked)
                used_contracts.add(checked["target_contract_id"])
                current_target = (checked["target_contract_id"], checked["target_event_id"])
            if len(chain) > len(best_chain):
                best_chain, best_raw_chain = chain, raw_chain
        if len(best_chain) >= 2:
            constraint_ids = [item["constraint_id"] for item in best_chain]
            selected_constraints = best_chain
            selected_chains = [{
                "chain_id": str((best_raw_chain or {}).get("chain_id", "isolated_chain")),
                "name": str((best_raw_chain or {}).get("name", "isolated lifecycle")),
                "constraint_ids": constraint_ids,
                "functional_meaning": str((best_raw_chain or {}).get("functional_meaning", "")),
            }]
        else:
            # An evidence-backed Adjacent Contract is a valid Req8.8 result on
            # its own.  Do not discard strictly validated relations merely
            # because a noisy response failed to form a two-edge lifecycle.
            selected_constraints = sorted(
                individually_valid.values(), key=lambda item: item["constraint_id"]
            )
            selected_chains = []
            if not selected_constraints:
                return None
        normalized = {
            "constraints": selected_constraints,
            "lifecycle_chains": selected_chains,
        }
        # Strip validation-added fields before the final schema gate.
        normalized["constraints"] = [{
            key: value for key, value in item.items()
            if key not in {"source_predicate", "target_predicate", "validated_exact_spec_evidence"}
        } for item in normalized["constraints"]]
        try:
            validated = validate_spec_composition_response(
                normalized, context, maximum_delay=maximum_delay,
            )
        except (Requirement88ValidationError, ValueError):
            return None
        validated["recovered_from_strict_per_relation_isolation"] = True
        validated["quarantined_constraints"] = len(raw_by_id) - len(selected_constraints)
        return validated

    cached = next((item for item in reversed(prior)
                   if item.get("context_sha256") == digest and not item.get("validation_error")), None)
    isolated_cached = None
    if cached is None:
        isolated_candidates = [
            (isolate(item.get("response", {})), item) for item in prior
            if item.get("context_sha256") == digest
        ]
        isolated_candidates = [(value, item) for value, item in isolated_candidates if value]
        if isolated_candidates:
            isolated_cached, isolated_record = max(
                isolated_candidates,
                key=lambda pair: (len(pair[0].get("constraints", [])), pair[1].get("attempt", 0)),
            )
            cached = isolated_record
    if cached:
        validated = isolated_cached or validate_spec_composition_response(
            cached["response"], context, maximum_delay=maximum_delay,
        )
        if isolated_cached is not None:
            records = [
                {**item, "cache_hit": item is cached, "used_for_isolated_binding": item is cached}
                for item in prior if item.get("context_sha256") == digest
            ]
        else:
            records = [{**cached, "cache_hit": True}]
        api_calls = 0
    else:
        records = []
        error = ""
        validated = None
        transport_error: LLMError | None = None
        for attempt in range(1, attempts + 1):
            payload: Any = context
            if error:
                payload = {
                    "context": context, "previous_validation_error": error,
                    "instruction": "Return a complete corrected JSON object; do not weaken or bypass any gate.",
                }
            try:
                response, metadata = client.complete_json(
                    prompt, json.dumps(payload, ensure_ascii=False)
                )
            except LLMError as exc:
                # Preserve earlier real responses for the strict per-relation
                # isolation below when the proxy/provider fails mid-sequence.
                transport_error = exc
                break
            record = {
                "attempt": attempt, "context_sha256": digest, "response": response,
                "metadata": {key: value for key, value in metadata.items() if key != "raw_content"},
            }
            try:
                validated = validate_spec_composition_response(
                    response, context, maximum_delay=maximum_delay,
                )
            except (Requirement88ValidationError, ValueError) as exc:
                error = str(exc)
                record["validation_error"] = error
                records.append(record)
                dump_json(path, records)
                continue
            records.append(record)
            dump_json(path, records)
            break
        if validated is None:
            isolated_candidates = [(isolate(item.get("response", {})), item) for item in records]
            isolated_candidates = [(value, item) for value, item in isolated_candidates if value]
            if not isolated_candidates:
                if transport_error is not None:
                    raise transport_error
                raise Requirement88ValidationError(error or "DeepSeek composition binding did not validate")
            validated, _record = max(
                isolated_candidates,
                key=lambda pair: (len(pair[0].get("constraints", [])), pair[1].get("attempt", 0)),
            )
        api_calls = len(records)
    return validated, {
        "provider": getattr(client.config, "provider", "deepseek"), "calls": len(records), "api_calls_this_run": api_calls,
        "validated_cache_hits": int(bool(cached)), "usage": _usage(records),
        "response_models": sorted({str(item.get("metadata", {}).get("response_model"))
                                   for item in records if item.get("metadata", {}).get("response_model")}),
        "real_response_artifacts": sum(
            bool(item.get("metadata", {}).get("request_id"))
            and item.get("metadata", {}).get("response_model") not in {None, "", "fake"}
            for item in records
        ),
        "whole_design_rtl_supplied": False, "generated_sva": False,
    }


def _assert_local_baseline(root: Path, design: RTLDesign) -> tuple[list[PropertyIR], dict[str, Any], dict[str, Any]]:
    summary = json.loads((root / "spec_extraction_summary.json").read_text(encoding="utf-8"))
    if summary.get("source_digest") != design.source_digest:
        raise RuntimeError("Req8.7 baseline and Req8.8 RTL digests differ")
    raw_properties = json.loads((root / "spec_plus_rtl" / "trusted_properties.json").read_text(encoding="utf-8"))
    properties = properties_from_dict(raw_properties)
    result_doc = json.loads((root / "spec_plus_rtl" / "formal_results.json").read_text(encoding="utf-8"))
    results = result_doc.get("results", [])
    by_id = {item["property_id"]: item for item in results}
    if not properties or any(
        item.property_id not in by_id or by_id[item.property_id].get("result") != "PASS"
        or by_id[item.property_id].get("vacuity") != "NON_VACUOUS"
        for item in properties
    ):
        raise RuntimeError("Req8.7 Local Contract baseline is not wholly PASS + NON_VACUOUS")
    return properties, summary, result_doc


def _formal_metrics(
    root: Path, result: Any, properties: list[PropertyIR], baseline_checked: set[str],
    prior_checked: set[str], relation: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], set[str]]:
    checked = _stable_cover_ids(root / "formal" / "coverage_items.tsv")
    coverage = _coverage(root)
    counts = result_counts(properties, result.results)
    return ({
        **counts,
        "proof_core": result.coverage,
        "effective_proof_core": coverage,
        "unique_vs_local_baseline": len(checked - baseline_checked),
        "lost_vs_local_baseline": len(baseline_checked - checked),
        "marginal_new_checked_items": len(checked - prior_checked),
        "marginal_lost_checked_items": len(prior_checked - checked),
        "formal_runtime_seconds": result.runtime_seconds,
        "relations": relation or {},
    }, checked)


def _stabilize_composite_portfolio(
    design: RTLDesign, local_properties: list[PropertyIR], composites: list[PropertyIR],
    top: str, root: Path, config: dict[str, Any], *, attribution: bool,
) -> tuple[list[PropertyIR], Any, list[dict[str, Any]]]:
    """Keep the Req8.7 baseline fixed and monotonically remove unstable composites."""

    current = list(composites)
    rounds = []
    while True:
        combined = local_properties + current
        result = _formal(design, combined, top, root, config, attribution=attribution)
        by_id = {item.property_id: item for item in result.results}
        bad_local = [item.property_id for item in local_properties
                     if item.property_id not in by_id or by_id[item.property_id].result != "PASS"
                     or by_id[item.property_id].vacuity != "NON_VACUOUS"]
        if bad_local:
            raise RuntimeError(f"fixed Req8.7 Local baseline destabilized: {bad_local}")
        survivors = [item for item in current if item.property_id in by_id
                     and by_id[item.property_id].result == "PASS"
                     and by_id[item.property_id].vacuity == "NON_VACUOUS"]
        removed = sorted({item.property_id for item in current} - {item.property_id for item in survivors})
        rounds.append({
            "round": len(rounds) + 1, "local_properties_fixed": len(local_properties),
            "input_composites": len(current), "surviving_composites": len(survivors),
            "removed_composite_ids": removed,
        })
        if not removed:
            return survivors, result, rounds
        current = survivors


def _write_report(path: Path, summary: dict[str, Any]) -> None:
    baseline = summary["experiments"]["A_local_baseline"]
    rows = []
    for experiment in summary["experiments"]["progressive"]:
        rows.append(
            f"| {experiment['name']} | {experiment['local_assertions']} + {experiment['trusted_composites']} | "
            f"{experiment['pass']}/{experiment['cex']}/{experiment['unknown']}/{experiment['vacuous']} | "
            f"{experiment['proven_rate_percent']:.2f}% | "
            f"{experiment['proof_core']['covered_items']}/{experiment['proof_core']['total_items']} = "
            f"{experiment['proof_core']['proof_core_coverage_percent']:.2f}% | "
            f"{experiment['effective_proof_core']['covered_and_checked']}/"
            f"{experiment['effective_proof_core']['effective_reachable_denominator']} = "
            f"{experiment['effective_proof_core']['effective_reachable_coverage_percent']:.2f}% | "
            f"{experiment['unique_vs_local_baseline']} |"
        )
    final = summary["final"]
    report = f"""# {summary['design']} Requirement 8.8 真实测试报告

## 结论

Req8.8 把 Req8.7 的 {summary['local_contracts']['contracts']} 个 Region 升级成 Local Contract，
并仅在 contract interface、SPEC/RTL partial order 与 execution context 均可检查的情况下组合。
DeepSeek `{summary['llm']['requested_model']}` 只把官方 SPEC 语义绑定到既有 contract/event ID；
所有 Composite SVA 都由固定 bounded-sequence 模板生成，Formal 中未加入 assumption。

最终集合为 {final['local_assertions']} 条可信 Local SVA + {final['trusted_composites']} 条可信
Composite SVA；独立最终复跑为 {final['pass']} PASS、{final['cex']} CEX、
{final['unknown']} UNKNOWN、{final['vacuous']} VACUOUS，因而所有入选 Composite Contract 均满足
**PASS + NON_VACUOUS**。

| 实验 | Local + Composite | PASS/CEX/UNKNOWN/Vacuous | Proven率 | Raw Proof-Core | Effective Proof-Core | 相对 Local 新增 checked item |
|---|---:|---:|---:|---:|---:|---:|
| A Local baseline | {baseline['local_assertions']} + 0 | {baseline['pass']}/{baseline['cex']}/{baseline['unknown']}/{baseline['vacuous']} | {baseline['proven_rate_percent']:.2f}% | {baseline['proof_core']['covered_items']}/{baseline['proof_core']['total_items']} = {baseline['proof_core']['proof_core_coverage_percent']:.2f}% | {baseline['effective_proof_core']['covered_and_checked']}/{baseline['effective_proof_core']['effective_reachable_denominator']} = {baseline['effective_proof_core']['effective_reachable_coverage_percent']:.2f}% | 0 |
{chr(10).join(rows)}
| Final exact attribution rerun | {final['local_assertions']} + {final['trusted_composites']} | {final['pass']}/{final['cex']}/{final['unknown']}/{final['vacuous']} | {final['proven_rate_percent']:.2f}% | {final['proof_core']['covered_items']}/{final['proof_core']['total_items']} = {final['proof_core']['proof_core_coverage_percent']:.2f}% | {final['effective_proof_core']['covered_and_checked']}/{final['effective_proof_core']['effective_reachable_denominator']} = {final['effective_proof_core']['effective_reachable_coverage_percent']:.2f}% | {final['new_checked_items']} |

所有实验的官方 Raw denominator 均为 {final['proof_core']['total_items']}；Effective denominator 均为
{final['effective_proof_core']['effective_reachable_denominator']}，因此增益不是由分母变化造成。

## Contract Graph 与候选

- Local Contract readiness：{summary['local_contracts']['readiness']}。
- Contract Graph：{summary['contract_graph']['nodes']} 个节点、{summary['contract_graph']['edges']} 条可能组合边，其中 {summary['contract_graph']['spec_constrained_edges']} 条带精确 SPEC 证据。
- 静态产生 {summary['candidate_generation']['candidates']} 个 compatible composition candidate；Formal probe 后 {summary['formal_probe']['trusted']} 个通过严格 Trust Gate。
- 最终验证 {final['relation_coverage']['trusted_composition_relations']} 条 Composite Contract；其中
  {final['relation_coverage']['directly_trusted_adjacent_relations']} 条为直接 Adjacent relation，
  {final['relation_coverage']['transitively_covered_graph_relations']} 条图关系被 Intermediate/Lifecycle
  endpoint contract 覆盖；覆盖阶段为 {', '.join(final['relation_coverage']['covered_lifecycle_stages']) or '无'}。

## 增量组合

增量测试加入 {summary['incremental_update']['new_contracts']} 个新 Contract，仅重算
{summary['incremental_update']['recomputed_pair_space']} 个相关 pair，而全量 pair space 为
{summary['incremental_update']['full_pair_space']}；保留 {summary['incremental_update']['retained_unaffected_edges']}
条既有边，未使任何不相关 Formal 结果失效，并与全量重建图逐边一致。

## SPEC、LLM 与可审计性

SPEC 来源为 `{summary['spec']['source']}`（SHA256 `{summary['spec']['sha256']}`），官方地址为
`{summary['spec']['source_url']}`。本轮送入的是所选协议生命周期
原文行，所有关系均保存 exact quote 和行号。DeepSeek 实际响应 artifact 数为
{summary['llm']['real_response_artifacts']}，总 token 为 {summary['llm']['usage'].get('total_tokens', 0)}；
`whole_design_rtl_supplied=false`、`generated_sva=false`。

## Formal 成本与停止条件

Formal 共执行 {summary['formal_cost']['runs']} 个 multi-target run，总墙钟时间
{summary['formal_cost']['runtime_seconds']:.2f}s。Progressive composition 按边际新增 relation、lifecycle stage、
proof-core item 与 Formal runtime 计算价值；停止原因：`{summary['progressive_stop']['reason']}`，不是固定路径长度截断。
"""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(report, encoding="utf-8")


def run(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = yaml.safe_load(Path(args.config).resolve().read_text(encoding="utf-8"))
    req = config.get("spec_composition", {})
    local_root = Path(args.local_root).resolve()
    spec_path = Path(args.spec).resolve()

    design = parse_rtl([args.rtl])
    graph = build_semantic_graph(design)
    design_map = build_hierarchical_design_map(design, graph, args.top,
                                               include_dirs=config.get("include_dirs", []))
    local_properties, local_summary, local_result = _assert_local_baseline(local_root, design)
    regions = json.loads((local_root / "regions.json").read_text(encoding="utf-8"))
    metadata = json.loads((local_root / "property_metadata.json").read_text(encoding="utf-8"))
    spec_doc = json.loads((local_root / "spec_behaviors.json").read_text(encoding="utf-8"))
    local_contracts = build_local_contracts(regions, local_properties, metadata, graph, design)
    dump_json(output / "local_contracts.json", local_contracts)

    selected_spec_lines = spec_lines(spec_path, req.get("spec_line_ranges", []))
    context = package_spec_composition_context(
        selected_spec_lines, local_contracts,
        max_contracts=int(req.get("max_contracts_for_llm", 24)),
        max_context_chars=int(req.get("max_composition_context_chars", 32_000)),
    )
    dump_json(output / "llm" / "composition_context.json", context)
    prompt = (PROJECT_ROOT / "llm" / "prompts" / "composition_constraints.txt").read_text(encoding="utf-8")
    client = DeepSeekClient(_llm_config(config["llm"]))
    constraints, llm = _validated_llm_constraints(
        client, prompt, context, output / "llm" / "calls.json",
        attempts=int(req.get("llm_validation_attempts", 3)),
        maximum_delay=int(req.get("maximum_composition_delay", 128)),
    )
    if not constraints.get("constraints"):
        raise RuntimeError("DeepSeek did not bind any evidence-backed partial-order constraint")
    dump_json(output / "partial_order_constraints.json", constraints)

    contract_graph = build_contract_graph(local_contracts, constraints)
    dump_json(output / "contract_graph.json", contract_graph)

    # Exercise the actual incremental API with a contract used by SPEC edges.
    constrained_ids = sorted({item["target_contract_id"] for item in constraints["constraints"]})
    new_id = constrained_ids[-1]
    prior_contracts = {**local_contracts, "contracts": [
        item for item in local_contracts["contracts"] if item["contract_id"] != new_id
    ]}
    prior_constraints = {
        **constraints, "constraints": [item for item in constraints["constraints"]
                                        if new_id not in {item["source_contract_id"], item["target_contract_id"]}],
        "lifecycle_chains": [],
    }
    prior_graph = build_contract_graph(prior_contracts, prior_constraints)
    incremental_graph, incremental = incremental_update_contract_graph(
        prior_graph, local_contracts, constraints,
    )
    if {item["edge_id"] for item in incremental_graph["edges"]} != {
        item["edge_id"] for item in contract_graph["edges"]
    }:
        raise RuntimeError("incremental Contract Graph differs from full rebuild")
    dump_json(output / "incremental_update_audit.json", incremental)

    candidate_doc = generate_composition_candidates(
        contract_graph, constraints, max_chain_length=int(req.get("max_chain_length", 6)),
    )
    selected, portfolio = select_composition_portfolio(
        candidate_doc, caps=req.get("portfolio_caps", {}),
    )
    if not selected:
        raise RuntimeError("no compatible Contract composition survived deterministic selection")
    dump_json(output / "composition_candidates.json", candidate_doc)
    dump_json(output / "composition_portfolio.json", {**portfolio, "candidates": selected})

    reset = str(config.get("reset", "resetn"))
    reset_asserted = f"!{reset}" if config.get("reset_active_low", True) else reset
    composite_properties, composite_metadata = compile_composition_properties(
        selected, design, reset_asserted,
    )
    dump_json(output / "generated_composite_properties.json", composite_properties)
    dump_json(output / "composite_property_metadata.json", composite_metadata)

    formal_design = deepcopy(design)
    formal_design.files = _reachable_formal_files(design, design_map)
    probe = _formal(formal_design, composite_properties, args.top,
                    output / "formal_probe", config, attribution=False)
    dump_json(output / "formal_probe" / "formal_results.json", probe)
    trusted_probe = _trusted(composite_properties, probe.results)
    if not trusted_probe:
        raise RuntimeError("no Composite Assertion passed PASS + NON_VACUOUS probe gate")
    trusted_probe_ids = {item.property_id for item in trusted_probe}

    baseline_formal_dir = local_root / "spec_plus_rtl" / "trusted" / "formal"
    baseline_checked = _stable_cover_ids(baseline_formal_dir / "coverage_items.tsv")
    baseline_effective = _coverage(local_root / "spec_plus_rtl" / "trusted")
    baseline_coverage = local_summary["experiments"]["spec_extraction_spec_plus_rtl"]["proof_core"]
    baseline_counts = result_counts(local_properties, [FormalPropertyResult(
        property_id=item["property_id"], result=item["result"], vacuity=item.get("vacuity")
    ) for item in local_result["results"]])
    baseline_experiment = {
        "name": "A Local baseline", "local_assertions": len(local_properties),
        "trusted_composites": 0, **baseline_counts,
        "proof_core": baseline_coverage, "effective_proof_core": baseline_effective,
        "source_artifact": str(local_root / "spec_plus_rtl" / "formal_results.json"),
    }

    # Progressive portfolios are grouped by contract count, not by a hard-coded
    # endpoint.  Each stage contains every previously trusted shorter contract.
    by_length: dict[int, list[PropertyIR]] = {}
    for prop in trusted_probe:
        length = len(composite_metadata[prop.property_id]["contract_ids"])
        by_length.setdefault(length, []).append(prop)
    cumulative: list[PropertyIR] = []
    progressive = []
    previous_checked = baseline_checked
    declining_rounds = 0
    stop_reason = "ALL_AVAILABLE_COMPATIBLE_LENGTHS_EVALUATED"
    stable_rounds: dict[str, Any] = {}
    final_composites: list[PropertyIR] = []
    final_result = None
    run_count = 1
    runtime_sum = probe.runtime_seconds
    for length in sorted(by_length):
        cumulative += by_length[length]
        stage_root = output / "experiments" / f"length_{length}"
        stable, result, rounds = _stabilize_composite_portfolio(
            formal_design, local_properties, cumulative, args.top, stage_root, config,
            attribution=False,
        )
        run_count += len(rounds)
        runtime_sum += result.runtime_seconds
        cumulative = stable
        stable_rounds[str(length)] = rounds
        trusted_ids = {item.property_id for item in stable}
        relation = relation_coverage(trusted_ids, composite_metadata, contract_graph)
        metrics, checked = _formal_metrics(
            stage_root, result, local_properties + stable, baseline_checked,
            previous_checked, relation,
        )
        newly_covered_relations = len(set(relation["trusted_relation_ids"]) - {
            edge for prior in progressive for edge in prior["relations"].get("trusted_relation_ids", [])
        })
        new_stage = int(any(len(composite_metadata[item.property_id]["contract_ids"]) == length
                            for item in stable))
        marginal_value = (
            metrics["marginal_new_checked_items"] - metrics["marginal_lost_checked_items"]
            + 10 * newly_covered_relations + 20 * new_stage - result.runtime_seconds / 30.0
        )
        stage = {
            "name": ("B Local + Adjacent" if length == 2 else
                     f"C Progressive {length}-Contract"),
            "contract_length": length, "local_assertions": len(local_properties),
            "trusted_composites": len(stable), "new_composites_at_length": len(by_length[length]),
            **metrics, "marginal_verification_value": round(marginal_value, 3),
            "stabilization_rounds": len(rounds),
        }
        progressive.append(stage)
        previous_checked = checked
        final_composites, final_result = stable, result
        if marginal_value <= float(req.get("marginal_stop_threshold", 0)):
            declining_rounds += 1
        else:
            declining_rounds = 0
        if declining_rounds >= int(req.get("marginal_stop_patience", 2)):
            stop_reason = f"MARGINAL_VERIFICATION_VALUE_NON_POSITIVE_FOR_{declining_rounds}_STAGES"
            break
    if final_result is None:
        raise RuntimeError("no progressive composition stage was executed")

    # Final exact set gets a clean run with per-property proof-core attribution.
    final_composites, final_result, final_stabilization = _stabilize_composite_portfolio(
        formal_design, local_properties, final_composites, args.top,
        output / "final", config, attribution=bool(req.get("property_attribution", True)),
    )
    run_count += len(final_stabilization)
    runtime_sum += final_result.runtime_seconds
    final_ids = {item.property_id for item in final_composites}
    final_relation = relation_coverage(final_ids, composite_metadata, contract_graph)
    final_metrics, final_checked = _formal_metrics(
        output / "final", final_result, local_properties + final_composites,
        baseline_checked, previous_checked, final_relation,
    )
    if any(item.result != "PASS" or item.vacuity != "NON_VACUOUS" for item in final_result.results):
        raise RuntimeError("final Local + Composite set violated PASS + NON_VACUOUS")
    if final_metrics["proof_core"]["covered_items"] <= baseline_coverage["covered_items"]:
        raise RuntimeError("Local + Composite Raw Proof-Core did not improve over Local baseline")
    if final_metrics["effective_proof_core"]["effective_reachable_coverage_percent"] <= baseline_effective["effective_reachable_coverage_percent"]:
        raise RuntimeError("Local + Composite Effective Proof-Core did not improve over Local baseline")

    attribution = {}
    attribution_path = output / "final" / "formal" / "property_proof_core_items.tsv"
    if attribution_path.is_file():
        combined_metadata = {
            **metadata,
            **{key: value for key, value in composite_metadata.items() if key in final_ids},
        }
        attribution = build_property_attribution(
            attribution_path, output / "final" / "formal" / "coverage_items.tsv",
            combined_metadata, set(),
        )
        dump_json(output / "final" / "property_proof_core_attribution.json", attribution)

    dump_json(output / "trusted_composite_properties.json", final_composites)
    dump_json(output / "trusted_stabilization.json", {
        "progressive": stable_rounds, "final": final_stabilization,
    })
    incremental_summary = {**incremental,
                           "new_contracts": len(incremental["new_contract_ids"])}
    summary = {
        "schema": "region_flow.8-real.v1", "design": args.design, "top": args.top,
        "rtl": str(Path(args.rtl).resolve()), "source_digest": design.source_digest,
        "spec": {
            "source": str(spec_path), "sha256": spec_doc.get("source_sha256"),
            "source_url": req.get("spec_source_url", ""),
            "selected_line_ranges": req.get("spec_line_ranges", []),
            "exact_evidence_constraints": len(constraints["constraints"]),
            "remote_verification": local_summary.get("spec", {}).get("remote_verification", {}),
        },
        "local_contracts": local_contracts["summary"],
        "contract_graph": contract_graph["summary"],
        "candidate_generation": candidate_doc["summary"],
        "portfolio": portfolio,
        "incremental_update": incremental_summary,
        "formal_probe": {**result_counts(composite_properties, probe.results),
                         "trusted": len(trusted_probe)},
        "experiments": {"A_local_baseline": baseline_experiment, "progressive": progressive},
        "final": {
            **final_metrics, "local_assertions": len(local_properties),
            "trusted_composites": len(final_composites),
            "relation_coverage": final_relation,
            "all_pass_non_vacuous": True, "unproven_assumptions": 0,
            "new_checked_items": len(final_checked - baseline_checked),
            "lost_checked_items": len(baseline_checked - final_checked),
        },
        "proof_core_attribution": {
            key: attribution.get(key) for key in (
                "properties_catalogued", "properties_measured", "observed_union_items",
                "global_checked_items", "global_attribution_reconciliation_percent",
                "globally_checked_unattributed_items", "globally_unique_items", "shared_items",
                "properties_with_unique_contribution",
            )
        } if attribution else {},
        "progressive_stop": {"reason": stop_reason,
                             "threshold": req.get("marginal_stop_threshold", 0),
                             "patience": req.get("marginal_stop_patience", 2)},
        "llm": {
            **llm, "requested_model": config.get("llm", {}).get("model"),
        },
        "formal_cost": {"runs": run_count, "runtime_seconds": round(runtime_sum, 3),
                        "generated_composite_candidates": len(composite_properties),
                        "trusted_composites": len(final_composites)},
        "runtime_seconds": round(time.monotonic() - started, 3),
        "artifacts": {
            "local_contracts": str(output / "local_contracts.json"),
            "contract_graph": str(output / "contract_graph.json"),
            "constraints": str(output / "partial_order_constraints.json"),
            "candidates": str(output / "composition_candidates.json"),
            "trusted_composites": str(output / "trusted_composite_properties.json"),
            "final_assertions": str(output / "final" / "assertions.sv"),
        },
    }
    dump_json(output / "spec_composition_summary.json", summary)
    _write_report(Path(args.report).resolve(), summary)
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Req8.8 Local Contract composition")
    parser.add_argument("--design", required=True)
    parser.add_argument("--rtl", required=True)
    parser.add_argument("--top", required=True)
    parser.add_argument("--spec", required=True)
    parser.add_argument("--config", required=True)
    parser.add_argument("--local-root", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--report", required=True)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        summary = run(args)
    except Exception as exc:
        print(f"Requirement 8.8 failed: {exc}")
        return 1
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
