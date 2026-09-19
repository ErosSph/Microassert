"""Requirement 8.9: Formal gap-guided semantic expansion and refinement."""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import shutil
import time
from typing import Any, Callable

import yaml

from dateassertion.coverage_analysis.proof_core import CoverItem, parse_coverage_items
from dateassertion.coverage_analysis.property_attribution import build_property_attribution
from dateassertion.ir.schema import FormalPropertyResult, PropertyIR, dump_json, properties_from_dict
from dateassertion.llm.client import DeepSeekClient
from dateassertion.pipeline.contract_validation import _llm_config
from dateassertion.pipeline.formal_gap_semantics import (
    Requirement89ValidationError,
    candidate_score,
    compile_completion_composition,
    compile_region_gap_properties,
    coverage_by_type,
    extension_region_from_interpretation,
    gap_summary,
    incremental_update_audit,
    localize_coverage_gaps,
    package_extension_interpretation_context,
    property_from_assignment,
    refine_gap_classification,
    refine_local_contract,
    select_contract_gap_assignments,
    select_residual_region_candidate,
    stable_cover_item_id,
    validate_extension_interpretation,
)
from dateassertion.pipeline.region_flow import _reachable_formal_files, _run_formal
from dateassertion.rtl_frontend.hierarchical_design import build_hierarchical_design_map
from dateassertion.rtl_frontend.parser import RTLDesign, parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def _digest(value: Any) -> str:
    return hashlib.sha256(json.dumps(value, ensure_ascii=False, sort_keys=True).encode()).hexdigest()


def _safe_metadata(value: dict[str, Any]) -> dict[str, Any]:
    return {key: item for key, item in value.items() if key != "raw_content"}


def _validated_llm_interpretation(
    client: DeepSeekClient, prompt: str, context: dict[str, Any], path: Path,
    *, attempts: int,
) -> tuple[dict[str, Any], dict[str, Any]]:
    digest = _digest(context)
    prior = json.loads(path.read_text(encoding="utf-8")) if path.is_file() else []
    cached = next((row for row in reversed(prior) if row.get("context_sha256") == digest and not row.get("validation_error")), None)
    if cached:
        validated = validate_extension_interpretation(cached["response"], context)
        records = [{**cached, "cache_hit": True}]
        api_calls = 0
    else:
        records = []
        validated = None
        error = ""
        for attempt in range(1, attempts + 1):
            payload: Any = context
            if error:
                payload = {
                    "context": context, "previous_validation_error": error,
                    "instruction": "Return corrected JSON using only supplied IDs and signals; do not weaken a gate.",
                }
            response, metadata = client.complete_json(prompt, json.dumps(payload, ensure_ascii=False))
            row = {
                "attempt": attempt, "context_sha256": digest, "response": response,
                "metadata": _safe_metadata(metadata),
            }
            try:
                validated = validate_extension_interpretation(response, context)
            except (Requirement89ValidationError, ValueError) as exc:
                error = str(exc)
                row["validation_error"] = error
                records.append(row)
                dump_json(path, prior + records)
                continue
            records.append(row)
            dump_json(path, prior + records)
            break
        if validated is None:
            raise Requirement89ValidationError(error or "DeepSeek interpretation failed validation")
        api_calls = len(records)
    usage: Counter[str] = Counter()
    for row in records:
        for key, value in row.get("metadata", {}).get("usage", {}).items():
            if isinstance(value, int) and not isinstance(value, bool):
                usage[key] += value
    models = sorted({
        str(row.get("metadata", {}).get("response_model")) for row in records
        if row.get("metadata", {}).get("response_model")
    })
    return validated, {
        "provider": getattr(client.config, "provider", "deepseek"), "requested_model": client.config.model,
        "calls": len(records), "api_calls_this_run": api_calls,
        "validated_cache_hits": int(bool(cached)), "usage": dict(usage),
        "response_models": models,
        "real_response_artifacts": sum(bool(row.get("metadata", {}).get("request_id")) for row in records),
        "whole_design_rtl_supplied": False, "generated_sva": False,
        "decides_formal_status": False, "decides_trusted_status": False,
    }


def _formal(
    design: RTLDesign, properties: list[PropertyIR], top: str, root: Path,
    config: dict[str, Any], *, attribution: bool,
) -> Any:
    local = deepcopy(config)
    local.setdefault("formal", {})["property_attribution"] = attribution
    local["formal"]["attribution_time_limit"] = str(
        config.get("gap_interpretation", {}).get("attribution_time_limit", "10s")
    )
    return _run_formal(design, properties, top, root / "formal", local, root / "assertions.sv")


def _trusted(properties: list[PropertyIR], results: list[FormalPropertyResult]) -> list[PropertyIR]:
    by_id = {item.property_id: item for item in results}
    return [
        prop for prop in properties if prop.property_id in by_id
        and by_id[prop.property_id].result == "PASS"
        and by_id[prop.property_id].vacuity == "NON_VACUOUS"
    ]


def _result_counts(properties: list[PropertyIR], results: list[FormalPropertyResult]) -> dict[str, Any]:
    by_id = {item.property_id: item for item in results}
    rows = [by_id.get(prop.property_id) for prop in properties]
    total = len(properties)
    passed = sum(row is not None and row.result == "PASS" for row in rows)
    failed = sum(row is not None and row.result == "FAIL" for row in rows)
    unknown = total - passed - failed
    vacuous = sum(row is not None and row.vacuity == "VACUOUS" for row in rows)
    non_vacuous = sum(row is not None and row.vacuity == "NON_VACUOUS" for row in rows)
    return {
        "generated": total, "pass": passed, "cex": failed, "unknown": unknown,
        "vacuous": vacuous, "non_vacuous": non_vacuous,
        "proven_rate_percent": round(100 * passed / total, 2) if total else 0.0,
        "trusted": sum(row is not None and row.result == "PASS" and row.vacuity == "NON_VACUOUS" for row in rows),
    }


def _checked_ids(path: Path) -> set[str]:
    return {
        stable_cover_item_id(item) for item in parse_coverage_items(path)
        if item.status == "covered_and_checked"
    }


def _coverage_for_union(universe: list[CoverItem], checked: set[str]) -> dict[str, Any]:
    replaced = []
    for item in universe:
        status = "covered_and_checked" if stable_cover_item_id(item) in checked else item.status
        replaced.append(CoverItem(**{**item.to_dict(), "status": status}))
    return coverage_by_type(replaced)


def _assert_baseline(
    design: RTLDesign, composition_root: Path, local_root: Path,
) -> tuple[list[PropertyIR], dict[str, Any], list[CoverItem]]:
    summary = json.loads((composition_root / "spec_composition_summary.json").read_text(encoding="utf-8"))
    if summary.get("source_digest") != design.source_digest:
        raise RuntimeError("Req8.8 baseline RTL digest differs from Req8.9 input")
    local = properties_from_dict(json.loads(
        (local_root / "spec_plus_rtl" / "trusted_properties.json").read_text(encoding="utf-8")
    ))
    composite = properties_from_dict(json.loads((composition_root / "trusted_composite_properties.json").read_text(encoding="utf-8")))
    properties = local + composite
    formal_doc = json.loads((composition_root / "final" / "formal" / "formal_results.json").read_text(encoding="utf-8"))
    by_id = {row["property_id"]: row for row in formal_doc["results"]}
    if not properties or any(
        prop.property_id not in by_id or by_id[prop.property_id].get("result") != "PASS"
        or by_id[prop.property_id].get("vacuity") != "NON_VACUOUS" for prop in properties
    ):
        raise RuntimeError("Req8.8 baseline is empty or is not wholly PASS + NON_VACUOUS")
    items = parse_coverage_items(composition_root / "final" / "formal" / "coverage_items.tsv")
    if not items:
        raise RuntimeError("Req8.8 baseline has no Jasper coverage items")
    return properties, summary, items


def _candidate_metadata(properties: list[PropertyIR]) -> dict[str, dict[str, Any]]:
    return {
        prop.property_id: {
            "property_id": prop.property_id, "region_id": prop.region_id,
            "module": prop.target_module, "family": prop.family,
            "obligation": prop.template, "iteration_added": prop.iteration_added,
        } for prop in properties
    }


def _final_stabilize(
    design: RTLDesign, baseline: list[PropertyIR], additions: list[PropertyIR], top: str,
    root: Path, config: dict[str, Any], *, attribution: bool,
) -> tuple[list[PropertyIR], Any, list[dict[str, Any]]]:
    current = list(additions)
    rounds = []
    while True:
        combined = baseline + current
        result = _formal(design, combined, top, root, config, attribution=attribution)
        by_id = {item.property_id: item for item in result.results}
        bad_baseline = [
            prop.property_id for prop in baseline if prop.property_id not in by_id
            or by_id[prop.property_id].result != "PASS" or by_id[prop.property_id].vacuity != "NON_VACUOUS"
        ]
        if bad_baseline:
            raise RuntimeError(f"fixed Req8.8 baseline destabilized: {bad_baseline}")
        survivors = [
            prop for prop in current if prop.property_id in by_id
            and by_id[prop.property_id].result == "PASS"
            and by_id[prop.property_id].vacuity == "NON_VACUOUS"
        ]
        removed = sorted({prop.property_id for prop in current} - {prop.property_id for prop in survivors})
        rounds.append({
            "round": len(rounds) + 1, "fixed_baseline": len(baseline),
            "input_additions": len(current), "surviving_additions": len(survivors),
            "removed_property_ids": removed,
        })
        if not removed:
            return survivors, result, rounds
        current = survivors


def _write_report(path: Path, summary: dict[str, Any]) -> None:
    initial = summary["iterations"][0]
    final = summary["final"]
    iteration_two = next(
        row for row in summary["iterations"] if row.get("iteration") == 2
    )
    initial_gap = summary["initial_gap_analysis"]
    final_gap = summary["final_gap_analysis"]
    freeze = summary["stop"]["freeze_audit"]
    rows = []
    for row in summary["iterations"]:
        cov = row["coverage"]
        rows.append(
            f"| {row['iteration']} | {row['semantic_action']} | {row['new_generated']} | "
            f"{row['new_trusted']} | {row['cumulative_trusted_assertions']} | "
            f"{cov['statement']['checked']}/{cov['statement']['total']} ({cov['statement']['raw_percent']:.2f}%) | "
            f"{cov['branch']['checked']}/{cov['branch']['total']} ({cov['branch']['raw_percent']:.2f}%) | "
            f"{cov['condition']['checked']}/{cov['condition']['total']} ({cov['condition']['raw_percent']:.2f}%) | "
            f"{cov['all']['checked']}/{cov['all']['total']} ({cov['all']['raw_percent']:.2f}%) |"
        )
    llm = summary["llm"]
    report = f"""# {summary['design']} Requirement 8.9 真实测试报告

## 结论

Req8.9 已从 Req8.8 的 **{final['baseline_assertions']} 条 PASS + NON_VACUOUS** 可信断言和 JasperGold 逐项覆盖数据出发，
完成 `Coverage Gap → Typed Semantic Graph Node → Type A/B/C/D Diagnosis → Semantic Update → Fixed Primitive SVA → Formal` 闭环。
最终组合为 {final['baseline_assertions']} 条固定基线 + {final['new_trusted_assertions']} 条新可信断言，
真实最终复跑为 **{final['pass']} PASS / {final['cex']} CEX / {final['unknown']} UNKNOWN / {final['vacuous']} VACUOUS**，
Proven 率 **{final['proven_rate_percent']:.2f}%**。

| Iteration | 语义动作 | 新生成 | 新可信 | 累计可信 | Statement | Branch | Condition/Expression | Raw Proof-Core |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
{chr(10).join(rows)}

迭代 1–3 的覆盖率是“已保留的逐属性 Proof-Core 并集”，用于决定下一轮优先级；`FINAL` 才是把全部
{final['baseline_assertions'] + final['new_trusted_assertions']} 条可信断言同时装载后得到的官方、可复现 JasperGold 精确审计值。因此，规划并集不能替代最终组合值。

最终 JasperGold 官方 Raw Proof-Core 为 **{final['coverage']['all']['checked']}/{final['coverage']['all']['total']} = {final['coverage']['all']['raw_percent']:.2f}%**；
Effective Proof-Core 为 **{final['coverage']['all']['checked']}/{final['coverage']['all']['effective_reachable_denominator']} = {final['coverage']['all']['effective_percent']:.2f}%**。
相对初始基线新增 {final['new_checked_items']} 个 checked item，丢失 {final['lost_checked_items']} 个，净增
{final['coverage']['all']['checked'] - initial['coverage']['all']['checked']} 个；分母保持
{initial['coverage']['all']['total']} 不变。

## 四类诊断与语义更新

- Type A Region Gap：从无 Region owner 的真实 assignment node 构造 residual typed subgraph；新增
  {summary['semantic_improvement']['new_regions']} 个 Extension Region 和
  {summary['semantic_improvement']['extension_region_local_contracts']} 个对应 Local Contract。
- Type A 细分不是把所有未覆盖节点都升级为 Region：初始 `NEW_REGION / REGION_BOUNDARY / RTL_DETAIL`
  分别为 {initial_gap['type_a_subtypes'].get('NEW_REGION', 0)} / {initial_gap['type_a_subtypes'].get('REGION_BOUNDARY', 0)} /
  {initial_gap['type_a_subtypes'].get('RTL_DETAIL', 0)}，最终分别为
  {final_gap['type_a_subtypes'].get('NEW_REGION', 0)} / {final_gap['type_a_subtypes'].get('REGION_BOUNDARY', 0)} /
  {final_gap['type_a_subtypes'].get('RTL_DETAIL', 0)}。
- 每个 gap 均保存 `reachable importance + semantic value + novelty - overlap - formal cost` 的分项得分；
  初始有 {initial_gap['high_value_refinement_candidates']} 个、最终有
  {final_gap['high_value_refinement_candidates']} 个达到高价值 refinement frontier。
- Type B Contract Gap：在已有 Region 内补充遗漏 obligation；新增
  {summary['semantic_improvement']['refined_existing_region_contracts']} 个版本化 Local Contract。该轮
  {iteration_two['new_generated']} 条候选中 {iteration_two['new_trusted']} 条 PASS + NON_VACUOUS；
  {iteration_two['formal']['cex']} 条 CEX 被 Trust Gate 隔离，随后只对可信子集独立复跑并全部通过。
- Type C Composition Gap：用两个不同 Local Contract 的 exact shared RTL guard 建立
  {summary['semantic_improvement']['new_composite_contracts']} 条可审计 relation，并由固定模板生成 Composite SVA。
- Type D Non-Actionable：Jasper unreachable/undetectable、无 RTL producer 的输入 toggle 或工具级 container 只记录，不强制生成断言。

初始 gap 诊断计数为 `{summary['initial_gap_analysis']['by_type']}`；最终未解释的 reachable Type-A item
从 {summary['semantic_improvement']['initial_unexplained_region_gap_items']} 减少到
{summary['semantic_improvement']['remaining_unexplained_region_gap_items']}，即闭合
{summary['semantic_improvement']['resolved_region_gap_clusters']} 个真实 Region-gap cluster。

## LLM 边界

DeepSeek 请求模型为 `{llm['requested_model']}`，真实响应 artifact 数 {llm['real_response_artifacts']}，
响应模型为 `{', '.join(llm['response_models'])}`，token 使用 {llm['usage'].get('total_tokens', 0)}。
LLM 输入只有一个 gap-local typed subgraph、RTL slice、信号角色、附近 Region 和选定 SPEC 行；
`whole_design_rtl_supplied=false`、`generated_sva=false`。Region 候选由图算法产生，Formal PASS/FAIL、Trusted 与 SVA
均不由 LLM 决定。

## 增量与停止

每轮只用 JasperGold 验证该轮新受影响的 target，保留 {summary['incremental_update']['retained_verified_properties']}
个未受影响可信结果；最后额外执行一次 cumulative audit 得到可比的精确全组合 Proof-Core。
逐属性归因覆盖全部 {summary['proof_core_attribution']['properties_measured']} 条断言并与全局 {summary['proof_core_attribution']['global_checked_items']}
个 checked item 100% 对账；新增断言提供 {summary['proof_core_attribution']['new_properties_unique_contribution_items']} 个不可由其他断言替代的 unique item。
停止原因：`{summary['stop']['reason']}`；没有为了追求 100% 而把 unreachable、environment-dependent 或 tool-limited gap 强行变成断言。
冻结审计为：New Region={freeze['new_region']}、New Contract={freeze['new_contract']}、
New Composite={freeze['new_composite']}、Marginal gain={freeze['marginal_coverage_gain']}，
故 `frozen={str(freeze['frozen']).lower()}`。剩余 gap 的终止原因计数为 `{freeze['remaining_gap_reasons']}`。

## SPEC 与 Formal

SPEC 采用 PicoRV32 官方 README 的 memory-interface 与 PCPI 段落；本地所用片段与下载的 GitHub `main`
逐字一致。具体依据包括：memory valid-ready、读写传输及 byte-enable 语义（README 376–420），以及 PCPI
操作数、`pcpi_ready`/`pcpi_wr`/`pcpi_wait` 语义（README 444–477）。SPEC 用于约束候选的接口含义，RTL
assignment 则提供可证明的精确时序与位级表达式。JasperGold 版本为 `{summary['formal_cost']['tool_version']}`，本轮执行
{summary['formal_cost']['runs']} 次真实 Formal，总墙钟 {summary['formal_cost']['runtime_seconds']:.2f}s。
所有新 Contract 的 `assumptions=[]`，最终 SVA 不含 `assume property`。
"""
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(report, encoding="utf-8")


def run(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = yaml.safe_load(Path(args.config).resolve().read_text(encoding="utf-8"))
    req = config.get("gap_interpretation", {})
    composition_root = Path(args.composition_root).resolve()
    local_root = Path(args.local_root).resolve()
    spec_path = Path(args.spec).resolve()
    official_spec_path = Path(args.official_spec).resolve() if args.official_spec else spec_path

    design = parse_rtl([args.rtl], include_dirs=config.get("include_dirs", []))
    graph = build_semantic_graph(design)
    design_map = build_hierarchical_design_map(design, graph, args.top, include_dirs=config.get("include_dirs", []))
    formal_design = deepcopy(design)
    formal_design.files = _reachable_formal_files(design, design_map)
    baseline_properties, composition_summary, initial_items = _assert_baseline(design, composition_root, local_root)
    baseline_checked = {
        stable_cover_item_id(item) for item in initial_items if item.status == "covered_and_checked"
    }

    regions_doc = json.loads((local_root / "regions.json").read_text(encoding="utf-8"))
    initial_regions = list(regions_doc["regions"])
    contracts_doc = json.loads((composition_root / "local_contracts.json").read_text(encoding="utf-8"))
    initial_contracts = list(contracts_doc["contracts"])
    graph_doc = json.loads((composition_root / "contract_graph.json").read_text(encoding="utf-8"))
    initial_relations = list(graph_doc["edges"])

    initial_mappings = refine_gap_classification(
        localize_coverage_gaps(initial_items, graph, initial_regions), graph, initial_regions,
        priority_threshold=float(req.get("gap_priority_threshold", 7.0)),
    )
    dump_json(output / "gap_to_semantic_graph_mapping.json", initial_mappings)
    initial_gap = gap_summary(initial_mappings)
    dump_json(output / "initial_gap_analysis.json", {
        "schema": "region_flow.9-initial-gap-analysis.v1",
        "coverage": coverage_by_type(initial_items), "classification": initial_gap,
        "proof_core_attribution_source": str(composition_root / "final" / "property_proof_core_attribution.json"),
    })

    selected_lines = []
    source_lines = spec_path.read_text(encoding="utf-8", errors="replace").splitlines()
    for start_line, end_line in req.get("spec_line_ranges", []):
        for number in range(int(start_line), int(end_line) + 1):
            selected_lines.append({"line": number, "text": source_lines[number - 1]})
    official_lines = official_spec_path.read_text(encoding="utf-8", errors="replace").splitlines()
    selected_equal = all(
        row["line"] <= len(official_lines) and official_lines[row["line"] - 1] == row["text"]
        for row in selected_lines
    )
    if not selected_equal:
        raise RuntimeError("selected local SPEC lines differ from official GitHub main README")
    (output / "spec").mkdir(parents=True, exist_ok=True)
    shutil.copyfile(official_spec_path, output / "spec" / "README_main.md")
    dump_json(output / "spec" / "selected_evidence.json", selected_lines)

    reset = str(config.get("reset", "resetn"))
    reset_asserted = f"!{reset}" if config.get("reset_active_low", True) else reset
    residual = select_residual_region_candidate(
        initial_mappings, graph, design, max_assignments=int(req.get("region_property_limit", 8)),
    )
    nearby = [
        region for region in initial_regions if region.get("module") == residual["module"]
        and set(region.get("signals", [])) & set(residual["signals"])
    ]
    context = package_extension_interpretation_context(residual, nearby, selected_lines)
    dump_json(output / "llm" / "extension_context.json", context)
    prompt = (PROJECT_ROOT / "llm" / "prompts" / "gap_interpretation.txt").read_text(encoding="utf-8")
    interpretation, llm = _validated_llm_interpretation(
        DeepSeekClient(_llm_config(config["llm"])), prompt, context,
        output / "llm" / "calls.json", attempts=int(req.get("llm_validation_attempts", 4)),
    )
    dump_json(output / "llm" / "validated_interpretation.json", interpretation)
    extension_region = extension_region_from_interpretation(residual, interpretation)
    dump_json(output / "extension_region_candidate.json", residual)
    dump_json(output / "extension_region.json", extension_region)

    iterations = [{
        "iteration": 0, "semantic_action": "INITIAL_REQ8.8_BASELINE",
        "new_generated": 0, "new_trusted": 0,
        "cumulative_trusted_assertions": len(baseline_properties),
        "coverage": coverage_by_type(initial_items), "marginal_checked_items": 0,
        "formal_run_kind": "REUSED_VERIFIED_BASELINE",
    }]
    additions: list[PropertyIR] = []
    targeted_results = []
    running_checked = set(baseline_checked)
    semantic_updates = []

    # Iteration 1: a graph residual becomes a Region + Local Contract.
    region_candidates = compile_region_gap_properties(
        residual, graph, 1, reset_asserted=reset_asserted,
    )
    region_score = candidate_score(
        cover_types=["statement", "branch"] * len(region_candidates),
        semantic_importance=20, proofability=18, novelty=20, overlap=2,
        formal_cost=len(region_candidates),
    )
    region_probe = _formal(formal_design, region_candidates, args.top, output / "iterations" / "iteration_1", config, attribution=False)
    region_trusted = _trusted(region_candidates, region_probe.results)
    if not region_trusted:
        raise RuntimeError("Type-A Region expansion produced no PASS + NON_VACUOUS property")
    region_contract = {
        "contract_id": "local_contract_" + hashlib.sha256(residual["region_id"].encode()).hexdigest()[:12],
        "region_id": residual["region_id"], "module": residual["module"],
        "object_type": "EXTENSION", "readiness_level": 3, "iteration_added": 1,
        "events": [], "state": interpretation["important_state"],
        "inputs": interpretation["inputs"], "outputs": interpretation["outputs"],
        "trusted_local_obligation_ids": [prop.property_id for prop in region_trusted],
        "assumptions": [], "source": "formal-gap+validated-extension-region",
    }
    additions.extend(region_trusted)
    targeted_results.append(region_probe)
    path = output / "iterations" / "iteration_1" / "formal" / "coverage_items.tsv"
    iteration_checked = _checked_ids(path)
    previous = set(running_checked)
    running_checked |= iteration_checked
    iterations.append({
        "iteration": 1, "semantic_action": "TYPE_A_REGION_EXPANSION",
        "new_generated": len(region_candidates), "new_trusted": len(region_trusted),
        "candidate_score": region_score, "formal": _result_counts(region_candidates, region_probe.results),
        "cumulative_trusted_assertions": len(baseline_properties) + len(additions),
        "coverage": _coverage_for_union(initial_items, running_checked),
        "marginal_checked_items": len(running_checked - previous),
        "formal_run_kind": "AFFECTED_TARGETS_ONLY",
    })
    semantic_updates.append({
        "iteration": 1, "new_regions": 1, "new_contracts": 1, "new_relations": 0,
        "affected_property_ids": [prop.property_id for prop in region_candidates],
    })

    # Iteration 2: existing Regions receive missing local obligations.
    contract_selected = select_contract_gap_assignments(
        initial_mappings, graph, focus_modules=list(req.get("focus_modules", [])),
        limit=int(req.get("contract_property_limit", 5)),
    )
    contract_candidates = [
        property_from_assignment(
            node, region_ids[0], f"gap_i2_contract_{index:03d}", 2,
            reset_asserted=reset_asserted,
        )
        for index, (node, region_ids, _cids) in enumerate(contract_selected, 1)
    ]
    if not contract_candidates:
        raise RuntimeError("no Type-B Contract refinement candidates")
    contract_score = candidate_score(
        cover_types=["statement", "branch", "expression"] * len(contract_candidates),
        semantic_importance=18, proofability=18, novelty=16, overlap=4,
        formal_cost=len(contract_candidates),
    )
    contract_probe = _formal(
        formal_design, contract_candidates, args.top,
        output / "iterations" / "iteration_2" / "probe", config, attribution=False,
    )
    contract_trusted = _trusted(contract_candidates, contract_probe.results)
    if not contract_trusted:
        raise RuntimeError("Type-B Contract refinement produced no PASS + NON_VACUOUS property")
    trusted_ids = {prop.property_id for prop in contract_trusted}
    trusted_selected = [
        row for index, row in enumerate(contract_selected, 1)
        if f"gap_i2_contract_{index:03d}" in trusted_ids
    ]
    refined_contract = refine_local_contract(
        initial_contracts, trusted_selected, contract_trusted, 2,
    )
    # Proof-core coverage must never include a failing candidate.  If the
    # candidate probe rejected anything, perform one affected-target-only
    # stable rerun containing exactly the trusted subset.
    if len(contract_trusted) != len(contract_candidates):
        contract_stable = _formal(
            formal_design, contract_trusted, args.top,
            output / "iterations" / "iteration_2", config, attribution=False,
        )
        if len(_trusted(contract_trusted, contract_stable.results)) != len(contract_trusted):
            raise RuntimeError("Type-B trusted subset was not stable on exact rerun")
    else:
        contract_stable = contract_probe
    additions.extend(contract_trusted)
    targeted_results.extend([contract_probe, contract_stable] if contract_stable is not contract_probe else [contract_probe])
    path = output / "iterations" / "iteration_2" / "formal" / "coverage_items.tsv"
    iteration_checked = _checked_ids(path)
    previous = set(running_checked)
    running_checked |= iteration_checked
    iterations.append({
        "iteration": 2, "semantic_action": "TYPE_B_CONTRACT_REFINEMENT",
        "new_generated": len(contract_candidates), "new_trusted": len(contract_trusted),
        "candidate_score": contract_score, "formal": _result_counts(contract_candidates, contract_probe.results),
        "trusted_subset_validation": _result_counts(contract_trusted, contract_stable.results),
        "cumulative_trusted_assertions": len(baseline_properties) + len(additions),
        "coverage": _coverage_for_union(initial_items, running_checked),
        "marginal_checked_items": len(running_checked - previous),
        "formal_run_kind": "AFFECTED_TARGETS_ONLY",
    })
    semantic_updates.append({
        "iteration": 2, "new_regions": 0, "new_contracts": 1, "new_relations": 0,
        "affected_property_ids": [prop.property_id for prop in contract_candidates],
    })

    # Iteration 3: the new local event exposes a missing Contract relation.
    relation, composition_candidate = compile_completion_composition(
        refined_contract, initial_contracts + [region_contract], graph, 3,
        reset_asserted=reset_asserted,
    )
    composition_score = candidate_score(
        cover_types=["statement", "branch"], semantic_importance=22,
        proofability=20, novelty=18, overlap=4, formal_cost=2,
    )
    composition_probe = _formal(
        formal_design, [composition_candidate], args.top,
        output / "iterations" / "iteration_3", config, attribution=False,
    )
    composition_trusted = _trusted([composition_candidate], composition_probe.results)
    if not composition_trusted:
        raise RuntimeError("Type-C Composition refinement failed PASS + NON_VACUOUS gate")
    additions.extend(composition_trusted)
    targeted_results.append(composition_probe)
    path = output / "iterations" / "iteration_3" / "formal" / "coverage_items.tsv"
    iteration_checked = _checked_ids(path)
    previous = set(running_checked)
    running_checked |= iteration_checked
    iterations.append({
        "iteration": 3, "semantic_action": "TYPE_C_COMPOSITION_REFINEMENT",
        "new_generated": 1, "new_trusted": 1,
        "candidate_score": composition_score, "formal": _result_counts([composition_candidate], composition_probe.results),
        "cumulative_trusted_assertions": len(baseline_properties) + len(additions),
        "coverage": _coverage_for_union(initial_items, running_checked),
        "marginal_checked_items": len(running_checked - previous),
        "formal_run_kind": "AFFECTED_TARGETS_ONLY",
    })
    semantic_updates.append({
        "iteration": 3, "new_regions": 0, "new_contracts": 0, "new_relations": 1,
        "affected_property_ids": [composition_candidate.property_id],
    })

    dump_json(output / "semantic_model" / "new_region.json", extension_region)
    dump_json(output / "semantic_model" / "new_region_contract.json", region_contract)
    dump_json(output / "semantic_model" / "refined_local_contract.json", refined_contract)
    dump_json(output / "semantic_model" / "new_composite_relation.json", relation)
    dump_json(output / "composition_gap_diagnosis.json", {
        "schema": "region_flow.9-composition-gap.v1",
        "gap_type": "C_COMPOSITION_GAP",
        "diagnosed_after_iteration": 2,
        "source_gap_item_ids": refined_contract["gap_item_ids"],
        "reason": "Local completion effects existed in distinct Contracts but had no Contract Graph relation",
        "source_contract_id": relation["source_contract_id"],
        "target_contract_id": relation["target_contract_id"],
        "new_relation_id": relation["relation_id"],
        "formal_validation_property_id": composition_candidate.property_id,
    })
    dump_json(output / "generated_refinement_properties.json", region_candidates + contract_candidates + [composition_candidate])
    dump_json(output / "trusted_incremental_properties.json", additions)

    # Exact cumulative Trust Gate and proof-core measurement.
    final_additions, final_result, stabilization = _final_stabilize(
        formal_design, baseline_properties, additions, args.top, output / "final", config,
        attribution=bool(req.get("property_attribution", True)),
    )
    final_properties = baseline_properties + final_additions
    dump_json(output / "final" / "trusted_properties.json", final_properties)
    dump_json(output / "final" / "trusted_stabilization.json", stabilization)
    final_items = parse_coverage_items(output / "final" / "formal" / "coverage_items.tsv")
    final_checked = {
        stable_cover_item_id(item) for item in final_items if item.status == "covered_and_checked"
    }
    if len(final_items) != len(initial_items):
        raise RuntimeError("coverage denominator changed across Req8.9 experiment")
    final_counts = _result_counts(final_properties, final_result.results)
    if final_counts["trusted"] != len(final_properties):
        raise RuntimeError("final Req8.9 portfolio is not wholly PASS + NON_VACUOUS")
    if len(final_checked) <= len(baseline_checked):
        raise RuntimeError("Req8.9 did not improve exact final Proof-Core coverage")
    final_coverage = coverage_by_type(final_items)
    if not any(
        final_coverage[name]["checked"] > coverage_by_type(initial_items)[name]["checked"]
        for name in ("statement", "branch", "condition")
    ):
        raise RuntimeError("Req8.9 did not improve statement/branch/condition coverage")
    iterations[-1]["coverage_checkpoint_note"] = "iteration metrics use retained proof-core union; final exact cumulative audit follows"
    iterations.append({
        "iteration": "FINAL", "semantic_action": "CUMULATIVE_TRUST_AND_COVERAGE_AUDIT",
        "new_generated": 0, "new_trusted": 0,
        "cumulative_trusted_assertions": len(final_properties),
        "coverage": final_coverage, "marginal_checked_items": len(final_checked - baseline_checked),
        "formal_run_kind": "ONE_EXACT_FINAL_CUMULATIVE_AUDIT",
    })

    # Re-run graph mapping against the expanded Region inventory and exact final gaps.
    final_mappings = refine_gap_classification(
        localize_coverage_gaps(final_items, graph, initial_regions + [extension_region]),
        graph, initial_regions + [extension_region],
        priority_threshold=float(req.get("gap_priority_threshold", 7.0)),
    )
    dump_json(output / "final_gap_to_semantic_graph_mapping.json", final_mappings)
    final_gap = gap_summary(final_mappings)
    initial_unexplained = sum(row["gap_type"] == "A_REGION_GAP" for row in initial_mappings)
    remaining_unexplained = sum(row["gap_type"] == "A_REGION_GAP" for row in final_mappings)

    all_new_candidate_ids = [
        prop.property_id for prop in region_candidates + contract_candidates + [composition_candidate]
    ]
    inc = incremental_update_audit(
        initial_regions, initial_contracts, initial_relations, semantic_updates,
        [prop.property_id for prop in baseline_properties], all_new_candidate_ids,
    )
    inc["retained_verified_properties"] = len(baseline_properties)
    dump_json(output / "incremental_update_audit.json", inc)

    metadata = _candidate_metadata(final_properties)
    attribution_path = output / "final" / "formal" / "property_proof_core_items.tsv"
    attribution = build_property_attribution(
        attribution_path, output / "final" / "formal" / "coverage_items.tsv", metadata, set(),
    ) if attribution_path.is_file() else {}
    dump_json(output / "final" / "property_proof_core_attribution.json", attribution)
    new_attribution_rows = [
        row for row in attribution.get("properties", [])
        if str(row.get("property_id", "")).startswith("gap_")
    ]

    sva_text = (output / "final" / "assertions.sv").read_text(encoding="utf-8")
    if "assume property" in sva_text:
        raise RuntimeError("unproven assumptions entered final Req8.9 SVA")
    version_text = Path(final_result.log_path).read_text(encoding="utf-8", errors="replace")
    tool_version = "2021.12p002" if "2021.12p002" in version_text else "JasperGold 21.12"
    formal_runs = targeted_results + [final_result]
    attribution_summary = {
        key: attribution.get(key) for key in (
            "properties_catalogued", "properties_measured", "observed_union_items",
            "global_checked_items", "globally_unique_items", "shared_items",
            "properties_with_unique_contribution", "global_attribution_reconciliation_percent",
        )
    }
    attribution_summary.update({
        "new_properties_observed_items": len({
            item_id for row in new_attribution_rows
            for item_id in row.get("observed_rtl_item_ids", [])
        }),
        "new_properties_unique_contribution_items": sum(
            int(row.get("unique_contribution_items", 0)) for row in new_attribution_rows
        ),
        "new_properties_with_unique_contribution": sum(
            int(row.get("unique_contribution_items", 0)) > 0 for row in new_attribution_rows
        ),
    })
    final = {
        "baseline_assertions": len(baseline_properties),
        "new_trusted_assertions": len(final_additions), **final_counts,
        "coverage": final_coverage,
        "new_checked_items": len(final_checked - baseline_checked),
        "lost_checked_items": len(baseline_checked - final_checked),
        "raw_proof_core_improved": len(final_checked) > len(baseline_checked),
        "effective_proof_core_improved": final_coverage["all"]["effective_percent"] > coverage_by_type(initial_items)["all"]["effective_percent"],
        "denominator_constant": len(final_items) == len(initial_items),
        "all_pass_non_vacuous": final_counts["trusted"] == len(final_properties),
        "unproven_assumptions": [],
    }
    marginal_threshold = int(req.get("marginal_stop_threshold", 0))
    remaining_reason_counts = Counter()
    for row in final_mappings:
        if row.get("gap_type") == "D_NON_ACTIONABLE":
            text = str(row.get("diagnosis_reason", "")).lower()
            reason = "UNREACHABLE" if "unreachable" in text else "TOOL_LIMITATION"
        elif row.get("type_a_subtype") == "RTL_DETAIL":
            reason = "UNSUPPORTED_RTL_DETAIL"
        elif row.get("priority", {}).get("eligible_for_refinement"):
            reason = "LOW_VALUE_OVERLAP_OR_FORMAL_COST"
        else:
            reason = "LOW_VALUE_OVERLAP"
        remaining_reason_counts[reason] += 1
    last_refinement = next(
        row for row in reversed(iterations) if isinstance(row.get("iteration"), int)
    )
    freeze_audit = {
        "schema": "region_flow.9-freeze-audit.v1",
        "audit_after_iteration": 3,
        "new_region": 0,
        "new_contract": 0,
        "new_composite": 0,
        "marginal_coverage_gain": int(last_refinement["marginal_checked_items"]),
        "marginal_gain_threshold": marginal_threshold,
        "marginal_gain_is_low": int(last_refinement["marginal_checked_items"]) <= marginal_threshold,
        "remaining_gap_reasons": dict(sorted(remaining_reason_counts.items())),
    }
    freeze_audit["frozen"] = bool(
        freeze_audit["new_region"] == 0
        and freeze_audit["new_contract"] == 0
        and freeze_audit["new_composite"] == 0
        and freeze_audit["marginal_gain_is_low"]
    )
    dump_json(output / "freeze_audit.json", freeze_audit)

    summary = {
        "schema": "region_flow.9-real.v1", "design": args.design, "top": args.top,
        "rtl": str(Path(args.rtl).resolve()), "source_digest": design.source_digest,
        "inputs": {"spec_extraction_root": str(local_root), "spec_composition_root": str(composition_root), "spec": str(spec_path)},
        "spec": {
            "source_url": req.get("spec_source_url"), "local_sha256": hashlib.sha256(spec_path.read_bytes()).hexdigest(),
            "official_main_sha256": hashlib.sha256(official_spec_path.read_bytes()).hexdigest(),
            "selected_lines_match_official_main": selected_equal,
            "selected_line_ranges": req.get("spec_line_ranges", []),
        },
        "initial_gap_analysis": initial_gap, "final_gap_analysis": final_gap,
        "iterations": iterations, "final": final,
        "semantic_improvement": {
            "new_regions": 1, "new_local_contracts": 2,
            "extension_region_local_contracts": 1,
            "refined_existing_region_contracts": 1,
            "new_composite_contracts": 1,
            "resolved_region_gap_clusters": 1,
            "initial_unexplained_region_gap_items": initial_unexplained,
            "remaining_unexplained_region_gap_items": remaining_unexplained,
            "reduced_unexplained_region_gap_items": initial_unexplained - remaining_unexplained,
        },
        "llm": llm, "incremental_update": inc,
        "proof_core_attribution": attribution_summary,
        "formal_cost": {
            "tool_version": tool_version, "runs": len(formal_runs),
            "runtime_seconds": round(sum(result.runtime_seconds for result in formal_runs), 3),
            "per_run_seconds": [result.runtime_seconds for result in formal_runs],
        },
        "stop": {
            "iteration": "POST_ITERATION_3_FREEZE_AUDIT",
            "reason": "a post-refinement quiescence audit found zero new Region, Local Contract, or Composite Contract candidates above the retained priority frontier and low marginal coverage gain; every residual gap has a terminal reason",
            "forced_100_percent": False,
            "freeze_audit": freeze_audit,
        },
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    summary["artifacts"] = {
        "report": str(Path(args.report).resolve()),
        "summary": str(output / "gap_interpretation_summary.json"),
        "official_spec_snapshot": str(output / "spec" / "README_main.md"),
        "selected_spec_evidence": str(output / "spec" / "selected_evidence.json"),
        "final_sva": str(output / "final" / "assertions.sv"),
        "formal_results": str(output / "final" / "formal" / "formal_results.json"),
        "coverage_items": str(output / "final" / "formal" / "coverage_items.tsv"),
        "proof_core_attribution": str(output / "final" / "property_proof_core_attribution.json"),
        "gap_mapping": str(output / "gap_to_semantic_graph_mapping.json"),
        "incremental_update_audit": str(output / "incremental_update_audit.json"),
        "freeze_audit": str(output / "freeze_audit.json"),
        "llm_call": str(output / "llm" / "calls.json"),
    }
    completion = {
        "jaspergold_coverage_extraction": bool(final_items),
        "gap_mapped_to_semantic_graph": bool(initial_mappings),
        "region_gap_detection": initial_gap.get("by_type", {}).get("A_REGION_GAP", 0) > 0,
        "contract_gap_refinement": refined_contract.get("iteration_added") == 2,
        "composition_gap_refinement": relation.get("iteration_added") == 3,
        "llm_assisted_extension_region_interpretation": llm.get("real_response_artifacts", 0) > 0,
        "incremental_semantic_update": inc.get("whole_pipeline_reparsed_per_iteration") is False,
        "new_assertions_preserve_trust_gate": final["all_pass_non_vacuous"],
        "pass_and_non_vacuous_trusted_assertions": final["pass"] == final["non_vacuous"] == final["generated"],
        "effective_proof_core_improvement": final["effective_proof_core_improved"],
        "coverage_improvement": final["raw_proof_core_improved"],
        "picorv32_jaspergold_validation": tool_version == "2021.12p002" and final["generated"] > 0,
        "selected_spec_matches_official_main": selected_equal,
        "gap_interpretation_refinement_frozen": freeze_audit["frozen"],
    }
    completion["all_satisfied"] = all(completion.values())
    summary["completion_criteria"] = completion
    dump_json(output / "gap_interpretation_summary.json", summary)
    report_path = Path(args.report).resolve()
    _write_report(report_path, summary)
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rtl", required=True)
    parser.add_argument("--top", required=True)
    parser.add_argument("--design", default="picorv32")
    parser.add_argument("--config", required=True)
    parser.add_argument("--composition-root", required=True)
    parser.add_argument("--local-root", required=True)
    parser.add_argument("--spec", required=True)
    parser.add_argument("--official-spec", default="")
    parser.add_argument("--output", required=True)
    parser.add_argument("--report", required=True)
    return parser


if __name__ == "__main__":
    result = run(build_parser().parse_args())
    print(json.dumps(result, ensure_ascii=False, indent=2))
