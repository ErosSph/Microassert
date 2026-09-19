"""Requirement 8.7: SPEC/RTL-guided Local Region and assertion expansion."""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import time
from typing import Any, Callable

import yaml

from dateassertion.coverage_analysis.proof_core import coverage_item_summary, parse_coverage_items
from dateassertion.coverage_analysis.property_attribution import build_property_attribution
from dateassertion.generators.sva_generator import generate_sva
from dateassertion.ir.schema import FormalPropertyResult, PropertyIR, dump_json
from dateassertion.llm.client import DeepSeekClient, LLMError
from dateassertion.pipeline.contract_validation import _llm_config
from dateassertion.pipeline.local_region_assertions import (
    Requirement87ValidationError,
    build_local_obligation_matrix,
    build_region_inventory,
    candidate_inventory,
    compile_rtl_properties,
    compile_spec_properties,
    enumerate_local_candidate_bindings,
    extension_region_from_response,
    map_spec_behaviors_to_regions,
    package_extension_context,
    package_spec_context,
    region_participation,
    result_counts,
    select_local_candidate_bindings,
    spec_lines,
    validate_extension_response,
    validate_spec_response,
)
from dateassertion.pipeline.property_portfolio_planner import build_property_candidate_pool
from dateassertion.pipeline.region_flow import _reachable_formal_files, _run_formal
from dateassertion.rtl_frontend.hierarchical_design import build_hierarchical_design_map
from dateassertion.rtl_frontend.parser import RTLDesign, parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph
from dateassertion.pipeline.semantic_slicing import build_verification_regions


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def _safe_llm_metadata(metadata: dict[str, Any]) -> dict[str, Any]:
    return {key: value for key, value in metadata.items() if key != "raw_content"}


def _usage_counter(records: list[dict[str, Any]]) -> Counter[str]:
    """Accumulate scalar usage fields; providers may add nested detail maps."""

    usage: Counter[str] = Counter()
    for record in records:
        for key, value in record.get("metadata", {}).get("usage", {}).items():
            if isinstance(value, (int, float)) and not isinstance(value, bool):
                usage[str(key)] += value
    return usage


def _context_digest(context: dict[str, Any]) -> str:
    return hashlib.sha256(
        json.dumps(context, sort_keys=True, ensure_ascii=False).encode("utf-8")
    ).hexdigest()


def _validated_llm_call(
    client: DeepSeekClient, prompt: str, context: dict[str, Any],
    validator: Callable[[dict[str, Any]], dict[str, Any]], *, attempts: int,
    records_path: Path | None = None,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    records = []
    error = ""
    for attempt in range(1, attempts + 1):
        payload: dict[str, Any] = context
        if error:
            payload = {
                "context": context,
                "previous_validation_error": error,
                "instruction": "Return a complete corrected JSON object using only the supplied context.",
            }
        response, metadata = client.complete_json(prompt, json.dumps(payload, ensure_ascii=False))
        record = {
            "attempt": attempt,
            "context_sha256": _context_digest(context),
            "response": response,
            "metadata": _safe_llm_metadata(metadata),
        }
        try:
            validated = validator(response)
        except (Requirement87ValidationError, ValueError) as exc:
            error = str(exc)
            record["validation_error"] = error
            records.append(record)
            if records_path:
                dump_json(records_path, records)
            continue
        records.append(record)
        if records_path:
            dump_json(records_path, records)
        return validated, records
    raise Requirement87ValidationError(error or "LLM response did not pass validation")


def _discover_extensions(
    regions: dict[str, Any], design: RTLDesign, spec_evidence: list[dict[str, Any]],
    client: DeepSeekClient, prompt: str, output: Path, *, limit: int, attempts: int,
) -> tuple[list[dict[str, Any]], dict[str, Any]]:
    prior_records = []
    calls_path = output / "calls.json"
    if calls_path.is_file():
        prior_records = json.loads(calls_path.read_text(encoding="utf-8"))
    candidates = [
        item for item in regions.get("regions", [])
        if item.get("kind") != "MODULE" and item.get("detection_status") == "AMBIGUOUS"
    ]
    # Ambiguity explicitly marked as requiring semantic disambiguation is a
    # better use of the bounded LLM budget than a merely low-confidence form
    # of an otherwise known Core pattern. This ranking is graph-feature based
    # and contains no design, module, or signal-name special case.
    def ambiguity_rank(item: dict[str, Any]) -> tuple[int, float, str]:
        features = {
            str(feature.get("feature", ""))
            for feature in item.get("matched_features", [])
        }
        needs_semantics = any(
            "requires_semantic_disambiguation" in feature for feature in features
        )
        return (-int(needs_semantics), -float(item.get("score", 0.0)), str(item["region_id"]))

    candidates.sort(key=ambiguity_rank)
    extensions = []
    call_records = []
    cache_hits = 0
    api_calls_this_run = 0
    for region in candidates[:limit]:
        context = package_extension_context(region, design, spec_evidence)
        dump_json(output / "contexts" / f"{region['region_id']}.json", context)
        context_sha = _context_digest(context)
        cached = next((
            item for item in reversed(prior_records)
            if item.get("region_id") == region["region_id"]
            and item.get("context_sha256") == context_sha
            and not item.get("validation_error")
        ), None)
        if cached:
            validated = validate_extension_response(cached["response"], context)
            records = [{**deepcopy(cached), "cache_hit": True}]
            cache_hits += 1
        else:
            validated, records = _validated_llm_call(
                client, prompt, context,
                lambda response, supplied=context: validate_extension_response(response, supplied),
                attempts=attempts,
            )
            api_calls_this_run += len(records)
        for record in records:
            record["region_id"] = region["region_id"]
        call_records.extend(records)
        extension = extension_region_from_response(region, validated, _context_digest(context))
        if extension:
            extensions.append(extension)
    dump_json(output / "calls.json", call_records)
    return extensions, {
        "candidate_regions": len(candidates),
        "selected_local_slices": min(limit, len(candidates)),
        "calls": len(call_records),
        "api_calls_this_run": api_calls_this_run,
        "validated_cache_hits": cache_hits,
        "extension_regions": len(extensions),
        "whole_design_rtl_supplied": False,
        "usage": dict(_usage_counter(call_records)),
        "response_models": sorted({
            str(item["metadata"].get("response_model")) for item in call_records
            if item["metadata"].get("response_model")
        }),
    }


def _extract_spec(
    path: Path, lines: list[dict[str, Any]], design: RTLDesign, module: str,
    client: DeepSeekClient, prompt: str, output: Path, *, attempts: int,
    max_context_chars: int = 24_000,
) -> tuple[dict[str, Any], dict[str, Any]]:
    context = package_spec_context(path, lines, design, module)
    dump_json(output / "context.json", context)
    serialized_chars = len(json.dumps(context, ensure_ascii=False))
    if max_context_chars > 0 and serialized_chars > max_context_chars:
        chunks: list[list[dict[str, Any]]] = []
        current: list[dict[str, Any]] = []
        for line in lines:
            trial = current + [line]
            trial_context = package_spec_context(path, trial, design, module)
            if current and len(json.dumps(trial_context, ensure_ascii=False)) > max_context_chars:
                chunks.append(current)
                current = [line]
            else:
                current = trial
        if current:
            chunks.append(current)
        if len(chunks) < 2:
            raise RuntimeError(
                f"SPEC context exceeds {max_context_chars} characters but cannot be split by line"
            )

        merged_behaviors: list[dict[str, Any]] = []
        rejected_behaviors: list[dict[str, Any]] = []
        aggregate_records: list[dict[str, Any]] = []
        aggregate_usage: Counter[str] = Counter()
        response_models: set[str] = set()
        api_calls = 0
        cache_hits = 0
        for index, chunk in enumerate(chunks, 1):
            chunk_root = output / "chunks" / f"chunk_{index:03d}"
            document, metadata = _extract_spec(
                path, chunk, design, module, client, prompt, chunk_root,
                attempts=attempts, max_context_chars=0,
            )
            for raw in document.get("behaviors", []):
                copied = deepcopy(raw)
                copied["behavior_id"] = f"chunk_{index:03d}_{copied['behavior_id']}"
                copied["spec_chunk"] = index
                merged_behaviors.append(copied)
            for raw in document.get("rejected_behaviors", []):
                rejected_behaviors.append({"spec_chunk": index, **deepcopy(raw)})
            records_path = chunk_root / "calls.json"
            if records_path.is_file():
                for record in json.loads(records_path.read_text(encoding="utf-8")):
                    aggregate_records.append({"spec_chunk": index, **record})
            aggregate_usage.update(metadata.get("usage", {}))
            response_models.update(metadata.get("response_models", []))
            api_calls += int(metadata.get("api_calls_this_run", 0))
            cache_hits += int(bool(metadata.get("validated_cache_hit")))
        dump_json(output / "calls.json", aggregate_records)
        merged = {
            "schema": "region_flow.7-spec-behaviors.v1",
            "behaviors": merged_behaviors,
        }
        if rejected_behaviors:
            merged["rejected_behaviors"] = rejected_behaviors
        return merged, {
            "calls": len(aggregate_records),
            "api_calls_this_run": api_calls,
            "validated_cache_hit": cache_hits == len(chunks),
            "whole_design_rtl_supplied": False,
            "usage": dict(aggregate_usage),
            "response_models": sorted(response_models),
            "spec_source": str(path.resolve()),
            "spec_sha256": context["spec_sha256"],
            "supplied_line_count": len(lines),
            "chunked": True,
            "chunk_count": len(chunks),
            "max_context_chars": max_context_chars,
            "original_context_chars": serialized_chars,
        }
    calls_path = output / "calls.json"

    def isolate(response: dict[str, Any], aggregate_error: Exception) -> dict[str, Any]:
        # Do not weaken quote validation. If repeated correction leaves one bad
        # record in an otherwise useful response, validate each record with the
        # exact same gate and quarantine only the invalid extraction.
        accepted = []
        rejected = []
        for raw in response.get("behaviors", []) if isinstance(response, dict) else []:
            try:
                one = validate_spec_response({"behaviors": [raw]}, lines, design, module)
            except (Requirement87ValidationError, ValueError) as exc:
                rejected.append({"response": raw, "rejection_reason": str(exc)})
            else:
                accepted.extend(one["behaviors"])
        if not accepted:
            raise Requirement87ValidationError(
                f"no SPEC behavior survived exact-evidence isolation: {aggregate_error}"
            ) from aggregate_error
        return {
            "schema": "region_flow.7-spec-behaviors.v1",
            "behaviors": accepted,
            "rejected_behaviors": rejected,
            "aggregate_validation_error": str(aggregate_error),
        }

    current_context_digest = _context_digest(context)
    cached = None
    cached_validated = None
    cache_revalidated_for_current_context = False
    records = []
    if calls_path.is_file():
        records = json.loads(calls_path.read_text(encoding="utf-8"))

        def best_cached(candidates: list[dict[str, Any]]) -> tuple[dict[str, Any] | None, dict[str, Any] | None]:
            # Correction attempts are append-only.  A later reply can be less
            # useful than an earlier one (for example, every record in the
            # correction may reference a signal outside the checker module).
            # Revalidate every reply and retain the one with the most surviving
            # exact-evidence behaviors instead of blindly trusting the last.
            survivors = []
            for reverse_order, record in enumerate(reversed(candidates)):
                response = record.get("response")
                if not isinstance(response, dict):
                    continue
                try:
                    document = validate_spec_response(response, lines, design, module)
                except (Requirement87ValidationError, ValueError) as exc:
                    try:
                        document = isolate(response, exc)
                    except Requirement87ValidationError:
                        continue
                survivors.append((len(document.get("behaviors", [])), -reverse_order, record, document))
            if not survivors:
                return None, None
            _, _, record, document = max(survivors, key=lambda item: (item[0], item[1]))
            return record, document

        current_records = [
            record for record in records
            if record.get("context_sha256") == current_context_digest
        ]
        cached, cached_validated = best_cached(current_records)
        if cached is None and records:
            # A primitive-schema expansion can change the packaged context
            # without invalidating an older extraction. Never trust the old
            # hash directly: it must pass the full current validator above.
            older_records = [
                record for record in records
                if record.get("context_sha256") != current_context_digest
            ]
            cached, cached_validated = best_cached(older_records)
            cache_revalidated_for_current_context = cached is not None
    cache_hit = False
    if cached:
        validated = cached_validated
        cache_hit = True
    else:
        try:
            validated, records = _validated_llm_call(
                client, prompt, context,
                lambda response: validate_spec_response(response, lines, design, module),
                attempts=attempts,
                records_path=calls_path,
            )
        except (Requirement87ValidationError, LLMError) as aggregate_error:
            # A proxy/provider failure after one or more replies must not
            # discard already returned evidence. Reapply the exact
            # per-behavior validator to every reply for this context and keep
            # the strongest surviving extraction. No semantic gate is relaxed.
            records = (
                json.loads(calls_path.read_text(encoding="utf-8"))
                if calls_path.is_file() else []
            )
            isolated = []
            for record in records:
                if record.get("context_sha256") != _context_digest(context):
                    continue
                try:
                    candidate = isolate(record.get("response", {}), aggregate_error)
                except Requirement87ValidationError:
                    continue
                isolated.append(candidate)
            if not isolated:
                raise
            validated = max(isolated, key=lambda item: len(item.get("behaviors", [])))
    dump_json(output / "calls.json", records)
    usage = dict(_usage_counter(records))
    return validated, {
        "calls": len(records),
        "api_calls_this_run": 0 if cache_hit else len(records),
        "validated_cache_hit": cache_hit,
        "cache_revalidated_for_current_context": cache_revalidated_for_current_context,
        "whole_design_rtl_supplied": False,
        "usage": usage,
        "response_models": sorted({
            str(item["metadata"].get("response_model")) for item in records
            if item["metadata"].get("response_model")
        }),
        "spec_source": str(path.resolve()),
        "spec_sha256": context["spec_sha256"],
        "supplied_line_count": len(lines),
    }


def _trusted(properties: list[PropertyIR], results: list[FormalPropertyResult]) -> list[PropertyIR]:
    by_id = {item.property_id: item for item in results}
    return [
        item for item in properties
        if item.property_id in by_id
        and by_id[item.property_id].result == "PASS"
        and by_id[item.property_id].vacuity == "NON_VACUOUS"
    ]


def _formal(
    design: RTLDesign, properties: list[PropertyIR], top: str, root: Path,
    config: dict[str, Any], *, attribution: bool,
) -> Any:
    local_config = deepcopy(config)
    local_config.setdefault("formal", {})["property_attribution"] = attribution
    local_config["formal"]["attribution_time_limit"] = str(
        config.get("spec_extraction", {}).get("attribution_time_limit", "15s")
    )
    return _run_formal(
        design, properties, top, root / "formal", local_config, root / "assertions.sv"
    )


def _stabilize_trusted(
    design: RTLDesign, candidates: list[PropertyIR], top: str, root: Path,
    config: dict[str, Any], *, attribution: bool,
) -> tuple[list[PropertyIR], Any, list[dict[str, Any]], dict[str, FormalPropertyResult]]:
    """Monotonically shrink and rerun until the trusted set is stable.

    A solver result can move from PASS to UNKNOWN on a later multi-target run.
    Such a target must not remain in the reported Trusted portfolio.  Every
    reduction is therefore followed by a real rerun of the reduced set so the
    final proof core is measured on exactly the properties being reported.
    """

    current = list(candidates)
    rounds: list[dict[str, Any]] = []
    removed_results: dict[str, FormalPropertyResult] = {}
    if not current:
        raise RuntimeError("trusted stabilization received no candidate properties")
    while current:
        result = _formal(design, current, top, root, config, attribution=attribution)
        surviving = _trusted(current, result.results)
        rounds.append({
            "round": len(rounds) + 1,
            "input_properties": len(current),
            "pass_non_vacuous": len(surviving),
            "removed_property_ids": sorted(
                {item.property_id for item in current} - {item.property_id for item in surviving}
            ),
        })
        if len(surviving) == len(current):
            return surviving, result, rounds, removed_results
        surviving_ids = {item.property_id for item in surviving}
        removed_results.update({
            item.property_id: item for item in result.results
            if item.property_id not in surviving_ids
        })
        current = surviving
    raise RuntimeError("all properties were removed by the repeated Trusted gate")


def _stable_cover_ids(path: str | Path, status: str = "covered_and_checked") -> set[str]:
    result = set()
    for item in parse_coverage_items(path):
        if item.status != status:
            continue
        identity = "\x1f".join(str(value) for value in (
            item.file, item.line_start, item.column_start, item.line_end, item.column_end,
            item.cover_item_type, item.description, item.expression, item.module, item.instance,
        ))
        result.add("rtl_item_" + hashlib.sha256(identity.encode("utf-8")).hexdigest()[:20])
    return result


def _region_gap_audit(
    inventory: dict[str, Any], applicable: set[tuple[str, str]],
    metadata: dict[str, dict[str, Any]], trusted_ids: set[str],
) -> dict[str, Any]:
    """Explain Region-participation shortfalls without changing the gate."""

    all_ids = {str(item["region_id"]) for item in inventory.get("regions", [])}
    applicable_ids = {region_id for region_id, _ in applicable}
    generated_ids = {
        str(region_id)
        for item in metadata.values()
        for region_id in item.get("region_ids", [item.get("region_id")])
        if region_id
    }
    trusted_region_ids = {
        str(region_id)
        for property_id, item in metadata.items() if property_id in trusted_ids
        for region_id in item.get("region_ids", [item.get("region_id")])
        if region_id
    }
    return {
        "regions_without_applicable_graph_obligation": len(all_ids - applicable_ids),
        "applicable_regions_not_selected_under_budget": len(applicable_ids - generated_ids),
        "generated_regions_without_trusted_property": len(generated_ids - trusted_region_ids),
        "applicable_regions": len(applicable_ids),
        "generated_regions": len(generated_ids),
        "trusted_regions": len(trusted_region_ids),
    }


def _coverage(root: Path) -> dict[str, Any]:
    items = parse_coverage_items(root / "formal" / "coverage_items.tsv")
    return coverage_item_summary(items)


def _baseline(baseline_root: Path) -> dict[str, Any]:
    summary = json.loads((baseline_root / "region_flow_summary.json").read_text(encoding="utf-8"))
    regions = json.loads((baseline_root / "regions.json").read_text(encoding="utf-8"))
    properties = json.loads((baseline_root / "generated_properties.json").read_text(encoding="utf-8"))
    formal = json.loads((baseline_root / "formal_results.json").read_text(encoding="utf-8"))
    functional = {item["region_id"] for item in regions["regions"] if item.get("kind") != "MODULE"}
    participating = {item.get("region_id") for item in properties} & functional
    return {
        "name": "Req8.4 Local Baseline",
        "regions": len(functional),
        "core_regions": len(functional),
        "extension_regions": 0,
        "generated": len(properties),
        "trusted": sum(
            item.get("result") == "PASS" and item.get("vacuity") == "NON_VACUOUS"
            for item in formal.get("results", [])
        ),
        "pass": formal["summary"]["proven"],
        "cex": formal["summary"]["failed"],
        "unknown": formal["summary"]["unknown"] + formal["summary"].get("errors", 0),
        "vacuous": formal["summary"]["vacuous"],
        "proven_rate_percent": formal["summary"]["proven_rate"],
        "region_participation": {
            "total_regions": len(functional),
            "regions_with_trusted_assertion": len(participating),
            "coverage_percent": round(100 * len(participating) / len(functional), 2) if functional else 0.0,
        },
        "proof_core": summary["formal"]["proof_core_coverage"],
        "source_digest": RTLDesign.load(baseline_root / "zero_adaptation" / "rtl_structure.json").source_digest,
        "coverage_items": str(baseline_root / "formal" / "coverage_items.tsv"),
    }


def _write_report(path: Path, summary: dict[str, Any], spec_behaviors: list[dict[str, Any]]) -> None:
    base = summary["experiments"]["req8_4_baseline"]
    rtl = summary["experiments"]["spec_extraction_rtl_only"]
    combined = summary["experiments"]["spec_extraction_spec_plus_rtl"]
    region = summary["regions"]
    spec_rows = []
    for item in spec_behaviors:
        evidence = item["evidence"]
        spec_rows.append(
            f"| `{item['behavior_id']}` | {item.get('category')} | "
            f"{item.get('primitive') or '未编译'} | L{evidence['line_start']}-L{evidence['line_end']} | "
            f"{item.get('rtl_mapping', {}).get('status')} |"
        )
    spec_attribution_rows = [
        f"| `{item['property_id']}` | {item['obligation']} | "
        f"{item['observed_proof_core_items']} | {item['unique_contribution_items']} |"
        for item in summary.get("property_attribution", {}).get("spec_properties", [])
    ]
    remote = summary.get("spec", {}).get("remote_verification", {})
    remote_note = ""
    if remote:
        remote_note = (
            f"官方远端 `{remote.get('url', '')}` 的 SHA256 为 "
            f"`{remote.get('sha256', '')}`；实际送入 LLM 的配置行范围与远端"
            f"{'逐字符一致' if remote.get('selected_ranges_match') else '不一致'}。"
        )
    report = f"""# {summary['design']} Requirement 8.7 真实测试报告

## 结论

本次直接解析 `{summary['rtl']}`，读取用户指定的官方设计 SPEC，调用
DeepSeek `{summary['llm']['requested_model']}` 处理局部语义，并使用 JasperGold 21.12 做真实验证。
所有进入 Trusted 集合的属性在独立 Trusted-only 复跑中均为 **PASS + NON_VACUOUS**。

| 实验 | Region (Core/Extension) | Generated Local SVA | Final Trusted | Probe PASS/CEX/Unknown/Vacuous | Probe Proven率 | Region Participation | Raw Proof-Core |
|---|---:|---:|---:|---:|---:|---:|---:|
| Req8.4 baseline | {base['regions']} ({base['core_regions']}/0) | {base['generated']} | {base['trusted']} | {base['pass']}/{base['cex']}/{base['unknown']}/{base['vacuous']} | {base['proven_rate_percent']:.2f}% | {base['region_participation']['regions_with_trusted_assertion']}/{base['region_participation']['total_regions']} = {base['region_participation']['coverage_percent']:.2f}% | {base['proof_core']['covered_items']}/{base['proof_core']['total_items']} = {base['proof_core']['proof_core_coverage_percent']:.2f}% |
| Req8.7 RTL-only | {region['regions']} ({region['core_regions']}/{region['extension_regions']}) | {rtl['generated']} | {rtl['trusted']} | {rtl['pass']}/{rtl['cex']}/{rtl['unknown']}/{rtl['vacuous']} | {rtl['proven_rate_percent']:.2f}% | {rtl['region_participation']['regions_with_trusted_assertion']}/{rtl['region_participation']['total_regions']} = {rtl['region_participation']['coverage_percent']:.2f}% | {rtl['proof_core']['covered_items']}/{rtl['proof_core']['total_items']} = {rtl['proof_core']['proof_core_coverage_percent']:.2f}% |
| Req8.7 SPEC+RTL | {region['regions']} ({region['core_regions']}/{region['extension_regions']}) | {combined['generated']} | {combined['trusted']} | {combined['pass']}/{combined['cex']}/{combined['unknown']}/{combined['vacuous']} | {combined['proven_rate_percent']:.2f}% | {combined['region_participation']['regions_with_trusted_assertion']}/{combined['region_participation']['total_regions']} = {combined['region_participation']['coverage_percent']:.2f}% | {combined['proof_core']['covered_items']}/{combined['proof_core']['total_items']} = {combined['proof_core']['proof_core_coverage_percent']:.2f}% |

Trusted 集合采用单调收缩复跑：RTL-only 共 {len(rtl['trusted_stabilization'])} 轮，
SPEC+RTL 共 {len(combined['trusted_stabilization'])} 轮；最终 proof core 对应的正是表中 Trusted 集合。

Effective proof-core（排除 Jasper 标为 unreachable/undetectable 的项）：RTL-only 为
{rtl['effective_proof_core']['covered_and_checked']}/{rtl['effective_proof_core']['effective_reachable_denominator']}
= {rtl['effective_proof_core']['effective_reachable_coverage_percent']:.2f}%，SPEC+RTL 为
{combined['effective_proof_core']['covered_and_checked']}/{combined['effective_proof_core']['effective_reachable_denominator']}
= {combined['effective_proof_core']['effective_reachable_coverage_percent']:.2f}%。SPEC+RTL 相对 RTL-only
新增 {summary['proof_core_comparison']['spec_plus_rtl_unique_vs_rtl_only']} 个 checked RTL item。

Region Participation 的建议目标是 60%–80%，本次实际为
{combined['region_participation']['coverage_percent']:.2f}%。缺口审计显示：
{combined['region_gap_audit']['regions_without_applicable_graph_obligation']} 个 Region 没有可由现有
generic primitive 编译的图结构 obligation，
{combined['region_gap_audit']['applicable_regions_not_selected_under_budget']} 个有候选但未在预算内入选，
{combined['region_gap_audit']['generated_regions_without_trusted_property']} 个已有生成属性的 Region
最终没有属性通过严格 Trust Gate。这里保留真实缺口，不通过降低门槛追目标数值。

## Region 扩展

Core 图模式仍由有向 DATA/CONTROL/SEQUENTIAL 结构决定；本轮把其统一映射到 Req8.7 Core
ontology。原先无法确定 Core 类型的局部图才交给 DeepSeek，并得到
{region['extension_regions']} 个 Extension Region：{', '.join(region.get('extension_types', {})) or '无'}。
每次 Extension 调用只包含目标 RTL slice、相关 I/O、主要 state/event 和可选 SPEC 行，
`whole_design_rtl_supplied=false`。

## SPEC 提取与 RTL 映射

SPEC 来源：`{summary['spec']['source']}`，SHA256 `{summary['spec']['sha256']}`。
{remote_note}
每条行为必须携带能在所给 README 行中逐字定位的 evidence；LLM 不生成 SVA。

| Behavior | 类别 | Fixed primitive | SPEC evidence | RTL mapping |
|---|---|---|---|---|
{chr(10).join(spec_rows)}

SPEC 提取了 {summary['spec']['behaviors']} 条明确行为，其中 {summary['spec']['compiled_properties']}
条通过“原文证据 + RTL signal graph mapping + design-owned output”门槛并形成新属性。

| SPEC property | Obligation | Observed proof-core items | Globally unique items |
|---|---|---:|---:|
{chr(10).join(spec_attribution_rows) or '| 无 | - | 0 | 0 |'}

## Local Obligation Coverage

| 实验 | Applicable | Generated | Trusted | Generated coverage | Trusted coverage |
|---|---:|---:|---:|---:|---:|
| RTL-only | {rtl['obligation_coverage']['applicable_obligations']} | {rtl['obligation_coverage']['generated_obligations']} | {rtl['obligation_coverage']['trusted_obligations']} | {rtl['obligation_coverage']['generated_coverage_percent']:.2f}% | {rtl['obligation_coverage']['trusted_coverage_percent']:.2f}% |
| SPEC+RTL | {combined['obligation_coverage']['applicable_obligations']} | {combined['obligation_coverage']['generated_obligations']} | {combined['obligation_coverage']['trusted_obligations']} | {combined['obligation_coverage']['generated_coverage_percent']:.2f}% | {combined['obligation_coverage']['trusted_coverage_percent']:.2f}% |

## 三个实验问题

1. Region 更完整：Req8.4 的低置信 Core 候选现在可被保守地表达为 Extension Region，并保留局部证据与置信度。
2. Local Assertions 明显增加：RTL-only 从 {base['generated']} 增至 {rtl['generated']}，不是靠放宽 Trust Gate。
3. SPEC 带来新 obligation：新增 {summary['spec']['compiled_properties']} 条 SPEC_CONFORMANCE 候选，最终 {summary['spec']['trusted_properties']} 条通过严格门槛；其新增 proof-core item 数见上表说明。

## LLM 与硬编码审计

DeepSeek 共调用 {summary['llm']['calls']} 次、消耗 {summary['llm']['usage'].get('total_tokens', 0)} tokens；
Extension 与 SPEC 上下文均明确记录未提供 whole-design RTL。Python 实现中没有任何
design/module/signal 特判；设计路径、SPEC 行范围和模型参数全部来自配置/CLI。
"""
    path.write_text(report, encoding="utf-8")


def run(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    output = Path(args.output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    config = yaml.safe_load(Path(args.config).resolve().read_text(encoding="utf-8"))
    req = config.get("spec_extraction", {})
    spec_path = Path(args.spec).resolve()
    baseline_root = Path(args.baseline_root).resolve()

    design = parse_rtl([args.rtl])
    graph = build_semantic_graph(design)
    design_map = build_hierarchical_design_map(
        design, graph, args.top, include_dirs=config.get("include_dirs", [])
    )
    base_regions = build_verification_regions(
        design, graph, design_map,
        coi_depth=int(req.get("coi_depth", 2)),
        max_nodes=int(req.get("max_nodes_per_region", 72)),
        max_candidates_per_kind=req.get("max_candidates_per_kind_per_module"),
    )
    design.save(output / "rtl_structure.json")
    dump_json(output / "rtl_semantic_graph.json", graph)
    dump_json(output / "design_map.json", design_map)
    dump_json(output / "base_graph_regions.json", base_regions)

    baseline = _baseline(baseline_root)
    if baseline["source_digest"] != design.source_digest:
        raise RuntimeError("Req8.4 baseline and current RTL source digests differ")

    selected_spec_lines = spec_lines(spec_path, req.get("spec_line_ranges", []))
    extension_spec = spec_lines(spec_path, req.get("extension_spec_line_ranges", []))
    client = DeepSeekClient(_llm_config(config["llm"]))
    extension_prompt = (PROJECT_ROOT / "llm" / "prompts" / "extension_regions.txt").read_text(encoding="utf-8")
    extensions, extension_llm = _discover_extensions(
        base_regions, design, extension_spec, client, extension_prompt,
        output / "llm" / "extension_regions",
        limit=int(req.get("extension_llm_limit", 3)),
        attempts=int(req.get("llm_validation_attempts", 3)),
    )
    initial_inventory = build_region_inventory(base_regions, extensions)

    spec_prompt = (PROJECT_ROOT / "llm" / "prompts" / "spec_behaviors.txt").read_text(encoding="utf-8")
    spec_doc, spec_llm = _extract_spec(
        spec_path, selected_spec_lines, design, args.top, client, spec_prompt,
        output / "llm" / "spec_extraction",
        attempts=int(req.get("llm_validation_attempts", 3)),
    )
    mapped_behaviors, overlays = map_spec_behaviors_to_regions(spec_doc, initial_inventory, args.top)
    region_inventory = build_region_inventory(base_regions, extensions, overlays)
    # Re-run mapping only to make its evidence refer to the final enriched inventory.
    mapped_behaviors, _ = map_spec_behaviors_to_regions({"behaviors": mapped_behaviors}, region_inventory, args.top)
    dump_json(output / "regions.json", region_inventory)
    dump_json(output / "spec_behaviors.json", {
        **spec_doc, "behaviors": mapped_behaviors,
        "source": str(spec_path), "source_sha256": spec_llm["spec_sha256"],
    })

    reset = str(config.get("reset", "resetn"))
    reset_asserted = f"!{reset}" if config.get("reset_active_low", True) else reset
    pool_candidates, pool_rejections, pool_summary = build_property_candidate_pool(
        design, graph, design_map, region_inventory,
        {
            "reset": config.get("reset", "resetn"),
            "reset_active_low": config.get("reset_active_low", True),
        },
    )
    bindings = enumerate_local_candidate_bindings(
        pool_candidates, region_inventory, design, reset_asserted
    )
    selected, selection_audit = select_local_candidate_bindings(
        bindings,
        budget=int(req.get("rtl_property_budget", 60)),
        primitive_caps=req.get("primitive_caps", {}),
        minimum_count=int(req.get("minimum_rtl_properties", 40)),
    )
    rtl_properties, rtl_template_bindings, rtl_metadata = compile_rtl_properties(
        selected, design, reset_asserted
    )
    spec_properties, spec_template_bindings, spec_metadata = compile_spec_properties(
        mapped_behaviors, design, args.top, reset_asserted, spec_path
    )
    if len(rtl_properties) != len(selected):
        raise RuntimeError("a selected RTL candidate failed the fixed primitive binding gate")
    if len(rtl_properties) <= baseline["generated"]:
        raise RuntimeError("Req8.7 did not expand Local Assertions beyond Req8.4")

    dump_json(output / "candidate_pool_summary.json", pool_summary)
    dump_json(output / "candidate_selection.json", selection_audit)
    dump_json(output / "candidate_inventory.json", candidate_inventory(bindings))
    dump_json(output / "enumeration_rejections.json", pool_rejections)
    dump_json(output / "template_bindings.json", rtl_template_bindings + spec_template_bindings)
    dump_json(output / "rtl_only" / "generated_properties.json", rtl_properties)
    dump_json(output / "spec_plus_rtl" / "generated_properties.json", rtl_properties + spec_properties)
    dump_json(output / "property_metadata.json", {**rtl_metadata, **spec_metadata})

    formal_design = deepcopy(design)
    formal_design.files = _reachable_formal_files(design, design_map)
    rtl_probe = _formal(
        formal_design, rtl_properties, args.top, output / "rtl_only" / "probe", config,
        attribution=False,
    )
    dump_json(output / "rtl_only" / "probe_results.json", rtl_probe)
    trusted_rtl = _trusted(rtl_properties, rtl_probe.results)
    trusted_rtl, rtl_final, rtl_stabilization, rtl_removed_results = _stabilize_trusted(
        formal_design, trusted_rtl, args.top, output / "rtl_only" / "trusted", config,
        attribution=False,
    )
    dump_json(output / "rtl_only" / "trusted_properties.json", trusted_rtl)
    dump_json(output / "rtl_only" / "formal_results.json", rtl_final)

    spec_probe = _formal(
        formal_design, spec_properties, args.top, output / "spec_plus_rtl" / "spec_probe", config,
        attribution=False,
    ) if spec_properties else None
    spec_results = spec_probe.results if spec_probe else []
    if spec_probe:
        dump_json(output / "spec_plus_rtl" / "spec_probe_results.json", spec_probe)
    spec_probe_trusted = _trusted(spec_properties, spec_results)
    trusted_combined, combined_final, combined_stabilization, combined_removed_results = _stabilize_trusted(
        formal_design, trusted_rtl + spec_probe_trusted, args.top,
        output / "spec_plus_rtl" / "trusted", config,
        attribution=bool(req.get("property_attribution", True)),
    )
    combined_ids_after_stabilization = {item.property_id for item in trusted_combined}
    trusted_spec = [
        item for item in spec_probe_trusted
        if item.property_id in combined_ids_after_stabilization
    ]
    dump_json(output / "spec_plus_rtl" / "trusted_properties.json", trusted_combined)
    dump_json(output / "spec_plus_rtl" / "formal_results.json", combined_final)
    dump_json(output / "trusted_stabilization.json", {
        "rtl_only": rtl_stabilization,
        "spec_plus_rtl": combined_stabilization,
    })

    for name, result in (("RTL-only", rtl_final), ("SPEC+RTL", combined_final)):
        if any(item.result != "PASS" or item.vacuity != "NON_VACUOUS" for item in result.results):
            raise RuntimeError(f"{name} Trusted-only rerun violated PASS + NON_VACUOUS gate")

    rtl_trusted_ids = {item.property_id for item in trusted_rtl}
    spec_trusted_ids = {item.property_id for item in trusted_spec}
    combined_trusted_ids = rtl_trusted_ids | spec_trusted_ids
    rtl_applicability = {
        (region_id, item.candidate.primitive)
        for item in bindings for region_id in item.compatible_region_ids
    }
    spec_applicability = {
        (region_id, str(item["primitive"]))
        for item in mapped_behaviors if item.get("compilable")
        for region_id in item.get("rtl_mapping", {}).get("region_ids", [])
    }
    rtl_matrix_result_by_id = {item.property_id: item for item in rtl_probe.results}
    rtl_matrix_result_by_id.update(rtl_removed_results)
    rtl_matrix_result_by_id.update({item.property_id: item for item in rtl_final.results})
    rtl_matrix, rtl_obligation_coverage = build_local_obligation_matrix(
        region_inventory, rtl_applicability, rtl_properties, rtl_metadata,
        list(rtl_matrix_result_by_id.values()), rtl_trusted_ids,
    )
    combined_results = list(rtl_probe.results) + list(spec_results)
    combined_matrix_result_by_id = {item.property_id: item for item in combined_results}
    combined_matrix_result_by_id.update(rtl_removed_results)
    combined_matrix_result_by_id.update(combined_removed_results)
    combined_matrix_result_by_id.update({item.property_id: item for item in combined_final.results})
    combined_metadata = {**rtl_metadata, **spec_metadata}
    combined_matrix, combined_obligation_coverage = build_local_obligation_matrix(
        region_inventory, rtl_applicability | spec_applicability,
        rtl_properties + spec_properties, combined_metadata,
        list(combined_matrix_result_by_id.values()), combined_trusted_ids,
    )
    dump_json(output / "rtl_only" / "local_obligation_matrix.json", rtl_matrix)
    dump_json(output / "rtl_only" / "obligation_coverage.json", rtl_obligation_coverage)
    dump_json(output / "spec_plus_rtl" / "local_obligation_matrix.json", combined_matrix)
    dump_json(output / "spec_plus_rtl" / "obligation_coverage.json", combined_obligation_coverage)

    rtl_participation = region_participation(region_inventory, rtl_metadata, rtl_trusted_ids)
    combined_participation = region_participation(region_inventory, combined_metadata, combined_trusted_ids)
    rtl_region_gaps = _region_gap_audit(
        region_inventory, rtl_applicability, rtl_metadata, rtl_trusted_ids,
    )
    combined_region_gaps = _region_gap_audit(
        region_inventory, rtl_applicability | spec_applicability,
        combined_metadata, combined_trusted_ids,
    )
    if rtl_participation["coverage_percent"] <= baseline["region_participation"]["coverage_percent"]:
        raise RuntimeError("Req8.7 Region Participation did not improve beyond Req8.4")

    rtl_cover = _coverage(output / "rtl_only" / "trusted")
    combined_cover = _coverage(output / "spec_plus_rtl" / "trusted")
    rtl_checked = _stable_cover_ids(output / "rtl_only" / "trusted" / "formal" / "coverage_items.tsv")
    combined_checked = _stable_cover_ids(output / "spec_plus_rtl" / "trusted" / "formal" / "coverage_items.tsv")
    baseline_checked = _stable_cover_ids(baseline["coverage_items"])
    proof_comparison = {
        "rtl_only_unique_vs_req8_4": len(rtl_checked - baseline_checked),
        "rtl_only_lost_vs_req8_4": len(baseline_checked - rtl_checked),
        "spec_plus_rtl_unique_vs_rtl_only": len(combined_checked - rtl_checked),
        "spec_plus_rtl_lost_vs_rtl_only": len(rtl_checked - combined_checked),
        "denominators_equal": len({
            int(baseline["proof_core"]["total_items"]),
            int(rtl_final.coverage.get("total_items", -1)),
            int(combined_final.coverage.get("total_items", -2)),
        }) == 1,
    }
    dump_json(output / "proof_core_comparison.json", proof_comparison)

    attribution = {}
    attribution_path = output / "spec_plus_rtl" / "trusted" / "formal" / "property_proof_core_items.tsv"
    if attribution_path.is_file():
        attribution = build_property_attribution(
            attribution_path,
            output / "spec_plus_rtl" / "trusted" / "formal" / "coverage_items.tsv",
            {property_id: combined_metadata[property_id] for property_id in combined_trusted_ids},
            set(),
        )
        dump_json(output / "spec_plus_rtl" / "property_proof_core_attribution.json", attribution)

    rtl_counts = result_counts(rtl_properties, rtl_probe.results)
    combined_counts = result_counts(rtl_properties + spec_properties, combined_results)
    llm_usage = Counter(extension_llm.get("usage", {})) + Counter(spec_llm.get("usage", {}))
    summary = {
        "schema": "region_flow.7-real.v1",
        "design": args.design,
        "top": args.top,
        "rtl": str(Path(args.rtl).resolve()),
        "source_digest": design.source_digest,
        "spec": {
            "source": str(spec_path), "sha256": spec_llm["spec_sha256"],
            "source_url": str(req.get("spec_source_url", "")),
            "behaviors": len(mapped_behaviors),
            "compiled_properties": len(spec_properties),
            "trusted_properties": len(trusted_spec),
        },
        "regions": region_inventory["summary"],
        "experiments": {
            "req8_4_baseline": baseline,
            "spec_extraction_rtl_only": {
                **rtl_counts,
                "probe_trusted": rtl_counts["trusted"],
                "trusted": len(trusted_rtl),
                "trusted_rate_percent": round(100 * len(trusted_rtl) / len(rtl_properties), 2),
                "region_participation": rtl_participation,
                "region_gap_audit": rtl_region_gaps,
                "obligation_coverage": rtl_obligation_coverage,
                "proof_core": rtl_final.coverage,
                "effective_proof_core": rtl_cover,
                "trusted_rerun": result_counts(trusted_rtl, rtl_final.results),
                "trusted_stabilization": rtl_stabilization,
            },
            "spec_extraction_spec_plus_rtl": {
                **combined_counts,
                "probe_trusted": combined_counts["trusted"],
                "trusted": len(trusted_combined),
                "trusted_rate_percent": round(
                    100 * len(trusted_combined) / len(rtl_properties + spec_properties), 2
                ),
                "region_participation": combined_participation,
                "region_gap_audit": combined_region_gaps,
                "obligation_coverage": combined_obligation_coverage,
                "proof_core": combined_final.coverage,
                "effective_proof_core": combined_cover,
                "trusted_rerun": result_counts(trusted_combined, combined_final.results),
                "trusted_stabilization": combined_stabilization,
            },
        },
        "proof_core_comparison": proof_comparison,
        "property_attribution": {
            **{
                key: attribution.get(key) for key in (
                    "properties_catalogued", "properties_measured", "observed_union_items",
                    "globally_unique_items", "shared_items", "properties_with_unique_contribution",
                )
            },
            "spec_properties": [
                {
                    key: item.get(key) for key in (
                        "property_id", "obligation", "observed_proof_core_items",
                        "unique_contribution_items", "shared_contribution_items",
                    )
                }
                for item in attribution.get("properties", [])
                if str(item.get("property_id", "")).startswith("local_spec_")
            ],
        } if attribution else {},
        "llm": {
            "provider": "deepseek",
            "requested_model": config.get("llm", {}).get("model"),
            "calls": extension_llm["calls"] + spec_llm["calls"],
            "usage": dict(llm_usage),
            "extension": extension_llm,
            "spec_extraction": spec_llm,
            "whole_design_rtl_supplied": False,
            "generated_sva": False,
        },
        "trust_gate": {
            "definition": "all elaborated targets PASS and antecedent/precondition NON_VACUOUS",
            "rtl_only_final_all_pass_non_vacuous": all(
                item.result == "PASS" and item.vacuity == "NON_VACUOUS" for item in rtl_final.results
            ),
            "spec_plus_rtl_final_all_pass_non_vacuous": all(
                item.result == "PASS" and item.vacuity == "NON_VACUOUS" for item in combined_final.results
            ),
        },
        "runtime_seconds": round(time.monotonic() - started, 3),
        "artifacts": {
            "regions": str(output / "regions.json"),
            "spec_behaviors": str(output / "spec_behaviors.json"),
            "rtl_only_assertions": str(output / "rtl_only" / "trusted" / "assertions.sv"),
            "spec_plus_rtl_assertions": str(output / "spec_plus_rtl" / "trusted" / "assertions.sv"),
            "rtl_only_matrix": str(output / "rtl_only" / "local_obligation_matrix.json"),
            "spec_plus_rtl_matrix": str(output / "spec_plus_rtl" / "local_obligation_matrix.json"),
            "trusted_stabilization": str(output / "trusted_stabilization.json"),
        },
    }
    dump_json(output / "spec_extraction_summary.json", summary)
    report_path = Path(args.report).resolve()
    _write_report(report_path, summary, mapped_behaviors)
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Requirement 8.7 real local assertion expansion")
    parser.add_argument("--design", required=True)
    parser.add_argument("--rtl", required=True)
    parser.add_argument("--top", required=True)
    parser.add_argument("--spec", required=True)
    parser.add_argument("--config", required=True)
    parser.add_argument("--baseline-root", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--report", required=True)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    try:
        summary = run(args)
    except Exception as exc:
        print(f"Requirement 8.7 failed: {exc}")
        return 1
    print(json.dumps(summary, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
