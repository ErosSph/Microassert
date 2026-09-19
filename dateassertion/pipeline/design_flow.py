"""Requirement 8.10 cross-design generalization and real validation.

The orchestration is driven entirely by configuration.  Design-specific RTL,
top, reset, and documentation locations are data; graph discovery, fixed
primitive compilation, Contract composition, Formal feedback, and Trust Gate
logic are shared by every target.
"""

from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import shutil
import tempfile
import time
from typing import Any
import urllib.request

import yaml

from dateassertion.coverage_analysis.proof_core import (
    CoverItem, parse_coverage_items, stimuli_coverage_summary,
)
from dateassertion.formal.jaspergold import run_coverage_reachability
from dateassertion.generators.sva_generator import generate_sva
from dateassertion.ir.schema import FormalPropertyResult, FormalRunResult, PropertyIR, dump_json
from dateassertion.llm.client import DeepSeekClient, LLMUnavailableError
from dateassertion.pipeline.contract_validation import _llm_config
from dateassertion.pipeline.formal_gap_semantics import (
    compile_completion_composition,
    compile_region_gap_properties,
    coverage_by_type,
    extension_region_from_interpretation,
    gap_summary,
    localize_coverage_gaps,
    package_extension_interpretation_context,
    property_from_assignment,
    refine_local_contract,
    refine_gap_classification,
    select_contract_gap_assignments,
    select_residual_region_candidate,
    stable_cover_item_id,
)
from dateassertion.pipeline.local_contract_composition import (
    build_contract_graph,
    build_local_contracts,
    compile_composition_properties,
    generate_composition_candidates,
    package_spec_composition_context,
    select_composition_portfolio,
)
from dateassertion.pipeline.local_region_assertions import (
    build_obligation_funnel,
    build_region_inventory,
    compile_rtl_properties,
    compile_spec_properties,
    deduplicate_exact_properties,
    enumerate_local_candidate_bindings,
    expand_spec_behavior_obligations,
    map_spec_behaviors_to_regions,
    result_counts,
    select_local_candidate_bindings,
    spec_lines,
)
from dateassertion.pipeline.property_portfolio_planner import build_property_candidate_pool
from dateassertion.pipeline.region_flow import _run_formal
from dateassertion.pipeline.spec_extraction import _discover_extensions, _extract_spec
from dateassertion.pipeline.spec_composition import _validated_llm_constraints
from dateassertion.pipeline.gap_interpretation import _validated_llm_interpretation
from dateassertion.pipeline.feedback_regions import (
    localize_refinement_gaps, discover_refinement_candidates,
    interpret_refinements, compile_refinement_properties,
)
from dateassertion.pipeline.semantic_slicing import build_verification_regions
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.hierarchical_design import build_hierarchical_design_map
from dateassertion.rtl_frontend.parser import RTLDesign, parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph


PROJECT_ROOT = Path(__file__).resolve().parents[1]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _resolve(path: str) -> Path:
    value = Path(path)
    return value.resolve() if value.is_absolute() else (PROJECT_ROOT / value).resolve()


def _materialize_official_spec(
    spec_cfg: dict[str, Any], llm_cfg: dict[str, Any],
) -> tuple[Path, dict[str, Any]]:
    """Download an immutable official document and verify its configured hash.

    A byte-identical vendored copy is a fail-safe for transient network loss,
    but only when it matches the same expected digest. Neither source may be
    used without hash verification.
    """

    local_path = _resolve(str(spec_cfg["local_path"]))
    download_url = str(spec_cfg.get("download_url", "")).strip()
    expected = str(spec_cfg.get("expected_sha256", "")).lower().strip()
    if not download_url:
        return local_path, {
            "retrieval": "CONFIGURED_LOCAL_SOURCE",
            "download_url": "",
            "expected_sha256": expected or _sha256(local_path),
            "download_attempted": False,
            "download_cache_hit": False,
        }
    if not re.fullmatch(r"[0-9a-f]{64}", expected):
        raise RuntimeError("downloaded SPEC requires a 64-hex expected_sha256")
    cache_path = _resolve(str(spec_cfg["download_cache_path"]))
    if cache_path.is_file():
        actual = _sha256(cache_path)
        if actual != expected:
            raise RuntimeError(
                f"cached official SPEC digest mismatch: expected {expected}, got {actual}"
            )
        return cache_path, {
            "retrieval": "VERIFIED_DOWNLOAD_CACHE",
            "download_url": download_url,
            "expected_sha256": expected,
            "download_attempted": False,
            "download_cache_hit": True,
        }

    proxy = str(spec_cfg.get("download_proxy") or llm_cfg.get("proxy") or "").strip()
    handlers = [urllib.request.ProxyHandler({"http": proxy, "https": proxy})] if proxy else []
    try:
        with urllib.request.build_opener(*handlers).open(
            download_url, timeout=int(spec_cfg.get("download_timeout_seconds", 180)),
        ) as response:
            payload = response.read()
        actual = hashlib.sha256(payload).hexdigest()
        if actual != expected:
            raise RuntimeError(
                f"downloaded official SPEC digest mismatch: expected {expected}, got {actual}"
            )
        cache_path.parent.mkdir(parents=True, exist_ok=True)
        temporary = cache_path.with_name(cache_path.name + ".download")
        temporary.write_bytes(payload)
        temporary.replace(cache_path)
        return cache_path, {
            "retrieval": "DOWNLOADED_AND_HASH_VERIFIED",
            "download_url": download_url,
            "expected_sha256": expected,
            "download_attempted": True,
            "download_cache_hit": False,
        }
    except Exception as exc:
        if local_path.is_file() and _sha256(local_path) == expected:
            return local_path, {
                "retrieval": "VERIFIED_VENDORED_FALLBACK_AFTER_DOWNLOAD_ERROR",
                "download_url": download_url,
                "expected_sha256": expected,
                "download_attempted": True,
                "download_cache_hit": False,
                "download_error": f"{type(exc).__name__}: {exc}",
            }
        raise


def _checked(items: list[CoverItem]) -> set[str]:
    return {
        stable_cover_item_id(item) for item in items
        if item.status == "covered_and_checked"
    }


def _trusted(properties: list[PropertyIR], results: list[FormalPropertyResult]) -> list[PropertyIR]:
    by_id = {item.property_id: item for item in results}
    return [
        prop for prop in properties
        if prop.property_id in by_id
        and by_id[prop.property_id].result == "PASS"
        and by_id[prop.property_id].vacuity == "NON_VACUOUS"
    ]


def _passed(properties: list[PropertyIR], results: list[FormalPropertyResult]) -> list[PropertyIR]:
    """Admit PASS candidates to an exact-set vacuity rerun, not to trust."""

    by_id = {item.property_id: item for item in results}
    return [
        prop for prop in properties
        if prop.property_id in by_id and by_id[prop.property_id].result == "PASS"
    ]


def _combined_probe(*runs: Any | None) -> Any:
    """Join already completed independent candidate-gate results."""

    available = [item for item in runs if item is not None]
    if not available:
        raise ValueError("at least one completed Formal run is required")
    merged = deepcopy(available[0])
    merged.results = [result for run in available for result in run.results]
    merged.notes = list(merged.notes) + [
        "Candidate probe assembled from independent persisted JasperGold runs."
    ]
    return merged


def _formal_config(config: dict[str, Any], target: dict[str, Any]) -> dict[str, Any]:
    local = deepcopy(config)
    local["clock"] = target["clock"]
    local["reset"] = target["reset"]
    local["reset_active_low"] = bool(target["reset_active_low"])
    local["include_dirs"] = [str(_resolve(item)) for item in target.get("include_dirs", [])]
    return local


def _independent_stimuli_coverage(
    design: RTLDesign, top: str, root: Path, config: dict[str, Any],
) -> dict[str, Any]:
    """Run or reuse DUT-only stimuli coverage for the requested final metrics."""

    output = root / "formal" / "stimuli_coverage"
    record_path = output / "reachability_run.json"
    statuses_path = output / "coverage_statuses.tsv"
    reused = False
    if record_path.is_file() and statuses_path.is_file():
        record = json.loads(record_path.read_text(encoding="utf-8"))
        reused = record.get("source_digest") == design.source_digest
    if not reused:
        formal_config = dict(config.get("formal", {}))
        formal_config.update({
            "clock": config.get("clock", "clk"),
            "reset": config.get("reset", "resetn"),
            "reset_active_low": bool(config.get("reset_active_low", True)),
            "include_dirs": list(config.get("include_dirs", [])),
        })
        record = run_coverage_reachability(
            design.files, top, output, formal_config,
        )
    return {
        "run": {**record, "reused": reused},
        "coverage": stimuli_coverage_summary(statuses_path),
    }


def _normalize_cached_budget_outcomes(run: FormalRunResult) -> bool:
    """Upgrade legacy UNKNOWN records without hiding missing tool results."""

    changed = False
    for item in run.results:
        if item.result == "UNKNOWN":
            has_elaborated_target = bool(
                item.target_count or item.target_summary.get("UNKNOWN", 0)
            )
            item.result = "TIMEOUT_ACCEPTED" if has_elaborated_target else "NOT_EVALUATED"
            item.classification = item.result
            changed = True
        if "UNKNOWN" in item.target_summary:
            item.target_summary["TIMEOUT_ACCEPTED"] = item.target_summary.pop("UNKNOWN")
            changed = True
        for target in item.target_results:
            if target.get("result") == "UNKNOWN":
                target["result"] = "TIMEOUT_ACCEPTED"
                changed = True
        if item.vacuity == "UNKNOWN":
            item.vacuity = "NOT_EVALUATED"
            changed = True
        if "UNKNOWN" in item.target_vacuity_summary:
            item.target_vacuity_summary["NOT_EVALUATED"] = (
                item.target_vacuity_summary.pop("UNKNOWN")
            )
            changed = True
    if "unknown" in run.summary or "elaborated_targets_unknown" in run.summary:
        changed = True
    if not changed:
        return False
    counts = Counter(item.result for item in run.results)
    total = len(run.results)
    accepted = counts["PASS"] + counts["TIMEOUT_ACCEPTED"]
    run.summary.update({
        "total": total,
        "proven": counts["PASS"],
        "failed": counts["FAIL"],
        "timeout_accepted": counts["TIMEOUT_ACCEPTED"],
        "not_evaluated": counts["NOT_EVALUATED"],
        "errors": counts["ERROR"],
        "accepted_correct": accepted,
        "accepted_correct_rate": round(100 * accepted / total, 2) if total else 0.0,
        "proven_rate": round(100 * counts["PASS"] / total, 2) if total else 0.0,
    })
    for key in ("unknown", "elaborated_targets_unknown"):
        run.summary.pop(key, None)
    run.summary["elaborated_targets_timeout_accepted"] = sum(
        item.target_summary.get("TIMEOUT_ACCEPTED", 0) for item in run.results
    )
    if counts["FAIL"]:
        run.status = "FAIL"
    elif counts["ERROR"] or counts["NOT_EVALUATED"]:
        run.status = "NOT_EVALUATED"
    elif counts["PASS"] == total and total:
        run.status = "PASS"
    elif accepted == total and total:
        run.status = "TIMEOUT_ACCEPTED"
    run.notes.append(
        "Legacy UNKNOWN outcomes normalized as TIMEOUT_ACCEPTED under the configured formal time-budget policy."
    )
    return True


def _scope_regions(regions: dict[str, Any], module: str | set[str]) -> dict[str, Any]:
    """Restrict an experiment to one module or a resolved CPU hierarchy."""

    scoped = deepcopy(regions)
    modules = {module} if isinstance(module, str) else set(module)
    scoped["regions"] = [
        item for item in regions.get("regions", []) if item.get("module") in modules
    ]
    functional = [item for item in scoped["regions"] if item.get("kind") != "MODULE"]
    scoped["summary"] = {
        **deepcopy(regions.get("summary", {})),
        "region_count": len(scoped["regions"]),
        "functional_region_count": len(functional),
        "by_kind": dict(Counter(item.get("kind", "UNKNOWN") for item in scoped["regions"])),
        "by_detection_status": dict(Counter(
            item.get("detection_status", "UNSPECIFIED") for item in functional
        )),
        "validation_scope_module": module if isinstance(module, str) else None,
        "validation_scope_modules": sorted(modules),
    }
    return scoped


def _property_antecedent(prop: PropertyIR) -> str:
    """Return the fixed-template implication antecedent, if present."""

    for operator in ("|->", "|=>"):
        if operator in prop.body:
            return prop.body.split(operator, 1)[0].strip().strip("() ")
    return "1'b1"


def _antecedent_coi(
    graph: dict[str, Any], prop: PropertyIR, *, maximum_depth: int,
) -> dict[str, Any]:
    """Build an auditable directed backward slice from antecedent signals."""

    module = prop.target_module
    node_ids = {str(node.get("id", "")) for node in graph.get("nodes", [])}
    names = expression_signals(_property_antecedent(prop))
    seeds = {
        f"signal:{module}.{name}" for name in names
        if f"signal:{module}.{name}" in node_ids
    }
    incoming: dict[str, list[dict[str, Any]]] = {}
    for edge in graph.get("edges", []):
        if str(edge.get("type", "")).upper() not in {
            "DATA", "CONTROL", "SEQUENTIAL", "CROSS_MODULE",
        }:
            continue
        incoming.setdefault(str(edge.get("target", "")), []).append(edge)
    visited = set(seeds)
    traversed: list[dict[str, Any]] = []
    frontier = set(seeds)
    for _depth in range(max(0, maximum_depth)):
        next_frontier: set[str] = set()
        for target in sorted(frontier):
            for edge in incoming.get(target, []):
                source = str(edge.get("source", ""))
                if not source:
                    continue
                traversed.append({
                    key: deepcopy(edge.get(key))
                    for key in ("type", "source", "target", "semantic_kind", "evidence")
                    if key in edge
                })
                if source not in visited:
                    visited.add(source)
                    next_frontier.add(source)
        if not next_frontier:
            break
        frontier = next_frontier
    return {
        "antecedent": _property_antecedent(prop),
        "seed_signal_nodes": sorted(seeds),
        "node_ids": sorted(visited),
        "edges": traversed,
        "node_count": len(visited),
        "edge_count": len(traversed),
        "maximum_depth": maximum_depth,
        "direction": "BACKWARD_INCOMING_DATA_CONTROL_SEQUENTIAL_CROSS_MODULE",
    }


def _local_clock_reset(
    design: RTLDesign, module: str, config: dict[str, Any],
) -> tuple[str, str, bool] | None:
    """Choose real local clock/reset ports using generic signal metadata."""

    signals = design.module_signals.get(module, {})
    inputs = {
        name for name, signal in signals.items()
        if signal.direction in {"input", "inout"}
    }
    preferred_clock = str(config.get("clock", "clk"))
    preferred_reset = str(config.get("reset", "resetn"))
    clocks = sorted(
        (name for name in inputs if re.search(r"(^|_)clk($|_)", name, re.I)),
        key=lambda name: (name != preferred_clock, len(name), name),
    )
    resets = sorted(
        (name for name in inputs if re.search(r"(^|_)(rst|reset)($|_)", name, re.I)),
        key=lambda name: (name != preferred_reset, len(name), name),
    )
    if not clocks or not resets:
        return None
    reset = resets[0]
    active_low = bool(re.search(r"(?:_n|n)$", reset, re.I))
    if reset == preferred_reset:
        active_low = bool(config.get("reset_active_low", active_low))
    return clocks[0], reset, active_low


def _formal_input_identity(design, properties, top, config):
    """Ignore mutable report annotations; include all proof-relevant inputs."""
    include_hashes = {}
    for directory in config.get("include_dirs", []):
        for path in Path(directory).rglob("*"):
            if path.is_file() and path.suffix in {".vh", ".svh"}:
                include_hashes[str(path.resolve())] = _sha256(path)
    payload = {
        "source_digest": design.source_digest, "top": top,
        "clock": config.get("clock", "clk"), "reset": config.get("reset", "rst_n"),
        "reset_active_low": config.get("reset_active_low", True),
        "include_dirs": config.get("include_dirs", []), "formal": config.get("formal", {}),
        "include_sha256": include_hashes,
        "properties": [{key: getattr(p, key) for key in (
            "property_id", "target_module", "body", "disable_iff", "signals", "observation_helper_ids",
        )} for p in properties],
    }
    return {"schema": "formal-input-identity.v1", "sha256": hashlib.sha256(
        json.dumps(payload, sort_keys=True).encode()).hexdigest(), "inputs": payload}


def _formal_cache_matches(design, properties, top, root, config, identity):
    manifest = root / "formal" / "input_identity.json"
    if manifest.is_file():
        recorded = json.loads(manifest.read_text())
        cached_sva = root / "assertions.sv"
        return (recorded.get("sha256") == identity["sha256"] and cached_sva.is_file()
                and recorded.get("sva_sha256") == _sha256(cached_sva))
    # Existing real runs predate the manifest. Admit them only when the exact
    # rendered assertion file matches and no RTL/include input is newer than
    # the result. New executions always carry the full input digest above.
    sva = root / "assertions.sv"
    tcl = root / "formal" / "run_jaspergold.tcl"
    result = root / "formal" / "formal_results.json"
    if not (sva.is_file() and tcl.is_file() and result.is_file()):
        return False
    inputs = [Path(p) for p in design.files]
    for folder in config.get("include_dirs", []):
        inputs.extend(p for p in Path(folder).rglob("*") if p.suffix in {".vh", ".svh"})
    if any(not p.is_file() or p.stat().st_mtime_ns > result.stat().st_mtime_ns for p in inputs):
        return False
    text = tcl.read_text()
    formal_cfg = config.get("formal", {})
    reset = str(config.get("reset", "rst_n"))
    reset_expr = "!" + reset if config.get("reset_active_low", True) else reset
    required = [f"elaborate -top {top}", f"clock {config.get('clock', 'clk')}",
                f"reset -expression {{{reset_expr}}}"]
    proof_scope = str(formal_cfg.get("proof_scope", "all")).lower()
    if proof_scope == "all":
        required.append(f"prove -all -time_limit {formal_cfg.get('prove_time_limit', '300s')}")
    elif proof_scope == "asserts":
        required.extend([
            f"prove -all -asserts -time_limit {formal_cfg.get('prove_time_limit', '300s')}",
            f"prove -all -covers -time_limit {formal_cfg.get('precondition_probe_time_limit', '60s')}",
        ])
    else:
        return False
    if formal_cfg.get("measure_proof_coverage", True):
        required.append("check_cov -measure -type proof")
    if formal_cfg.get("engine_mode"):
        required.append(f"set_engine_mode {{{formal_cfg['engine_mode']}}}")
    if any(value not in text for value in required):
        return False
    with tempfile.TemporaryDirectory(prefix="extension-cache-check-") as temporary:
        expected = generate_sva(deepcopy(properties), design.signals, top,
            Path(temporary)/"expected.sv", clock=config.get("clock", "clk"),
            reset=config.get("reset", "rst_n"), module_signals=design.module_signals)
    if sva.read_text() != expected:
        return False
    dump_json(manifest, {**identity, "sva_sha256": _sha256(sva),
                         "migration": "exact rendered SVA + Tcl + input timestamp verified"})
    return True


def _formal(
    design: RTLDesign, properties: list[PropertyIR], top: str, root: Path,
    config: dict[str, Any], *, attribution: bool = False,
    measure_proof_coverage: bool = True,
) -> Any:
    local = deepcopy(config)
    local.setdefault("formal", {})["property_attribution"] = attribution
    local["formal"]["measure_proof_coverage"] = measure_proof_coverage
    identity = _formal_input_identity(design, properties, top, local)
    completed_path = root / "formal" / "formal_results.json"
    if local.get("formal", {}).get("reuse_completed_results") and completed_path.is_file():
        raw = json.loads(completed_path.read_text(encoding="utf-8"))
        expected = [item.property_id for item in properties]
        observed = [item.get("property_id") for item in raw.get("results", [])]
        coverage_items = root / "formal" / "coverage_items.tsv"
        independent_vacuity_artifact = (
            "stabilization" in root.parts and "individual" in root.parts
        )
        if (
            expected == observed
            and raw.get("coverage", {}).get("instance") == top
            and (coverage_items.is_file() or independent_vacuity_artifact)
            and _formal_cache_matches(design, properties, top, root, local, identity)
        ):
            cached = FormalRunResult(
                status=raw["status"], tool=raw["tool"],
                runtime_seconds=float(raw.get("runtime_seconds", 0.0)),
                log_path=str(raw.get("log_path", "")),
                results=[FormalPropertyResult(**item) for item in raw.get("results", [])],
                summary=raw.get("summary", {}), coverage=raw.get("coverage", {}),
                notes=raw.get("notes", []),
            )
            by_id = {item.property_id: item for item in properties}
            normalized = _normalize_cached_budget_outcomes(cached)
            true_antecedent_normalized = False
            for item in cached.results:
                prop = by_id.get(item.property_id)
                compact = re.sub(r"\s+", "", prop.body) if prop else ""
                if (
                    item.result == "PASS" and item.vacuity is None
                    and re.match(r"^\(*1'b1\)*\|[-=]>", compact)
                ):
                    item.vacuity = "NON_VACUOUS"
                    item.classification = "PROVEN_NONVACUOUS"
                    item.target_vacuity_summary["NON_VACUOUS"] = max(
                        1, item.target_count,
                    )
                    normalized = True
                    true_antecedent_normalized = True
            if normalized:
                cached.summary["non_vacuous"] = sum(
                    item.vacuity == "NON_VACUOUS" for item in cached.results
                )
                if true_antecedent_normalized:
                    cached.notes.append(
                        "Syntactically true antecedents normalized as non-vacuous; JasperGold emits no precondition target for them."
                    )
                dump_json(completed_path, cached)
            return cached
    attempts = max(1, int(local.get("formal", {}).get("transient_retry_attempts", 3)))
    result = None
    for attempt in range(1, attempts + 1):
        result = _run_formal(
            design, properties, top, root / "formal", local, root / "assertions.sv"
        )
        dump_json(root / "formal" / "input_identity.json", {
            **identity, "sva_sha256": _sha256(root / "assertions.sv"),
        })
        if result.status not in {"ERROR", "NOT_EVALUATED"}:
            return result
        if attempt < attempts:
            time.sleep(float(
                local.get("formal", {}).get("transient_retry_delay_seconds", 2)
            ))
    assert result is not None
    return result


def _stable_formal(
    design: RTLDesign, fixed: list[PropertyIR], candidates: list[PropertyIR],
    top: str, root: Path, config: dict[str, Any], *, attribution: bool = False,
    candidate_probe: Any | None = None, graph: dict[str, Any] | None = None,
    allow_empty: bool = False,
) -> tuple[list[PropertyIR], Any | None, list[dict[str, Any]]]:
    """Establish strict trust without losing candidates to scheduler ordering.

    A multi-target run can prove every assertion while spending its entire
    cover budget on one hard antecedent.  We retain portfolio NON_VACUOUS
    results and re-run only PASS candidates without a vacuity decision one at a time.
    The exact final portfolio supplies Proof-Core; independently persisted
    reachability evidence supplies the per-property vacuity decision.
    """

    current = list(candidates)
    audit: list[dict[str, Any]] = []
    if candidate_probe is not None:
        probe = candidate_probe
        probe_source = "upstream_candidate_probe"
    else:
        probe = _formal(
            design, fixed + current, top,
            root / "stabilization" / "portfolio_probe", config,
            attribution=attribution,
        )
        probe_source = "portfolio_probe"
    by_id = {item.property_id: item for item in probe.results}
    bad_fixed = [
        prop.property_id for prop in fixed
        if prop.property_id not in by_id or by_id[prop.property_id].result != "PASS"
    ]
    if bad_fixed:
        raise RuntimeError(f"trusted fixed portfolio destabilized: {bad_fixed}")

    evidence: dict[str, FormalPropertyResult] = {
        prop.property_id: by_id[prop.property_id]
        for prop in current
        if prop.property_id in by_id
        and by_id[prop.property_id].result == "PASS"
        and by_id[prop.property_id].vacuity == "NON_VACUOUS"
    }
    individual: list[dict[str, Any]] = []
    hierarchical: list[dict[str, Any]] = []
    hierarchy_cfg = config.get("formal", {})
    if hierarchy_cfg.get("hierarchical_vacuity_enabled") and graph:
        unresolved = [
            prop for prop in current
            if prop.property_id not in evidence
            and prop.property_id in by_id
            and by_id[prop.property_id].result == "PASS"
            and by_id[prop.property_id].vacuity != "VACUOUS"
        ]
        depth = int(hierarchy_cfg.get("hierarchical_vacuity_coi_depth", 8))
        ranked = sorted(
            ((_antecedent_coi(graph, prop, maximum_depth=depth), prop) for prop in unresolved),
            key=lambda item: (
                item[0]["node_count"], item[0]["edge_count"], item[1].property_id,
            ),
        )
        full_limit = int(
            hierarchy_cfg.get("hierarchical_vacuity_full_confirm_limit", 4)
        )
        full_confirmations = 0
        for coi, prop in ranked:
            local_signals = _local_clock_reset(design, prop.target_module, config)
            record: dict[str, Any] = {
                "property_id": prop.property_id,
                "target_module": prop.target_module,
                "coi": coi,
                "helper_lemmas": [],
                "unproven_assumptions": [],
                "local_result": "NOT_RUN",
                "local_vacuity": "NOT_RUN",
                "full_cpu_result": "NOT_RUN",
                "full_cpu_vacuity": "NOT_RUN",
                "accepted_for_trust": False,
            }
            if local_signals is None:
                record["reason"] = "NO_LOCAL_CLOCK_RESET_PORTS"
                hierarchical.append(record)
                continue
            clock, reset, active_low = local_signals
            local_prop = deepcopy(prop)
            local_prop.disable_iff = f"!{reset}" if active_low else reset
            local_config = deepcopy(config)
            local_formal = local_config.setdefault("formal", {})
            local_formal["prove_time_limit"] = str(
                local_formal.get("hierarchical_vacuity_local_time_limit", "15s")
            )
            local_formal["coverage_time_limit"] = local_formal["prove_time_limit"]
            local_formal["measure_proof_coverage"] = False
            local_config["clock"] = clock
            local_config["reset"] = reset
            local_config["reset_active_low"] = active_low
            local_root = (
                root / "hierarchical_vacuity" / prop.property_id / "local_module"
            )
            local_run = _formal(
                design, [local_prop], prop.target_module, local_root, local_config,
            )
            local_item = local_run.results[0] if local_run.results else None
            record.update({
                "local_clock": clock,
                "local_reset": reset,
                "local_result": local_item.result if local_item else "NOT_EVALUATED",
                "local_vacuity": local_item.vacuity if local_item else "NOT_EVALUATED",
                "local_artifact": str(local_root / "formal" / "formal_results.json"),
            })
            if not (
                local_item and local_item.result == "PASS"
                and local_item.vacuity == "NON_VACUOUS"
            ):
                record["reason"] = "LOCAL_REACHABILITY_NOT_CONFIRMED"
                hierarchical.append(record)
                continue
            if full_confirmations >= full_limit:
                record["reason"] = "FULL_CPU_CONFIRMATION_BUDGET_EXHAUSTED"
                hierarchical.append(record)
                continue
            full_confirmations += 1
            full_config = deepcopy(config)
            full_formal = full_config.setdefault("formal", {})
            full_formal["prove_time_limit"] = str(
                full_formal.get("hierarchical_vacuity_full_time_limit", "300s")
            )
            full_formal["coverage_time_limit"] = full_formal["prove_time_limit"]
            full_formal["measure_proof_coverage"] = False
            full_root = (
                root / "hierarchical_vacuity" / prop.property_id / "full_cpu"
            )
            full_run = _formal(design, [prop], top, full_root, full_config)
            full_item = full_run.results[0] if full_run.results else None
            accepted = bool(
                full_item and full_item.result == "PASS"
                and full_item.vacuity == "NON_VACUOUS"
            )
            if accepted:
                evidence[prop.property_id] = full_item
            record.update({
                "full_cpu_result": full_item.result if full_item else "NOT_EVALUATED",
                "full_cpu_vacuity": full_item.vacuity if full_item else "NOT_EVALUATED",
                "accepted_for_trust": accepted,
                "reason": (
                    "FULL_CPU_PASS_NON_VACUOUS"
                    if accepted else "FULL_CPU_REACHABILITY_NOT_CONFIRMED"
                ),
                "full_cpu_artifact": str(full_root / "formal" / "formal_results.json"),
            })
            hierarchical.append(record)
    vacuity_config = deepcopy(config)
    formal_cfg = vacuity_config.setdefault("formal", {})
    limit = str(formal_cfg.get("vacuity_probe_time_limit", "30s"))
    formal_cfg["prove_time_limit"] = limit
    formal_cfg["coverage_time_limit"] = limit
    formal_cfg["measure_proof_coverage"] = False
    individual_limit_raw = formal_cfg.get("individual_vacuity_probe_limit")
    individual_limit = (
        max(0, int(individual_limit_raw))
        if individual_limit_raw is not None else None
    )
    individual_not_run: list[str] = []
    for prop in current:
        prior = by_id.get(prop.property_id)
        if (
            prop.property_id in evidence
            or prior is None
            or prior.result != "PASS"
            or prior.vacuity == "VACUOUS"
        ):
            continue
        if individual_limit is not None and len(individual) >= individual_limit:
            individual_not_run.append(prop.property_id)
            continue
        one = _formal(
            design, [prop], top,
            root / "stabilization" / "individual" / prop.property_id,
            vacuity_config,
        )
        item = one.results[0] if one.results else None
        accepted = bool(
            item and item.result == "PASS" and item.vacuity == "NON_VACUOUS"
        )
        if accepted:
            evidence[prop.property_id] = item
        individual.append({
            "property_id": prop.property_id,
            "result": item.result if item else "MISSING",
            "vacuity": item.vacuity if item else "NOT_EVALUATED",
            "accepted": accepted,
            "artifact": str(
                root / "stabilization" / "individual" / prop.property_id
                / "formal" / "formal_results.json"
            ),
        })

    survivors = [prop for prop in current if prop.property_id in evidence]
    removed = sorted(
        {prop.property_id for prop in current}
        - {prop.property_id for prop in survivors}
    )
    audit.append({
        "round": 1,
        "probe_source": probe_source,
        "fixed": len(fixed),
        "candidate_input": len(current),
        "candidate_survivors": len(survivors),
        "removed_property_ids": removed,
        "hierarchical_vacuity_runs": hierarchical,
        "individual_vacuity_runs": individual,
        "individual_vacuity_probe_limit": individual_limit,
        "individual_vacuity_not_run_property_ids": individual_not_run,
    })

    # Most callers require a populated exact portfolio: preserving that
    # default makes a missing assertion set a hard integration error.  The
    # Req12 incremental probe is different.  It may legitimately contain
    # policy-accepted timeouts or vacuous PASSes, neither of which can become
    # strict evidence.  Do not invoke JasperGold on a comment-only SVA file in
    # that explicitly opted-in case; retain the upstream probe and a concrete
    # audit instead of manufacturing a PASS/coverage result.
    if allow_empty and not fixed and not survivors:
        audit.append({
            "round": len(audit) + 1,
            "phase": "exact_portfolio",
            "status": "SKIPPED_EMPTY_STRICT_PORTFOLIO",
            "reason": "NO_PASS_NONVACUOUS_SURVIVORS",
            "fixed": 0,
            "candidate_input": len(current),
            "candidate_survivors": 0,
            "removed_property_ids": [item.property_id for item in current],
            "policy": (
                "No empty JasperGold proof is run. Upstream probe outcomes are "
                "retained and are not promoted to strict evidence."
            ),
        })
        dump_json(root / "stabilization" / "audit.json", audit)
        return [], None, audit

    # A target that was PASS in the broad probe can become UNKNOWN when the
    # reduced multi-target run changes Jasper's scheduling.  Treat that as an
    # unstable candidate, not as a fatal orchestration error: monotonically
    # remove it and rerun the exact reduced portfolio.  The final proof core
    # therefore still corresponds to precisely the properties we report.
    exact_round = 0
    while True:
        exact_round += 1
        exact = _formal(
            design, fixed + survivors, top, root, config, attribution=attribution,
        )
        if exact.status in {"ERROR", "NOT_EVALUATED"}:
            raise RuntimeError(
                f"JasperGold did not evaluate exact portfolio after retries: {root}"
            )
        exact_by_id = {item.property_id: item for item in exact.results}
        fixed_bad = [
            prop.property_id for prop in fixed
            if prop.property_id not in exact_by_id
            or exact_by_id[prop.property_id].result != "PASS"
        ]
        if fixed_bad:
            raise RuntimeError(f"exact fixed portfolio destabilized: {fixed_bad}")
        unstable = [
            prop.property_id for prop in survivors
            if prop.property_id not in exact_by_id
            or exact_by_id[prop.property_id].result != "PASS"
        ]
        audit.append({
            "round": len(audit) + 1,
            "phase": "exact_portfolio",
            "exact_round": exact_round,
            "fixed": len(fixed),
            "candidate_input": len(survivors),
            "candidate_survivors": len(survivors) - len(unstable),
            "removed_property_ids": sorted(unstable),
        })
        if not unstable:
            break
        unstable_ids = set(unstable)
        survivors = [
            prop for prop in survivors if prop.property_id not in unstable_ids
        ]
        if not fixed and not survivors:
            # An empty strict portfolio is a valid outcome.  The rejected
            # candidates remain visible in the stabilization audit and may be
            # budget-accepted, but are never silently promoted to Trusted.
            break

    trusted_ids = {prop.property_id for prop in fixed + survivors}
    merged_results: list[FormalPropertyResult] = []
    for item in exact.results:
        if item.property_id not in trusted_ids:
            continue
        source = evidence.get(item.property_id)
        if source is not None and item.vacuity != "NON_VACUOUS":
            item.vacuity = "NON_VACUOUS"
            item.classification = "PROVEN_NONVACUOUS"
            item.target_vacuity_summary = source.target_vacuity_summary
            item.notes = (
                (item.notes + "; ") if item.notes else ""
            ) + "vacuity joined from independent single-property JasperGold run"
        merged_results.append(item)
    exact.results = merged_results
    exact.summary.update({
        "total": len(merged_results),
        "proven": len(merged_results),
        "failed": 0,
        "timeout_accepted": 0,
        "not_evaluated": 0,
        "errors": 0,
        "accepted_correct": len(merged_results),
        "accepted_correct_rate": 100.0 if merged_results else 0.0,
        "proven_rate": 100.0 if merged_results else 0.0,
        "non_vacuous": sum(
            item.vacuity == "NON_VACUOUS" for item in merged_results
        ),
    })
    exact.notes.append(
        "Trust Gate joins exact-portfolio proof with persisted single-property antecedent-reachability evidence."
    )
    dump_json(root / "formal" / "formal_results.json", exact)
    dump_json(root / "stabilization" / "audit.json", audit)
    return survivors, exact, audit


def _formal_metrics(properties: list[PropertyIR], result: Any, items: list[CoverItem]) -> dict[str, Any]:
    return {
        **result_counts(properties, result.results),
        "coverage": coverage_by_type(items),
        "proof_core": result.coverage,
        "all_pass_non_vacuous": len(_trusted(properties, result.results)) == len(properties),
    }


def _region_metrics(
    regions: dict[str, Any], graph: dict[str, Any], design_map: dict[str, Any], modules: set[str],
) -> dict[str, Any]:
    functional = [item for item in regions.get("regions", []) if item.get("kind") != "MODULE"]
    graph_nodes = {
        str(item["id"]) for item in graph.get("nodes", []) if item.get("module") in modules
    }
    represented = {
        str(node_id) for region in functional if region.get("module") in modules
        for node_id in region.get("coi", {}).get("node_ids", [])
        if str(node_id) in graph_nodes
    }
    state = [
        item for item in design_map.get("ownership", {}).get("state_registers", [])
        if item.get("module") in modules
    ]
    region_signals = {
        (str(region.get("module", "")), str(signal))
        for region in functional for signal in region.get("signals", [])
    }
    owned = [
        item for item in state
        if (str(item.get("module", "")), str(item.get("signal", ""))) in region_signals
    ]
    unexplained = graph_nodes - represented
    adjacency: dict[str, set[str]] = {node_id: set() for node_id in unexplained}
    for edge in graph.get("edges", []):
        source, target = str(edge.get("source", "")), str(edge.get("target", ""))
        if source in unexplained and target in unexplained:
            adjacency[source].add(target)
            adjacency[target].add(source)
    components = 0
    pending = set(unexplained)
    while pending:
        components += 1
        stack = [pending.pop()]
        while stack:
            for neighbor in adjacency.get(stack.pop(), set()):
                if neighbor in pending:
                    pending.remove(neighbor)
                    stack.append(neighbor)
    return {
        "total_regions": len(functional),
        "core_regions": sum(item.get("ontology_classification") == "CORE_REGION" for item in functional),
        "extension_regions": sum(item.get("ontology_classification") == "EXTENSION_REGION" for item in functional),
        "region_semantic_coverage": {
            "represented_nodes": len(represented),
            "target_module_nodes": len(graph_nodes),
            "percent": round(100 * len(represented) / len(graph_nodes), 2) if graph_nodes else 0.0,
        },
        "unexplained_rtl_clusters": {
            "nodes": len(unexplained),
            "weakly_connected_components": components,
        },
        "region_ownership_completeness": {
            "owned_state": len(owned),
            "state": len(state),
            "percent": round(100 * len(owned) / len(state), 2) if state else 100.0,
        },
        "by_kind": dict(Counter(item.get("kind", "UNKNOWN") for item in functional)),
    }


def _terminal_reasons(records: list[dict[str, Any]]) -> dict[str, int]:
    reasons: Counter[str] = Counter()
    for row in records:
        if row.get("gap_type") == "D_NON_ACTIONABLE":
            reason = "UNREACHABLE" if "unreachable" in str(row.get("diagnosis_reason", "")).lower() else "TOOL_LIMITATION"
        elif row.get("type_a_subtype") == "RTL_DETAIL":
            reason = "UNSUPPORTED_RTL_DETAIL"
        elif row.get("priority", {}).get("eligible_for_refinement"):
            reason = "LOW_VALUE_OVERLAP_OR_FORMAL_COST"
        else:
            reason = "LOW_VALUE_OVERLAP"
        reasons[reason] += 1
    return dict(sorted(reasons.items()))


def _candidate_gate(properties: list[PropertyIR], result: Any | None) -> dict[str, Any]:
    if result is None:
        return {
            "generated": len(properties), "pass": 0, "cex": 0,
            "timeout_accepted": 0, "not_evaluated": len(properties),
            "accepted_correct": 0,
            "vacuous": 0, "non_vacuous": 0, "trusted": 0,
            "proven_rate_percent": 0.0, "accepted_correct_rate_percent": 0.0,
            "trusted_rate_percent": 0.0,
        }
    return result_counts(properties, result.results)


def _filter_renderable_properties(
    properties: list[PropertyIR], design: RTLDesign,
) -> tuple[list[PropertyIR], list[dict[str, Any]]]:
    """Reject graph candidates whose parsed signal cannot be bound into SVA."""

    accepted = []
    rejected = []
    for prop in properties:
        # An RTL intra-assignment delay is a timing control, not a value
        # expression. Never silently strip it or put it inside $past().
        # Apply the same conservative rule as initial RTL grounding to the
        # legacy feedback path too; otherwise one bad binding aborts a batch.
        delayed_values = {
            key: value for key, value in prop.bindings.items()
            if isinstance(value, str) and re.match(r"\s*#(?!#)", value)
        }
        if delayed_values or re.search(r"\$past\s*\(\s*#", prop.body):
            rejected.append({
                "property_id": prop.property_id,
                "target_module": prop.target_module,
                "reason": "INTRA_ASSIGNMENT_DELAY_NOT_A_VALUE_EXPRESSION",
                "unsupported_bindings": delayed_values,
                "missing_signals": [],
                "evidence": prop.evidence,
            })
            continue
        if "`" in prop.body:
            rejected.append({
                "property_id": prop.property_id,
                "target_module": prop.target_module,
                "reason": "PREPROCESSOR_MACRO_NOT_LEGAL_IN_STANDALONE_CHECKER",
                "missing_signals": [],
            })
            continue
        available = set(design.module_signals.get(prop.target_module, {}))
        missing = sorted(set(prop.signals) - available)
        if missing:
            rejected.append({
                "property_id": prop.property_id,
                "target_module": prop.target_module,
                "reason": "SIGNAL_NOT_BINDABLE_IN_PARSED_MODULE",
                "missing_signals": missing,
            })
        else:
            accepted.append(prop)
    return accepted, rejected


def _map_behavior_supporting_regions(
    behaviors: list[dict[str, Any]], inventory: dict[str, Any],
    design: RTLDesign, module: str,
) -> list[dict[str, Any]]:
    """Add conservative SPEC-to-Region trace links for non-compilable prose.

    A behavior that cannot be lowered to an assertion is not promoted to
    DIRECT_SPEC_CONFORMANCE.  It may still support an RTL assertion when its
    quoted evidence names real signals contained by a Region.  This join is
    deterministic and records the exact identifiers used.
    """

    all_regions = [
        item for item in inventory.get("regions", []) if item.get("kind") != "MODULE"
    ]
    # Full-CPU documentation commonly names child-module ports rather than
    # top-level ports.  Exact identifiers are therefore resolved throughout
    # the already-elaborated hierarchy, while the Region join still requires
    # that identifier to be a member of the matched Region.
    known = {
        name for signals in design.module_signals.values() for name in signals
    }
    hint_to_region_kinds = {
        "CONTROL_FSM": {"FSM"},
        "DECODE": {"DECODE"},
        "PIPELINE_FLOW": {"PIPELINE", "REGISTER_UPDATE"},
        "HANDSHAKE_REQUEST_RESPONSE": {"HANDSHAKE"},
        "REGISTER_UPDATE": {"REGISTER_UPDATE"},
        "DATAPATH": {"DATAPATH"},
        "FETCH_FRONTEND": {"PIPELINE", "REGISTER_UPDATE"},
        "MEMORY_CONTROL": {"FSM", "REGISTER_UPDATE"},
        "WRITEBACK": {"PIPELINE", "REGISTER_UPDATE"},
        "QUEUE_BUFFER": {"FSM", "REGISTER_UPDATE"},
        "RESOURCE_ARBITRATION": {"FSM", "DECODE"},
    }
    output = deepcopy(behaviors)
    for behavior in output:
        mapping = behavior.setdefault("rtl_mapping", {})
        if mapping.get("status") == "MAPPED":
            continue
        evidence = behavior.get("evidence", {})
        text = " ".join((
            str(evidence.get("quote", "")),
            str(behavior.get("functional_meaning", "")),
        ))
        identifiers = set(re.findall(r"\b[A-Za-z_$][A-Za-z0-9_$]*\b", text)) & known
        ranked = []
        if identifiers:
            for region in all_regions:
                overlap = identifiers & set(region.get("signals", []))
                if overlap:
                    ranked.append((len(overlap), str(region.get("region_id", "")), overlap))
        if ranked:
            best = max(score for score, _, _ in ranked)
            # Keep every equally strongest match. Truncating ties by lexical
            # Region ID can silently discard the Region that owns a later trusted
            # assertion, making traceability depend on filename ordering.
            selected = [item for item in ranked if item[0] == best]
            mapping.update({
                "status": "EVIDENCE_IDENTIFIER_MAPPED",
                "region_ids": [region_id for _, region_id, _ in selected],
                "matching_signals": sorted(set().union(*(overlap for _, _, overlap in selected))),
                "mapping_basis": "exact RTL identifiers in cited SPEC evidence",
                "directly_compilable": False,
            })
            continue

        # Full-CPU documents often specify architectural stages without RTL
        # signal names. Preserve that evidence as a non-compilable, supporting
        # link to graph-discovered Region kinds. The LLM-provided hint cannot
        # create SVA or establish conformance; it only chooses among the fixed
        # ontology roles and the deterministic graph performs the join.
        hint = str(behavior.get("core_region_hint", "")).upper()
        compatible_kinds = hint_to_region_kinds.get(hint, set())
        hinted = sorted(
            str(region.get("region_id", "")) for region in all_regions
            if str(region.get("kind", "")).upper() in compatible_kinds
        )
        if hinted:
            mapping.update({
                "status": "EVIDENCE_REGION_HINT_MAPPED",
                "region_ids": hinted,
                "matching_signals": [],
                "mapping_basis": "validated official quote + fixed ontology Region kind",
                "directly_compilable": False,
            })
    return output


def _assertion_traceability(
    staged: list[tuple[str, list[PropertyIR], Any | None]],
    final_properties: list[PropertyIR], metadata: dict[str, dict[str, Any]],
    mapped_spec: list[dict[str, Any]], local_contracts: dict[str, Any],
) -> dict[str, Any]:
    """Join candidate/final Formal results to exact SPEC and Region evidence."""

    final_ids = {item.property_id for item in final_properties}
    contract_regions = {
        str(item.get("contract_id")): str(item.get("region_id", ""))
        for item in local_contracts.get("contracts", [])
    }
    behavior_regions = {
        str(item.get("behavior_id")): set(item.get("rtl_mapping", {}).get("region_ids", []))
        for item in mapped_spec
        if item.get("rtl_mapping", {}).get("status") in {
            "MAPPED", "EVIDENCE_IDENTIFIER_MAPPED", "EVIDENCE_REGION_HINT_MAPPED",
        }
    }
    behavior_by_id = {str(item.get("behavior_id")): item for item in mapped_spec}
    records = []
    seen: set[str] = set()
    for stage, properties, formal in staged:
        results = {item.property_id: item for item in formal.results} if formal else {}
        for prop in properties:
            if prop.property_id in seen:
                continue
            seen.add(prop.property_id)
            item_metadata = metadata.get(prop.property_id, {})
            regions = set(item_metadata.get("region_ids", []))
            if prop.region_id and not prop.region_id.startswith("contract_composition_"):
                regions.add(prop.region_id)
            for contract_id in item_metadata.get("contract_ids", []):
                if contract_regions.get(str(contract_id)):
                    regions.add(contract_regions[str(contract_id)])
            for role in ("SOURCE_CONTRACT_ID", "TARGET_CONTRACT_ID"):
                contract_id = prop.bindings.get(role)
                if contract_id and contract_regions.get(str(contract_id)):
                    regions.add(contract_regions[str(contract_id)])
            direct_id = item_metadata.get("behavior_id")
            if direct_id:
                spec_ids = [str(direct_id)]
                mapping = "DIRECT_SPEC_CONFORMANCE"
            else:
                spec_ids = sorted(
                    behavior_id for behavior_id, mapped_regions in behavior_regions.items()
                    if regions & mapped_regions
                )
                mapping = "SPEC_SUPPORTING_RTL" if spec_ids else "RTL_ONLY_NO_DIRECT_SPEC_EVIDENCE"
            result = results.get(prop.property_id)
            records.append({
                "property_id": prop.property_id,
                "stage": stage,
                "source_classification": prop.source_classification,
                "target_module": prop.target_module,
                "region_ids": sorted(regions),
                "spec_mapping": mapping,
                "spec_behavior_ids": spec_ids,
                "spec_evidence": [
                    behavior_by_id[behavior_id].get("evidence", {})
                    for behavior_id in spec_ids if behavior_id in behavior_by_id
                ],
                "candidate_result": result.result if result else "NOT_RUN",
                "candidate_vacuity": result.vacuity if result else "NOT_EVALUATED",
                "in_final_trusted_portfolio": prop.property_id in final_ids,
            })
    final_records = [item for item in records if item["in_final_trusted_portfolio"]]
    return {
        "schema": "region_flow.10-assertion-spec-traceability.v1",
        "records": records,
        "summary": {
            "candidate_assertions": len(records),
            "final_trusted_assertions": len(final_records),
            "final_by_source_classification": dict(Counter(
                item["source_classification"] for item in final_records
            )),
            "final_by_spec_mapping": dict(Counter(
                item["spec_mapping"] for item in final_records
            )),
        },
    }


def _seed_spec_call_cache(source: Path, destination: Path) -> None:
    """Copy missing aggregate/chunk calls only; extraction revalidates context."""
    if not source.is_file():
        return
    records = [source, *sorted((source.parent / "chunks").glob("*/calls.json"))]
    for record in records:
        target = destination.parent / record.relative_to(source.parent)
        if not target.is_file():
            dump_json(target, json.loads(record.read_text(encoding="utf-8")))


def _llm_provider_name(llm_config: dict[str, Any]) -> str:
    """Return the configured provider label for run metadata only."""

    return str(llm_config.get("provider") or "deepseek")


def _initial_sva_deduplication_enabled(config: dict[str, Any]) -> bool:
    """Preserve exact-SVA deduplication unless Req12 explicitly disables it."""

    return bool(config.get("feedback", {}).get("deduplicate_sva", True))


def _initial_exact_sva_deduplication(
    properties: list[PropertyIR], bindings: list[Any], metadata: dict[str, dict[str, Any]], *,
    enabled: bool,
) -> tuple[list[PropertyIR], list[Any], dict[str, dict[str, Any]], list[dict[str, Any]]]:
    """Apply the legacy exact-body filter unless the Req12 experiment opts out.

    Candidate selection and semantic/rendering/Formal gates are outside this
    narrow operation.  Disabling it retains every selected Local record and
    its provenance without widening selection or accepting invalid SVA.
    """

    if enabled:
        return deduplicate_exact_properties(properties, bindings, metadata)
    audit = [{
        "property_id": prop.property_id,
        "disposition": "RETAINED_DEDUPLICATION_DISABLED",
        "target_module": prop.target_module,
        "body": prop.body,
    } for prop in properties]
    return properties, bindings, metadata, audit


def _run_design(
    target: dict[str, Any], config: dict[str, Any], output: Path,
) -> dict[str, Any]:
    started = time.monotonic()
    req = config["design_flow"]
    top = str(target["top"])
    design_id = str(target["design_id"])
    root = output / design_id
    root.mkdir(parents=True, exist_ok=True)
    files = [str(_resolve(item)) for item in target["rtl_files"]]
    include_dirs = [str(_resolve(item)) for item in target.get("include_dirs", [])]
    local_config = _formal_config(config, target)
    reset = str(target["reset"])
    reset_asserted = f"!{reset}" if target["reset_active_low"] else reset

    design = parse_rtl(files, include_dirs=include_dirs)
    graph = build_semantic_graph(design)
    design_map = build_hierarchical_design_map(design, graph, top, include_dirs=include_dirs)
    reachable_modules = {
        str(item["module"]) for item in design_map.get("instances", [])
        if item.get("module")
    } or {top}
    scope_modules = (
        reachable_modules
        if target.get("validation_scope") == "full_cpu"
        else {top}
    )
    base_regions = _scope_regions(
        build_verification_regions(design, graph, design_map,
            max_candidates_per_kind=req.get("max_candidates_per_kind_per_module"),
            matching_backend=req.get("graph_matching_backend", "attributed_vf2")), scope_modules,
    )
    stimuli = (
        _independent_stimuli_coverage(design, top, root, local_config)
        if req.get("collect_stimuli_coverage", False)
        else {"run": {"enabled": False}, "coverage": {}}
    )
    design.save(root / "rtl_structure.json")
    dump_json(root / "typed_semantic_graph.json", graph)
    dump_json(root / "design_map.json", design_map)
    dump_json(root / "base_regions.json", base_regions)

    spec_cfg = target["spec"]
    spec_module = str(spec_cfg.get("target_module", top))
    if spec_module not in reachable_modules:
        raise RuntimeError(
            f"{design_id}: SPEC target module {spec_module!r} is not reachable from {top!r}"
        )
    spec_path, retrieval_record = _materialize_official_spec(spec_cfg, local_config["llm"])
    selected_spec = spec_lines(spec_path, spec_cfg["line_ranges"])
    (root / "spec").mkdir(parents=True, exist_ok=True)
    snapshot = root / "spec" / spec_path.name
    shutil.copyfile(spec_path, snapshot)
    dump_json(root / "spec" / "selected_evidence.json", selected_spec)
    spec_record = {
        "source_url": spec_cfg["source_url"],
        "repository_revision": spec_cfg["repository_revision"],
        "repository_path": spec_cfg["repository_path"],
        "local_source": str(spec_path),
        "snapshot": str(snapshot),
        "local_sha256": _sha256(spec_path),
        "snapshot_sha256": _sha256(snapshot),
        "selected_line_ranges": spec_cfg["line_ranges"],
        "snapshot_exact_copy": _sha256(spec_path) == _sha256(snapshot),
        "document_scope": spec_cfg.get("document_scope", "local_module"),
        "requested_topics": list(spec_cfg.get("requested_topics", [])),
        **retrieval_record,
    }

    llm_provider = _llm_provider_name(local_config["llm"])
    client = DeepSeekClient(_llm_config(local_config["llm"]))
    extension_prompt = (
        PROJECT_ROOT / "llm" / "prompts" / "extension_regions.txt"
    ).read_text(encoding="utf-8")
    extensions, discovery_llm = _discover_extensions(
        base_regions, design, selected_spec, client, extension_prompt,
        root / "llm" / "extension_regions",
        limit=int(req.get("extension_llm_limit", 1)),
        attempts=int(req.get("llm_validation_attempts", 4)),
    )
    spec_prompt = (PROJECT_ROOT / "llm" / "prompts" / "spec_behaviors.txt").read_text(encoding="utf-8")
    cached_calls = spec_cfg.get("validated_calls_cache")
    calls_path = root / "llm" / "spec_extraction" / "calls.json"
    if cached_calls:
        cached_path = _resolve(str(cached_calls))
        _seed_spec_call_cache(cached_path, calls_path)
    spec_doc, spec_llm = _extract_spec(
        spec_path, selected_spec, design, spec_module, client, spec_prompt,
        root / "llm" / "spec_extraction",
        attempts=int(req.get("llm_validation_attempts", 4)),
        max_context_chars=int(req.get("max_spec_context_chars", 24_000)),
    )
    spec_expansion_audit: list[dict[str, Any]] = []
    if req.get("expand_spec_obligations", False):
        spec_doc, spec_expansion_audit = expand_spec_behavior_obligations(spec_doc)
    dump_json(root / "spec" / "obligation_expansion_audit.json", spec_expansion_audit)

    initial_inventory = build_region_inventory(base_regions, extensions)
    mapped_spec, overlays = map_spec_behaviors_to_regions(spec_doc, initial_inventory, spec_module)
    region_inventory = build_region_inventory(base_regions, extensions, overlays)
    mapped_spec, _ = map_spec_behaviors_to_regions(
        {"behaviors": mapped_spec}, region_inventory, spec_module,
    )
    mapped_spec = _map_behavior_supporting_regions(
        mapped_spec, region_inventory, design, spec_module,
    )
    dump_json(root / "regions.json", region_inventory)
    dump_json(root / "spec_behaviors.json", {
        **spec_doc, "behaviors": mapped_spec, "source": str(spec_path),
        "source_sha256": spec_record["local_sha256"],
    })

    pool, rejections, pool_summary = build_property_candidate_pool(
        design, graph, design_map, {"regions": region_inventory["regions"]},
        {"reset": reset, "reset_active_low": target["reset_active_low"]},
    )
    bindings = enumerate_local_candidate_bindings(
        pool, region_inventory, design, reset_asserted,
        recall_mode=bool(req.get("local_recall_mode", False)),
    )
    # Hierarchy scope is resolved structurally from the configured CPU top.
    bindings = [
        item for item in bindings
        if item.candidate.module in scope_modules
    ]
    if req.get("balanced_local_selection", False):
        from dateassertion.pipeline.portfolio_balance import select_balanced_local_bindings
        selected, selection_audit = select_balanced_local_bindings(
            bindings, budget=int(req.get("balanced_local_budget", 128)),
            fraction=float(req.get("balanced_local_fraction", 0.5)),
            minimum=int(req.get("balanced_local_minimum", 20)),
        )
    else:
        selected, selection_audit = select_local_candidate_bindings(
            bindings,
            budget=int(req.get("rtl_property_budget", 10)),
            primitive_caps=req.get("primitive_caps", {}),
            minimum_count=int(req.get("minimum_rtl_properties", 3)),
            selection_policy=str(req.get(
                "local_candidate_selection_policy", "primary_region_marginal",
            )),
        )
    rtl_candidates, rtl_bindings, rtl_metadata = compile_rtl_properties(
        selected, design, reset_asserted,
    )
    if req.get("architecture_contracts_enabled", True):
        from dateassertion.pipeline.architecture_contracts import compile_architecture_contracts
        extra, extra_bindings, extra_metadata, extra_audit = compile_architecture_contracts(
            design, graph, region_inventory, reset_asserted)
        rtl_candidates.extend(extra)
        rtl_bindings.extend(extra_bindings)
        rtl_metadata.update(extra_metadata)
        dump_json(root / "architecture_contracts.json", extra_audit)
    spec_candidates, spec_bindings, spec_metadata = compile_spec_properties(
        mapped_spec, design, spec_module, reset_asserted, spec_path,
    )
    initial_sva_deduplication_enabled = _initial_sva_deduplication_enabled(config)
    rtl_candidates, rtl_bindings, rtl_metadata, rtl_duplicate_audit = (
        _initial_exact_sva_deduplication(
            rtl_candidates, rtl_bindings, rtl_metadata,
            enabled=initial_sva_deduplication_enabled,
        )
    )
    spec_candidates, spec_bindings, spec_metadata, spec_duplicate_audit = (
        _initial_exact_sva_deduplication(
            spec_candidates, spec_bindings, spec_metadata,
            enabled=initial_sva_deduplication_enabled,
        )
    )
    if not rtl_candidates:
        raise RuntimeError(f"{design_id}: generic graph pipeline generated no local RTL property")
    dump_json(root / "candidate_pool_summary.json", pool_summary)
    dump_json(root / "candidate_rejections.json", rejections)
    dump_json(root / "candidate_selection.json", selection_audit)
    dump_json(root / "exact_sva_duplicate_audit.json", {
        "schema": "obligation_expansion-exact-sva-duplicate-audit.v1",
        "policy": (
            "exact module+disable+PropertyIR-body duplicate removal only"
            if initial_sva_deduplication_enabled else
            "disabled by feedback.deduplicate_sva=false; selected Local records retained"
        ),
        "enabled": initial_sva_deduplication_enabled,
        "rtl": rtl_duplicate_audit,
        "spec": spec_duplicate_audit,
        "composition_body_deduplication_performed": False,
        "removed": sum(
            item.get("disposition") == "REMOVED_EXACT_DUPLICATE_SVA"
            for item in rtl_duplicate_audit + spec_duplicate_audit
        ),
    })
    dump_json(root / "template_bindings.json", rtl_bindings + spec_bindings)
    dump_json(root / "local_candidates.json", rtl_candidates + spec_candidates)

    # Ablation A, arm 1: RTL only.  Probe candidates and rerun the exact
    # trusted subset whenever the gate rejects anything.
    rtl_probe = _formal(
        design, rtl_candidates, top, root / "formal" / "rtl_only_probe", local_config,
        measure_proof_coverage=False,
    )
    rtl_trusted = _passed(rtl_candidates, rtl_probe.results)
    rtl_trusted, rtl_final, rtl_stable = _stable_formal(
        design, [], rtl_trusted, top, root / "formal" / "rtl_only", local_config,
        candidate_probe=rtl_probe, graph=graph,
    )
    rtl_items = parse_coverage_items(root / "formal" / "rtl_only" / "formal" / "coverage_items.tsv")

    # Ablation A, arm 2: add independently extracted SPEC obligations.
    spec_probe = _formal(
        design, spec_candidates, top, root / "formal" / "spec_probe", local_config,
        measure_proof_coverage=False,
    ) if spec_candidates else None
    spec_trusted = _passed(spec_candidates, spec_probe.results) if spec_probe else []
    combined_candidates = rtl_trusted + spec_trusted
    combined_trusted, local_final, local_stable = _stable_formal(
        design, [], combined_candidates, top,
        root / "formal" / "spec_plus_rtl_local", local_config,
        candidate_probe=_combined_probe(rtl_final, spec_probe), graph=graph,
    )
    local_items = parse_coverage_items(
        root / "formal" / "spec_plus_rtl_local" / "formal" / "coverage_items.tsv"
    )
    combined_ids = {item.property_id for item in combined_trusted}
    trusted_rtl = [item for item in rtl_trusted if item.property_id in combined_ids]
    trusted_spec = [item for item in spec_trusted if item.property_id in combined_ids]
    all_metadata = {**rtl_metadata, **spec_metadata}
    local_probe_results = list(rtl_probe.results) + (
        list(spec_probe.results) if spec_probe else []
    )
    obligation_funnel = build_obligation_funnel(
        region_inventory, bindings, rtl_candidates + spec_candidates,
        all_metadata, local_probe_results, combined_ids,
    )
    dump_json(root / "obligation_funnel.json", obligation_funnel)

    # Local Contracts and Req8.8 composition use exactly the same builders on
    # all targets.  The LLM may only bind SPEC evidence to supplied events.
    local_contracts = build_local_contracts(
        region_inventory, combined_trusted, all_metadata, graph, design,
    )
    dump_json(root / "local_contracts.json", local_contracts)
    if req.get("balanced_composition_enabled", False):
        composition_context = {
            "schema": "feedback-balanced-composition-context-index.v1",
            "strategy": "bounded typed event pairs and continuous event chains",
            "actual_contexts_directory": str(root / "llm" / "composition_expansion"),
            "whole_design_rtl_supplied": False,
        }
    else:
        composition_context = package_spec_composition_context(
            selected_spec, local_contracts,
            max_contracts=int(req.get("max_contracts_for_llm", 24)),
            max_context_chars=int(req.get("max_composition_context_chars", 32_000)),
        )
    dump_json(root / "llm" / "composition_context.json", composition_context)
    composition_llm: dict[str, Any]
    composition_error = ""
    constraints: dict[str, Any] = {"constraints": [], "lifecycle_chains": []}
    try:
        composition_prompt = (PROJECT_ROOT / "llm" / "prompts" / "composition_constraints.txt").read_text(encoding="utf-8")
        if req.get("balanced_composition_enabled", False):
            from dateassertion.pipeline.composition_expansion import expand_initial_composition
            composition_config = deepcopy(local_config)
            composition_config.setdefault("feedback", {})["initial_generated_local_sva"] = (
                len(rtl_candidates) + len(spec_candidates)
            )
            constraints, composition_llm = expand_initial_composition(
                client, composition_prompt, selected_spec, local_contracts,
                design, root / "llm" / "composition_expansion", composition_config,
            )
        else:
            constraints, composition_llm = _validated_llm_constraints(
                client, composition_prompt, composition_context,
                root / "llm" / "composition_calls.json",
                attempts=int(req.get("llm_validation_attempts", 4)),
                maximum_delay=int(req.get("maximum_composition_delay", 96)),
            )
    except LLMUnavailableError as exc:
        composition_error = f"{type(exc).__name__}: {exc}"
        dump_json(root / "llm" / "composition_external_service_failure.json", {
            "status": "INTERRUPTED_EXTERNAL_SERVICE",
            "stage": "COMPOSITION_BINDING",
            "error": composition_error,
        })
        # A billing/auth/transport outage provides no semantic evidence.  Do
        # not silently continue with an empty composition portfolio.
        raise
    except Exception as exc:
        composition_error = f"{type(exc).__name__}: {exc}"
        calls_path = root / "llm" / "composition_calls.json"
        calls = (
            json.loads(calls_path.read_text(encoding="utf-8"))
            if calls_path.is_file() else []
        )
        composition_llm = {
            "provider": llm_provider, "calls": len(calls), "api_calls_this_run": len(calls),
            "real_response_artifacts": sum(
                bool(item.get("metadata", {}).get("request_id"))
                and item.get("metadata", {}).get("response_model") not in {None, "", "fake"}
                for item in calls
            ),
            "response_models": sorted({
                str(item.get("metadata", {}).get("response_model")) for item in calls
                if item.get("metadata", {}).get("response_model")
            }),
            "generated_sva": False,
            "validation_error": composition_error,
        }
    dump_json(root / "partial_order_constraints.json", constraints)
    contract_graph = build_contract_graph(local_contracts, constraints)
    candidate_doc = generate_composition_candidates(contract_graph, constraints)
    selected_composition, composition_portfolio = select_composition_portfolio(
        candidate_doc, caps=req.get("composition_caps", {}),
    )
    composition_candidates, composition_metadata = compile_composition_properties(
        selected_composition, design, reset_asserted,
    ) if selected_composition else ([], {})
    dump_json(root / "contract_graph.json", contract_graph)
    dump_json(root / "composition_candidates.json", candidate_doc)
    dump_json(root / "composition_properties.json", composition_candidates)

    composition_probe = _formal(
        design, composition_candidates, top, root / "formal" / "composition_probe", local_config,
        measure_proof_coverage=False,
    ) if composition_candidates else None
    trusted_composition = _passed(
        composition_candidates, composition_probe.results,
    ) if composition_probe else []
    no_feedback_candidates = combined_trusted + trusted_composition
    no_feedback_trusted, no_feedback_final, no_feedback_stable = _stable_formal(
        design, [], no_feedback_candidates, top,
        root / "formal" / "without_feedback", local_config,
        candidate_probe=_combined_probe(local_final, composition_probe), graph=graph,
    )
    no_feedback_items = parse_coverage_items(
        root / "formal" / "without_feedback" / "formal" / "coverage_items.tsv"
    )
    no_feedback_ids = {item.property_id for item in no_feedback_trusted}
    trusted_composition = [
        item for item in trusted_composition if item.property_id in no_feedback_ids
    ]

    # Ablation B: Req8.9 Formal-gap feedback over the exact no-feedback run.
    initial_mapping = refine_gap_classification(
        localize_coverage_gaps(no_feedback_items, graph, region_inventory["regions"]),
        graph, region_inventory["regions"],
        priority_threshold=float(req.get("gap_priority_threshold", 7.0)),
    )
    refinement_regions = []
    refinement_candidates = []
    refinement_metadata = {}
    refinement_llm = {}
    if req.get("region_refinement_enabled", False):
        initial_mapping = localize_refinement_gaps(no_feedback_items, graph, region_inventory["regions"])
        motifs = discover_refinement_candidates(
            initial_mapping, graph, region_inventory["regions"],
            max_regions=int(req.get("refinement_region_limit", 32)),
            max_assignments=int(req.get("refinement_max_assignments", 16)),
            depth=int(req.get("refinement_graph_depth", 2)),
        )
        dump_json(root / "feedback" / "refinement_candidates.json", motifs)
        refinement_regions, refinement_llm = interpret_refinements(
            motifs, region_inventory["regions"], selected_spec, client,
            root / "llm" / "refinement", attempts=int(req.get("llm_validation_attempts", 4)),
        )
        refinement_candidates, refinement_metadata = compile_refinement_properties(
            pool, refinement_regions, design, reset_asserted, root / "feedback" / "refinement",
        )
        dump_json(root / "feedback" / "extension_region_registry.json", {
            "schema": "region_refinement-design-local-registry.v1", "source_digest": design.source_digest,
            "regions": refinement_regions, "core_ontology_modified": False,
        })
    dump_json(root / "feedback" / "initial_gap_mapping.json", initial_mapping)
    initial_gap = gap_summary(initial_mapping)
    eligible = [row for row in initial_mapping if row["priority"]["eligible_for_refinement"]]
    region_feedback_candidates: list[PropertyIR] = []
    extension_region: dict[str, Any] | None = None
    extension_llm: dict[str, Any] = {
        "provider": llm_provider, "calls": 0, "api_calls_this_run": 0,
        "real_response_artifacts": 0, "generated_sva": False,
        "reason": "NO_HIGH_VALUE_NEW_REGION_GAP",
    }
    new_region_rows = [
        row for row in eligible
        if row.get("gap_type") == "A_REGION_GAP" and row.get("type_a_subtype") == "NEW_REGION"
    ]
    if new_region_rows:
        residual = select_residual_region_candidate(
            new_region_rows, graph, design,
            max_assignments=int(req.get("feedback_property_budget", 3)),
        )
        nearby = [
            region for region in region_inventory["regions"]
            if region.get("module") == residual["module"]
            and set(region.get("signals", [])) & set(residual["signals"])
        ]
        extension_context = package_extension_interpretation_context(
            residual, nearby, selected_spec,
        )
        dump_json(root / "llm" / "extension_context.json", extension_context)
        extension_prompt = (PROJECT_ROOT / "llm" / "prompts" / "gap_interpretation.txt").read_text(encoding="utf-8")
        interpretation, extension_llm = _validated_llm_interpretation(
            client, extension_prompt, extension_context,
            root / "llm" / "extension_calls.json",
            attempts=int(req.get("llm_validation_attempts", 4)),
        )
        extension_region = extension_region_from_interpretation(residual, interpretation)
        region_feedback_candidates.extend(compile_region_gap_properties(
            residual, graph, 1, reset_asserted=reset_asserted,
        )[: int(req.get("region_property_limit", 8))])
        dump_json(root / "feedback" / "extension_region.json", extension_region)

    contract_rows = select_contract_gap_assignments(
        eligible, graph, focus_modules=sorted(scope_modules),
        limit=int(req.get("contract_property_limit", 5)),
    )
    contract_feedback_candidates: list[PropertyIR] = []
    for index, (node, region_ids, _cids) in enumerate(contract_rows, 1):
        contract_feedback_candidates.append(property_from_assignment(
            node, region_ids[0], f"req810_contract_{index:03d}", 2,
            reset_asserted=reset_asserted,
        ))
    feedback_candidates = refinement_candidates + region_feedback_candidates + contract_feedback_candidates
    def exact_key(item):
        return (item.target_module, "".join(item.disable_iff.split()), "".join(item.body.split()))
    seen_bodies = {exact_key(item) for item in no_feedback_trusted}
    deduplicated = []
    for prop in feedback_candidates:
        signature = exact_key(prop)
        if signature in seen_bodies:
            continue
        seen_bodies.add(signature)
        deduplicated.append(prop)
    feedback_candidates = deduplicated[: int(req.get("feedback_property_budget", 3))]
    feedback_candidates, feedback_binding_rejections = _filter_renderable_properties(
        feedback_candidates, design,
    )
    dump_json(root / "feedback" / "generated_properties.json", feedback_candidates)
    dump_json(root / "feedback" / "binding_rejections.json", feedback_binding_rejections)

    feedback_probe = _formal(
        design, feedback_candidates, top, root / "formal" / "feedback_probe", local_config,
        measure_proof_coverage=False,
    ) if feedback_candidates else None
    trusted_local_feedback = _passed(
        feedback_candidates, feedback_probe.results,
    ) if feedback_probe else []
    trusted_local_ids = {item.property_id for item in trusted_local_feedback}
    trusted_contract_properties = [
        item for item in contract_feedback_candidates
        if item.property_id in trusted_local_ids
    ]
    trusted_contract_rows = [
        row for index, row in enumerate(contract_rows, 1)
        if f"req810_contract_{index:03d}" in trusted_local_ids
    ]
    feedback_composition_candidates: list[PropertyIR] = []
    feedback_composition_probe = None
    feedback_composition_reason = "NO_TRUSTED_CONTRACT_REFINEMENT"
    if trusted_contract_properties and trusted_contract_rows:
        refined = refine_local_contract(
            local_contracts["contracts"], trusted_contract_rows,
            trusted_contract_properties, 2,
        )
        try:
            feedback_relation, feedback_composition = compile_completion_composition(
                refined, local_contracts["contracts"], graph, 3,
                reset_asserted=reset_asserted,
            )
            feedback_composition_candidates = [feedback_composition]
            feedback_composition_candidates, composition_binding_rejections = _filter_renderable_properties(
                feedback_composition_candidates, design,
            )
            if composition_binding_rejections:
                feedback_composition_reason = "SIGNAL_NOT_BINDABLE_IN_PARSED_MODULE"
                dump_json(
                    root / "feedback" / "composition_binding_rejections.json",
                    composition_binding_rejections,
                )
            dump_json(root / "feedback" / "composition_relation.json", feedback_relation)
            feedback_composition_probe = _formal(
                design, feedback_composition_candidates, top,
                root / "formal" / "feedback_composition_probe", local_config,
                measure_proof_coverage=False,
            ) if feedback_composition_candidates else None
            if feedback_composition_candidates:
                feedback_composition_reason = "CANDIDATE_GENERATED"
        except RuntimeError as exc:
            feedback_composition_reason = str(exc)
    trusted_feedback_composition = _passed(
        feedback_composition_candidates, feedback_composition_probe.results,
    ) if feedback_composition_probe else []
    trusted_feedback = trusted_local_feedback + trusted_feedback_composition
    dump_json(root / "feedback" / "generated_composition_properties.json", feedback_composition_candidates)
    if feedback_candidates:
        final_properties_input = no_feedback_trusted + trusted_feedback
        final_properties, final_result, feedback_stable = _stable_formal(
            design, [], final_properties_input, top,
            root / "formal" / "with_feedback", local_config,
            candidate_probe=_combined_probe(
                no_feedback_final, feedback_probe, feedback_composition_probe,
            ), graph=graph,
        )
        final_ids = {item.property_id for item in final_properties}
        trusted_feedback = [
            item for item in trusted_feedback if item.property_id in final_ids
        ]
        final_formal_root = root / "formal" / "with_feedback"
        final_items = parse_coverage_items(
            final_formal_root / "formal" / "coverage_items.tsv"
        )
    else:
        # An empty feedback portfolio is a legitimate "no actionable gap"
        # outcome. Reusing the exact without-feedback run prevents solver
        # proof-core ordering noise from being reported as feedback gain.
        final_result = no_feedback_final
        feedback_stable = [{
            "round": 0,
            "fixed": len(no_feedback_trusted),
            "candidate_input": 0,
            "candidate_survivors": 0,
            "removed_property_ids": [],
            "reused_without_feedback_result": True,
        }]
        final_formal_root = root / "formal" / "without_feedback"
        final_items = no_feedback_items
        for stale in (
            root / "formal" / "feedback_probe",
            root / "formal" / "with_feedback",
        ):
            if stale.exists():
                shutil.rmtree(stale)
    if not feedback_candidates:
        final_properties = no_feedback_trusted + trusted_feedback
    final_regions = list(region_inventory["regions"])
    final_regions.extend(refinement_regions)
    if extension_region and trusted_feedback:
        final_regions.append(extension_region)
    final_mapping = refine_gap_classification(
        localize_coverage_gaps(final_items, graph, final_regions),
        graph, final_regions,
        priority_threshold=float(req.get("gap_priority_threshold", 7.0)),
    )
    if req.get("region_refinement_enabled", False):
        final_mapping = localize_refinement_gaps(final_items, graph, final_regions)
    dump_json(root / "feedback" / "final_gap_mapping.json", final_mapping)
    final_gap = gap_summary(final_mapping)
    dump_json(root / "final" / "regions.json", {"regions": final_regions})
    dump_json(root / "final" / "trusted_properties.json", final_properties)
    traceability = _assertion_traceability(
        [
            ("LOCAL_RTL", rtl_candidates, rtl_probe),
            ("LOCAL_SPEC", spec_candidates, spec_probe),
            ("COMPOSITION", composition_candidates, composition_probe),
            ("FEEDBACK_LOCAL", feedback_candidates, feedback_probe),
            ("FEEDBACK_COMPOSITION", feedback_composition_candidates, feedback_composition_probe),
        ],
        final_properties,
        {**all_metadata, **composition_metadata, **refinement_metadata},
        mapped_spec,
        local_contracts,
    )
    dump_json(root / "assertion_spec_traceability.json", traceability)

    baseline_checked, final_checked = _checked(no_feedback_items), _checked(final_items)
    if len(no_feedback_items) != len(final_items):
        raise RuntimeError(f"{design_id}: coverage denominator changed in feedback ablation")
    if len(_trusted(final_properties, final_result.results)) != len(final_properties):
        raise RuntimeError(f"{design_id}: final Trust Gate is not PASS + NON_VACUOUS")
    sva_text = (final_formal_root / "assertions.sv").read_text(encoding="utf-8")
    if "assume property" in sva_text:
        raise RuntimeError(f"{design_id}: unproven assumption entered final SVA")

    updated_region_metrics = _region_metrics(
        {"regions": final_regions}, graph, design_map, scope_modules,
    )
    feedback_gain = {
        "new_checked_items": len(final_checked - baseline_checked),
        "lost_checked_items": len(baseline_checked - final_checked),
        "net_checked_items": len(final_checked) - len(baseline_checked),
        "denominator_constant": len(no_feedback_items) == len(final_items),
        "denominator_constant_definition": "total instrumented cover-item count, not effective reachable denominator",
        "item_universe_constant": {stable_cover_item_id(x) for x in no_feedback_items} == {stable_cover_item_id(x) for x in final_items},
        "effective_denominator_before": coverage_by_type(no_feedback_items)["all"]["effective_reachable_denominator"],
        "effective_denominator_after": coverage_by_type(final_items)["all"]["effective_reachable_denominator"],
        "effective_denominator_constant": coverage_by_type(no_feedback_items)["all"]["effective_reachable_denominator"] == coverage_by_type(final_items)["all"]["effective_reachable_denominator"],
        "raw_percent_points": round(
            coverage_by_type(final_items)["all"]["raw_percent"]
            - coverage_by_type(no_feedback_items)["all"]["raw_percent"], 2,
        ),
        "effective_percent_points": round(
            coverage_by_type(final_items)["all"]["effective_percent"]
            - coverage_by_type(no_feedback_items)["all"]["effective_percent"], 2,
        ),
    }
    baseline_comparison: dict[str, Any] = {}
    baseline_root_value = str(req.get("obligation_expansion_baseline_root", "")).strip()
    if baseline_root_value:
        baseline_root = _resolve(baseline_root_value) / design_id
        baseline_summary_path = baseline_root / "design_flow_design_summary.json"
        baseline_selection_path = baseline_root / "candidate_selection.json"
        if baseline_summary_path.is_file():
            baseline_summary = json.loads(baseline_summary_path.read_text(encoding="utf-8"))
            baseline_selection = (
                json.loads(baseline_selection_path.read_text(encoding="utf-8"))
                if baseline_selection_path.is_file() else []
            )
            baseline_local = baseline_summary.get("local_assertions", {})
            baseline_rtl = baseline_local.get("rtl_candidate_gate", {})
            baseline_spec = baseline_local.get("spec_candidate_gate", {})
            baseline_cov = (
                baseline_summary.get("ablations", {}).get("with_feedback", {})
                .get("coverage", {}).get("all", {})
            )
            after_cov = coverage_by_type(final_items)["all"]
            before = {
                "applicable_obligations": len(baseline_selection),
                "grounded_obligations": len(baseline_selection),
                "generated_local_assertions": int(baseline_rtl.get("generated", 0))
                + int(baseline_spec.get("generated", 0)),
                "trusted_local_obligations": int(baseline_local.get("trusted_total", 0)),
                "effective_proof_core_percent": float(baseline_cov.get("effective_percent", 0.0)),
                "effective_proof_core_checked": int(baseline_cov.get("checked", 0)),
                "effective_proof_core_denominator": int(
                    baseline_cov.get("effective_reachable_denominator", 0)
                ),
            }
            after = {
                "applicable_obligations": obligation_funnel["summary"]["applicable_obligations"],
                "grounded_obligations": obligation_funnel["summary"]["grounded_obligations"],
                "generated_local_assertions": len(rtl_candidates) + len(spec_candidates),
                "trusted_local_obligations": len(combined_trusted),
                "effective_proof_core_percent": float(after_cov["effective_percent"]),
                "effective_proof_core_checked": int(after_cov["checked"]),
                "effective_proof_core_denominator": int(
                    after_cov["effective_reachable_denominator"]
                ),
            }
            baseline_comparison = {
                "baseline": str(baseline_summary_path),
                "before": before,
                "after": after,
                "delta": {
                    key: round(after[key] - before[key], 4)
                    for key in before
                },
            }
    summary = {
        "schema": "region_flow.10-design-real.v1",
        "design_id": design_id,
        "role": target["role"],
        "validation_scope": target["validation_scope"],
        "top": top,
        "reachable_modules": sorted(reachable_modules),
        "scope_modules": sorted(scope_modules),
        "rtl_files": files,
        "target_configuration_sha256": hashlib.sha256(
            json.dumps(target, sort_keys=True, ensure_ascii=False).encode("utf-8")
        ).hexdigest(),
        "source_digest": design.source_digest,
        "parser": {
            "modules": len(design.modules), "diagnostics": len(design.diagnostics),
            "graph_nodes": graph.get("node_count", len(graph.get("nodes", []))),
            "graph_edges": graph.get("edge_count", len(graph.get("edges", []))),
        },
        "spec": {
            **spec_record,
            "target_module": spec_module,
            "extracted_behaviors": len(mapped_spec),
            "mapped_behaviors": sum(
                item.get("rtl_mapping", {}).get("status") in {
                    "MAPPED", "EVIDENCE_IDENTIFIER_MAPPED", "EVIDENCE_REGION_HINT_MAPPED",
                }
                for item in mapped_spec
            ),
            "directly_compilable_behaviors": sum(
                item.get("rtl_mapping", {}).get("status") == "MAPPED"
                for item in mapped_spec
            ),
            "supporting_evidence_behaviors": sum(
                item.get("rtl_mapping", {}).get("status") in {
                    "EVIDENCE_IDENTIFIER_MAPPED", "EVIDENCE_REGION_HINT_MAPPED",
                }
                for item in mapped_spec
            ),
            "compiled_properties": len(spec_candidates),
            "trusted_properties": len(trusted_spec),
        },
        "regions": updated_region_metrics,
        "local_assertions": {
            "rtl_candidate_gate": _candidate_gate(rtl_candidates, rtl_probe),
            "spec_candidate_gate": _candidate_gate(spec_candidates, spec_probe),
            "trusted_rtl": len(trusted_rtl),
            "trusted_spec": len(trusted_spec),
            "trusted_total": len(combined_trusted),
        },
        "obligation_expansion": {
            "recall_mode": bool(req.get("local_recall_mode", False)),
            "selection_policy": (
                "balanced_structural_diversity"
                if req.get("balanced_local_selection", False)
                else str(req.get("local_candidate_selection_policy", ""))
            ),
            "semantic_deduplication_enabled": False,
            "exact_sva_deduplication_enabled": initial_sva_deduplication_enabled,
            "exact_sva_duplicates_removed": sum(
                item.get("disposition") == "REMOVED_EXACT_DUPLICATE_SVA"
                for item in rtl_duplicate_audit + spec_duplicate_audit
            ),
            "spec_one_to_many_expansions": len(spec_expansion_audit),
            "obligation_funnel": obligation_funnel["summary"],
            "obligation_funnel_by_region_type": obligation_funnel["by_region_type"],
            "obligation_funnel_by_functional_area": obligation_funnel["by_functional_area"],
            "before_after": baseline_comparison,
        },
        "composition": {
            "contract_graph": contract_graph["summary"],
            "local_contracts": local_contracts["summary"],
            "candidate_relations": candidate_doc["summary"],
            "portfolio": composition_portfolio,
            "generated_assertions": len(composition_candidates),
            "trusted_assertions": len(trusted_composition),
            "candidate_gate": _candidate_gate(composition_candidates, composition_probe),
            "new_proof_core_items": len(_checked(no_feedback_items) - _checked(local_items)),
            "llm_validation_error": composition_error,
        },
        "feedback": {
            "initial_gaps": initial_gap,
            "final_gaps": final_gap,
            "generated_assertions": len(feedback_candidates) + len(feedback_composition_candidates),
            "trusted_assertions": len(trusted_feedback),
            "new_regions": len(refinement_regions) + int(bool(extension_region and trusted_feedback)),
            "new_contracts": int(bool(trusted_local_feedback)),
            "new_composites": len(trusted_feedback_composition),
            "composition_candidate_reason": feedback_composition_reason,
            "binding_rejections": len(feedback_binding_rejections),
            "gain": feedback_gain,
            "remaining_reasons": _terminal_reasons(final_mapping),
        },
        "region_refinement": {
            "enabled": bool(req.get("region_refinement_enabled", False)),
            "extension_regions": len(refinement_regions),
            "refined_parent_regions": sorted({rid for r in refinement_regions for rid in r["parent_region_ids"]}),
            "generated_candidate_gate": _candidate_gate(feedback_candidates, feedback_probe),
            "generated_extension_properties": sum(p.property_id in refinement_metadata for p in feedback_candidates),
            "trusted_extension_properties": sum(p.property_id in refinement_metadata for p in trusted_feedback),
            "extension_regions_with_generated": sorted({p.region_id for p in feedback_candidates if p.property_id in refinement_metadata}),
            "extension_regions_with_trusted": sorted({p.region_id for p in trusted_feedback if p.property_id in refinement_metadata}),
            "llm": refinement_llm,
        },
        "ablations": {
            "rtl_only": _formal_metrics(rtl_trusted, rtl_final, rtl_items),
            "spec_plus_rtl": _formal_metrics(combined_trusted, local_final, local_items),
            "without_feedback": _formal_metrics(no_feedback_trusted, no_feedback_final, no_feedback_items),
            "with_feedback": _formal_metrics(final_properties, final_result, final_items),
        },
        "trust_gate": {
            "definition": "PASS + NON_VACUOUS + no unproven assumption",
            "final_all_pass_non_vacuous": True,
            "unproven_assumptions": [],
            "final_sva_contains_assume_property": False,
        },
        "assertion_traceability": traceability["summary"],
        "llm": {
            "provider": llm_provider, "requested_model": local_config["llm"]["model"],
            "spec_extraction": spec_llm,
            "ambiguous_region_interpretation": discovery_llm,
            "composition": composition_llm,
            "extension_region": extension_llm,
            "generated_sva": False,
            "decides_formal_or_trust_status": False,
            "real_response_artifacts": (
                int(bool(spec_llm.get("response_models")))
                + int(bool(discovery_llm.get("response_models")))
                + int(composition_llm.get("real_response_artifacts", 0) > 0)
                + int(extension_llm.get("real_response_artifacts", 0) > 0)
                + int(refinement_llm.get("real_response_artifacts", 0))
            ),
        },
        "stabilization": {
            "rtl_only": rtl_stable, "local_spec_plus_rtl": local_stable,
            "without_feedback": no_feedback_stable, "with_feedback": feedback_stable,
        },
        "formal_cost": {
            "tool": "JasperGold 2021.12p002",
            "real_runs": (
                1 + len(rtl_stable) + int(bool(spec_probe)) + len(local_stable)
                + int(bool(composition_probe)) + len(no_feedback_stable)
                + int(bool(feedback_probe))
                + int(bool(feedback_composition_probe))
                + (len(feedback_stable) if feedback_candidates else 0)
            ),
            "real_result_artifacts": (
                4 + int(bool(spec_probe)) + int(bool(composition_probe))
                + int(bool(feedback_probe)) + int(bool(feedback_composition_probe))
                + int(bool(feedback_candidates))
            ),
        },
        "stimuli_coverage": stimuli,
        "runtime_seconds": round(time.monotonic() - started, 3),
        "artifacts": {
            "graph": str(root / "typed_semantic_graph.json"),
            "regions": str(root / "regions.json"),
            "spec_behaviors": str(root / "spec_behaviors.json"),
            "local_contracts": str(root / "local_contracts.json"),
            "contract_graph": str(root / "contract_graph.json"),
            "final_sva": str(final_formal_root / "assertions.sv"),
            "final_formal": str(final_formal_root / "formal" / "formal_results.json"),
            "initial_gap_mapping": str(root / "feedback" / "initial_gap_mapping.json"),
            "final_gap_mapping": str(root / "feedback" / "final_gap_mapping.json"),
            "assertion_spec_traceability": str(root / "assertion_spec_traceability.json"),
            "obligation_funnel": str(root / "obligation_funnel.json"),
            "exact_sva_duplicate_audit": str(root / "exact_sva_duplicate_audit.json"),
            "stimuli_coverage": str(root / "formal" / "stimuli_coverage" / "coverage_statuses.tsv"),
        },
    }
    dump_json(root / "design_flow_design_summary.json", summary)
    return summary


def _write_report(path: Path, summary: dict[str, Any]) -> None:
    full_design = all(
        row.get("validation_scope") == "full_cpu" for row in summary["designs"]
    )
    lines = [
        "# Requirement 8.10 跨设计真实验证报告", "",
        "## 结论", "",
        (
            f"同一套无设计名分支的框架完成 {len(summary['designs'])} 个目标的验证；"
            f"最终可信 survivor 全部满足 PASS + NON_VACUOUS，且最终 SVA 不含 assume property。"
        ), "",
    ]
    if not full_design:
        lines += [
            "> **范围警告：本次配置是 arithmetic_execution_unit 子模块诊断，不是三个 CPU 的整机 Req8.10 实验。**",
            "> `Final survivor` 的分母是候选门禁后保留下来的可信集合，不能解释成全部生成断言的 Proven 率，也不能与整机 Req8.8/Req8.9 直接比较。",
            "",
        ]
    lines += [
        "| Design | Scope / top | Local candidates (trusted/generated) | Composite candidates (trusted/generated) | Feedback (trusted/generated) | Final trusted survivor | Effective Proof-Core |",
        "|---|---|---:|---:|---:|---:|---:|",
    ]
    for row in summary["designs"]:
        final = row["ablations"]["with_feedback"]
        coverage = final["coverage"]["all"]
        local_generated = (
            row["local_assertions"]["rtl_candidate_gate"]["generated"]
            + row["local_assertions"]["spec_candidate_gate"]["generated"]
        )
        lines.append(
            f"| {row['design_id']} | {row['validation_scope']} / `{row['top']}` | "
            f"{row['local_assertions']['trusted_total']}/{local_generated} | "
            f"{row['composition']['trusted_assertions']}/{row['composition']['generated_assertions']} | "
            f"{row['feedback']['trusted_assertions']}/{row['feedback']['generated_assertions']} | "
            f"{final['trusted']} | {coverage['checked']}/{coverage['effective_reachable_denominator']} "
            f"({coverage['effective_percent']:.2f}%) |"
        )
    lines += ["", "## 消融", ""]
    for row in summary["designs"]:
        lines += [f"### {row['design_id']}", ""]
        for name in ("rtl_only", "spec_plus_rtl", "without_feedback", "with_feedback"):
            experiment = row["ablations"][name]
            coverage = experiment["coverage"]["all"]
            lines.append(
                f"- `{name}`：可信 {experiment['trusted']}/{experiment['generated']}，"
                f"Effective Proof-Core {coverage['checked']}/"
                f"{coverage['effective_reachable_denominator']} "
                f"({coverage['effective_percent']:.2f}%)。"
            )
        gain = row["feedback"]["gain"]
        lines.append(
            f"- Feedback 精确差分：新增 {gain['new_checked_items']}、丢失 {gain['lost_checked_items']}、"
            f"净变化 {gain['net_checked_items']} 个 checked item。"
        )
        lines.append("")
    lines += [
        "## 可信边界", "",
        "LLM 只做 SPEC 行为提取、SPEC 事件关系绑定和候选 Extension Region 语义解释；",
        "所有 SVA 均由固定 primitive/compiler 生成，PASS、NON_VACUOUS 与是否进入可信集均由 JasperGold 决定。",
        "", "## 泛化边界", "",
        "设计差异只存在于 YAML 的 RTL/top/clock/reset/SPEC 字段。算法源文件的设计名扫描结果见 summary；",
        "配置中标记为 DEVELOPMENT_BASELINE 的目标用于开发调优；标记为 "
        "ZERO_ADAPTATION_VALIDATION 的目标均未增加目标专用规则。",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def run(args: argparse.Namespace) -> dict[str, Any]:
    started = time.monotonic()
    config_path = _resolve(args.config)
    config = yaml.safe_load(config_path.read_text(encoding="utf-8"))
    req = config.get("design_flow", {})
    output = _resolve(args.output)
    output.mkdir(parents=True, exist_ok=True)
    configured_designs = list(req.get("designs", []))
    requested_ids = set(getattr(args, "design_id", None) or [])
    active_designs = [
        item for item in configured_designs
        if not requested_ids or str(item.get("design_id")) in requested_ids
    ]
    missing_ids = requested_ids - {str(item.get("design_id")) for item in active_designs}
    if missing_ids:
        raise RuntimeError(f"unknown requested design_id(s): {sorted(missing_ids)}")
    partial_run = len(active_designs) < len(configured_designs)
    if partial_run and not getattr(args, "allow_partial", False):
        raise RuntimeError("a design subset requires --allow-partial")
    designs = [_run_design(item, config, output) for item in active_designs]
    if len(designs) < 3 and not getattr(args, "allow_partial", False):
        raise RuntimeError("Req8.10 requires at least three configured CPU designs")

    algorithm_paths = [
        PROJECT_ROOT / "rtl_frontend" / "graph_patterns.py",
        PROJECT_ROOT / "rtl_frontend" / "graph_motif_library.py",
        PROJECT_ROOT / "rtl_frontend" / "graph_motif_matching.py",
        PROJECT_ROOT / "pipeline" / "semantic_slicing.py",
        PROJECT_ROOT / "pipeline" / "local_region_assertions.py",
        PROJECT_ROOT / "pipeline" / "local_contract_composition.py",
        PROJECT_ROOT / "pipeline" / "formal_gap_semantics.py",
        Path(__file__).resolve(),
    ]
    configured_names = [str(item["design_id"]).lower() for item in active_designs]
    hits = []
    for path in algorithm_paths:
        source = path.read_text(encoding="utf-8", errors="replace").lower()
        for name in configured_names:
            if name in source:
                hits.append({"file": str(path), "design_id": name})
    hardcode_audit = {
        "algorithm_files": [
            {"path": str(item), "sha256": _sha256(item)} for item in algorithm_paths
        ],
        "configured_design_names": configured_names,
        "design_name_hits": hits,
        "passed": not hits,
        "configuration_is_only_design_specific_input": True,
    }
    if not hardcode_audit["passed"]:
        raise RuntimeError(f"design-specific algorithm hardcode detected: {hits}")

    frozen_path = _resolve(req["gap_interpretation_freeze_audit"])
    frozen = json.loads(frozen_path.read_text(encoding="utf-8")) if frozen_path.is_file() else {}
    all_trusted = all(row["trust_gate"]["final_all_pass_non_vacuous"] for row in designs)
    own_specs = len({row["spec"]["source_url"] for row in designs}) == len(designs)
    completion = {
        "gap_interpretation_refinement_frozen": bool(frozen.get("frozen")),
        "full_cpu_scope_for_all_designs": all(
            row.get("validation_scope") == "full_cpu" for row in designs
        ),
        "framework_runs_on_multiple_cpu_designs": len(designs) >= 3,
        "each_design_uses_own_spec_source": own_specs,
        "no_design_specific_hardcode": hardcode_audit["passed"],
        "core_region_ontology_reusable": all(
            row["regions"]["core_regions"] > 0 for row in designs
        ),
        "extension_region_handles_cpu_specific_logic": any(row["regions"]["extension_regions"] > 0 for row in designs),
        "local_contract_generation_works": all(row["composition"]["local_contracts"]["contracts"] > 0 for row in designs),
        "composite_contract_generation_works": all(row["composition"]["generated_assertions"] > 0 for row in designs),
        "formal_gap_refinement_works": (
            all(
                row["feedback"]["gain"]["denominator_constant"]
                and "gaps" in row["feedback"]["initial_gaps"]
                and "gaps" in row["feedback"]["final_gaps"]
                for row in designs
            )
            and any(row["feedback"]["generated_assertions"] > 0 for row in designs)
        ),
        "coverage_improvement_measurable": all(row["feedback"]["gain"]["denominator_constant"] for row in designs),
        "trust_gate_remains_strict": all_trusted,
        "real_llm_evidence": all(row["llm"]["real_response_artifacts"] > 0 for row in designs),
        "real_jaspergold_evidence": all(row["formal_cost"]["real_runs"] > 0 for row in designs),
    }
    completion["all_satisfied"] = all(completion.values())
    summary = {
        "schema": "region_flow.10-cross-design-real.v1",
        "config": str(config_path),
        "config_sha256": _sha256(config_path),
        "partial_run": partial_run,
        "requested_design_ids": sorted(requested_ids),
        "gap_interpretation_freeze_audit": frozen,
        "designs": designs,
        "hardcode_audit": hardcode_audit,
        "completion_criteria": completion,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "artifacts": {
            "summary": str(output / "design_flow_summary.json"),
            "report": str(_resolve(args.report)),
        },
    }
    dump_json(output / "design_flow_summary.json", summary)
    _write_report(_resolve(args.report), summary)
    return summary


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True)
    parser.add_argument("--output", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument(
        "--design-id", action="append",
        help="Run only the named configured design; repeat for a subset.",
    )
    parser.add_argument(
        "--allow-partial", action="store_true",
        help="Permit a diagnostic subset run; global three-design completion remains false.",
    )
    return parser


def main() -> int:
    args = build_parser().parse_args()
    summary = run(args)
    print(json.dumps(summary, ensure_ascii=False, indent=2))
    return 0 if summary["completion_criteria"]["all_satisfied"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
