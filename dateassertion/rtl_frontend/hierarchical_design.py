"""Elaborated hierarchy and cross-module semantic edges for Requirement 8.

This module is intentionally layered on top of the frozen Requirement-7
``RTLDesign`` and semantic graph.  It does not change their inference rules;
it adds instance paths and port connections that only exist after
elaboration.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from pathlib import Path
import re
from typing import Any

import pyslang

from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


_DIRECTION = {
    "ArgumentDirection.In": "input",
    "ArgumentDirection.Out": "output",
    "ArgumentDirection.InOut": "inout",
    "ArgumentDirection.Ref": "ref",
}


def _source(manager: Any, location: Any) -> dict[str, Any]:
    if location is None or location == pyslang.SourceLocation.NoLocation:
        return {"file": "", "line": 0}
    return {
        "file": str(Path(manager.getFileName(location)).resolve()),
        "line": int(manager.getLineNumber(location)),
    }


def _syntax_expression(instance: Any, port_name: str) -> str:
    syntax = getattr(instance, "syntax", None)
    if syntax is None:
        return ""
    for connection in getattr(syntax, "connections", []):
        if not str(getattr(connection, "kind", "")).endswith("NamedPortConnection"):
            continue
        if connection.name.valueText == port_name:
            return " ".join(str(connection.expr).split())
    return ""


def _instance_parent(path: str) -> str:
    return path.rsplit(".", 1)[0] if "." in path else ""


def _module_source(design: RTLDesign, module: str) -> dict[str, Any]:
    candidates = [item for item in design.modules if item.name == module]
    if not candidates:
        return {"file": "", "line_start": 0, "line_end": 0}
    item = candidates[0]
    return {"file": item.file, "line_start": item.line_start, "line_end": item.line_end}


def _major_flow(cross_edges: list[dict[str, Any]]) -> list[dict[str, Any]]:
    counts: dict[tuple[str, str, str], int] = Counter()
    signals: dict[tuple[str, str, str], set[str]] = defaultdict(set)
    for edge in cross_edges:
        key = (edge["source"]["module"], edge["target"]["module"], edge["semantic_kind"])
        counts[key] += 1
        signals[key].update((edge["source"]["signal"], edge["target"]["signal"]))
    return [
        {
            "source_module": source,
            "target_module": target,
            "semantic_kind": kind,
            "edge_count": count,
            "signals": sorted(signals[(source, target, kind)])[:24],
        }
        for (source, target, kind), count in sorted(
            counts.items(), key=lambda item: (-item[1], item[0])
        )
    ]


def build_hierarchical_design_map(
    design: RTLDesign,
    semantic_graph: dict[str, Any],
    top_module: str,
    *,
    include_dirs: list[str] | None = None,
) -> dict[str, Any]:
    """Elaborate ``top_module`` and map every concrete instance connection.

    Pyslang expands generate loops and parameterized instances.  The returned
    cross-module edges are instance-specific, while the frozen Req7 graph
    remains module-local.
    """

    include_dirs = [str(Path(item).resolve()) for item in (include_dirs or [])]
    source_files = [
        Path(item).resolve() for item in design.files
        if any(module.file == item for module in design.modules)
    ]
    source_files = list(dict.fromkeys(source_files))

    pp_options = pyslang.parsing.PreprocessorOptions()
    pp_options.additionalIncludePaths = include_dirs
    compilation_options = pyslang.ast.CompilationOptions()
    compilation_options.topModules = {top_module}
    options = pyslang.Bag()
    options.preprocessorOptions = pp_options
    options.compilationOptions = compilation_options
    source_manager = pyslang.SourceManager()
    compilation = pyslang.ast.Compilation(options)
    for path in source_files:
        tree = pyslang.syntax.SyntaxTree.fromFile(str(path), source_manager, options)
        compilation.addSyntaxTree(tree)

    root = compilation.getRoot()
    tops = [item for item in root.topInstances if item.name == top_module]
    if len(tops) != 1:
        raise ValueError(f"elaboration expected one top {top_module!r}, found {len(tops)}")

    instances: list[Any] = []
    tops[0].visit(
        lambda symbol: instances.append(symbol)
        if isinstance(symbol, pyslang.ast.InstanceSymbol) else None
    )
    instance_records: list[dict[str, Any]] = []
    hierarchy_edges: list[dict[str, Any]] = []
    cross_edges: list[dict[str, Any]] = []
    ports_by_instance: dict[str, list[dict[str, Any]]] = defaultdict(list)

    for instance in instances:
        path = str(instance.hierarchicalPath)
        module = str(instance.definition.name)
        parent_path = _instance_parent(path)
        parent_module = ""
        if parent_path:
            parent = next((item for item in instances if str(item.hierarchicalPath) == parent_path), None)
            parent_module = str(parent.definition.name) if parent is not None else ""
        record = {
            "path": path,
            "instance": instance.name,
            "module": module,
            "parent_path": parent_path or None,
            "parent_module": parent_module or None,
            "source": _module_source(design, module),
            "port_count": len(instance.portConnections),
        }
        instance_records.append(record)
        if parent_path:
            hierarchy_edges.append({
                "type": "INSTANCE",
                "source": parent_path,
                "target": path,
                "parent_module": parent_module,
                "child_module": module,
            })
        for connection in instance.portConnections:
            port = connection.port
            port_name = str(port.name)
            direction = _DIRECTION.get(str(port.direction), str(port.direction))
            expression = _syntax_expression(instance, port_name)
            parent_signals = sorted(expression_signals(expression))
            port_record = {
                "port": port_name,
                "direction": direction,
                "parent_expression": expression,
                "parent_signals": parent_signals,
            }
            ports_by_instance[path].append(port_record)
            if not parent_path or not parent_module:
                continue
            semantic_kind = (
                "CONTROL" if re.search(
                    r"(?:valid|ready|req|ack|enable|_en$|sel|state|flush|stall|irq|reset|rst)",
                    port_name, re.I,
                ) else "DATA"
            )
            for parent_signal in parent_signals:
                parent_endpoint = {
                    "instance_path": parent_path,
                    "module": parent_module,
                    "signal": parent_signal,
                }
                child_endpoint = {
                    "instance_path": path,
                    "module": module,
                    "signal": port_name,
                }
                directions = []
                if direction in {"input", "inout", "ref"}:
                    directions.append((parent_endpoint, child_endpoint))
                if direction in {"output", "inout", "ref"}:
                    directions.append((child_endpoint, parent_endpoint))
                for source, target in directions:
                    cross_edges.append({
                        "id": f"cross:{len(cross_edges) + 1}",
                        "type": "CROSS_MODULE",
                        "semantic_kind": semantic_kind,
                        "source": source,
                        "target": target,
                        "port": port_name,
                        "direction": direction,
                        "parent_expression": expression,
                        "evidence": _source(source_manager, instance.location),
                    })

    for record in instance_records:
        record["ports"] = ports_by_instance.get(record["path"], [])

    reachable_modules = sorted({item["module"] for item in instance_records})
    module_records = []
    for module in reachable_modules:
        signals = design.module_signals.get(module, {})
        assignments = [item for item in design.assignments if item.module == module]
        always_blocks = [item for item in design.always_blocks if item.module == module]
        cases = [item for item in design.cases if item.module == module]
        state = sorted({
            item.lhs for item in assignments if item.kind == "nonblocking"
        } | {
            name for name in signals
            if re.search(r"(?:state|_r$|_q$|_reg$|^reg_)", name, re.I)
        })
        module_records.append({
            "module": module,
            "source": _module_source(design, module),
            "instance_count": sum(item["module"] == module for item in instance_records),
            "signal_count": len(signals),
            "assignment_count": len(assignments),
            "always_block_count": len(always_blocks),
            "fsm_count": len(cases),
            "owned_state_registers": state,
            "ports": {
                direction: sorted(name for name, signal in signals.items() if signal.direction == direction)
                for direction in ("input", "output", "inout")
            },
        })

    diagnostics = []
    for diagnostic in compilation.getAllDiagnostics():
        diagnostics.append({
            "code": str(diagnostic.code),
            "is_error": bool(diagnostic.isError()),
            "args": [str(item) for item in diagnostic.args],
            **_source(source_manager, diagnostic.location),
        })

    local_edges = list(semantic_graph.get("edges", []))
    return {
        "schema": "region_flow-design-map.v1",
        "top_module": top_module,
        "source_digest": design.source_digest,
        "elaboration": {
            "engine": f"pyslang-{pyslang.__version__}",
            "source_files": len(source_files),
            "include_dirs": include_dirs,
            "top_instances": [item.name for item in root.topInstances],
            "concrete_instance_count": len(instance_records),
            "diagnostic_count": len(diagnostics),
            "error_count": sum(item["is_error"] for item in diagnostics),
            "diagnostics": diagnostics,
        },
        "modules": module_records,
        "instances": instance_records,
        "hierarchy_edges": hierarchy_edges,
        "local_semantic_edge_count": len(local_edges),
        "cross_module_dependencies": cross_edges,
        "cross_module_edge_count": len(cross_edges),
        "major_control_dataflow": _major_flow(cross_edges),
        "ownership": {
            "state_registers": [
                {"module": item["module"], "signal": signal}
                for item in module_records for signal in item["owned_state_registers"]
            ],
            "always_blocks": [
                {
                    "module": block.module,
                    "file": block.file,
                    "line_start": block.line_start,
                    "line_end": block.line_end,
                    "assigned_signals": block.assigned_signals,
                }
                for block in design.always_blocks if block.module in reachable_modules
            ],
            "fsms": [
                {
                    "module": case.module,
                    "selector": case.selector,
                    "labels": case.labels,
                    "file": case.file,
                    "line_start": case.line_start,
                    "line_end": case.line_end,
                }
                for case in design.cases if case.module in reachable_modules
            ],
        },
        "summary": {
            "reachable_modules": len(reachable_modules),
            "concrete_instances": len(instance_records),
            "hierarchy_edges": len(hierarchy_edges),
            "cross_module_dependencies": len(cross_edges),
            "cross_control_dependencies": sum(item["semantic_kind"] == "CONTROL" for item in cross_edges),
            "cross_data_dependencies": sum(item["semantic_kind"] == "DATA" for item in cross_edges),
        },
    }
