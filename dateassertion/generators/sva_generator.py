"""Deterministic SVA rendering from validated PropertyIR records."""

from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re
from typing import Any

import pyslang

from dateassertion.ir.schema import PropertyIR, SignalInfo


def _symbolic_width(signal: SignalInfo) -> bool:
    return bool(signal.width and re.search(r"[A-Za-z_][A-Za-z0-9_$]*", signal.width))


def _width_parameter(signal: SignalInfo) -> str:
    return "WIDTH_" + re.sub(r"[^A-Za-z0-9_$]", "_", signal.name).upper()


def _port(signal: SignalInfo) -> str:
    if _symbolic_width(signal):
        width = f" [{_width_parameter(signal)}-1:0]"
    else:
        width = f" {signal.width}" if signal.width else ""
    dimensions = ""
    if signal.kind.endswith("_array"):
        if len(signal.unpacked_dimensions) != 1:
            raise ValueError(f"array {signal.name} requires one known unpacked dimension")
        stem = _width_parameter(signal)
        dimensions = f" [{stem}_LEFT:{stem}_RIGHT]"
    return f"    input logic{width} {signal.name}{dimensions}"


def generate_sva(
    properties: list[PropertyIR],
    signals: dict[str, SignalInfo],
    top_module: str,
    output_path: str | Path,
    clock: str = "clk",
    reset: str = "resetn",
    observation_helpers: list[dict[str, Any]] | None = None,
    module_signals: dict[str, dict[str, SignalInfo]] | None = None,
    assume_property_ids: set[str] | None = None,
) -> str:
    helpers = observation_helpers or []
    helper_by_id = {item["helper_id"]: item for item in helpers}
    properties_by_module: dict[str, list[PropertyIR]] = defaultdict(list)
    for prop in properties:
        properties_by_module[prop.target_module or top_module].append(prop)
    lines = [
        "// Generated deterministically from properties.json; do not edit by hand.",
    ]
    for module, module_properties in sorted(properties_by_module.items()):
        module_helpers = {
            helper_id: helper for helper_id, helper in helper_by_id.items()
            if helper.get("module") == module
            and any(helper_id in prop.observation_helper_ids or helper_id in prop.signals for prop in module_properties)
        }
        referenced = {clock, reset}
        helper_names = set(module_helpers)
        for prop in module_properties:
            referenced.update(set(prop.signals) - helper_names)
        for helper in module_helpers.values():
            referenced.update(helper.get("signals", []))
        scoped_signals = (module_signals or {}).get(module, {})
        top_signals = (module_signals or {}).get(top_module, {})
        if module_signals:
            missing = sorted(
                name for name in referenced
                if name not in scoped_signals
                and not (name in {clock, reset} and name in top_signals)
            )
        else:
            missing = sorted(name for name in referenced if name not in signals)
        if missing:
            raise ValueError(f"cannot render checker for {module}; signal metadata missing for: {missing}")
        metadata = {
            name: scoped_signals.get(name, top_signals.get(name, signals.get(name)))
            for name in referenced
        }
        checker_name = re.sub(r"[^A-Za-z0-9_$]", "_", module) + "_microarch_checker"
        referenced_names = sorted(referenced)
        constant_names = [
            name for name in referenced_names if metadata[name].direction == "constant"
        ]
        port_names = [name for name in referenced_names if name not in constant_names]
        symbolic = [metadata[name] for name in port_names if _symbolic_width(metadata[name])]
        arrays = [metadata[name] for name in port_names if metadata[name].kind.endswith("_array")]
        ports = ",\n".join(_port(metadata[name]) for name in port_names)
        parameter_lines = [
            f"    parameter integer {_width_parameter(signal)} = 1" for signal in symbolic
        ] + [
            f"    parameter {name} = 0" for name in constant_names
        ] + [
            f"    parameter integer {_width_parameter(signal)}_{bound} = 0"
            for signal in arrays for bound in ("LEFT", "RIGHT")
        ]
        if parameter_lines:
            parameters = ",\n".join(parameter_lines)
            lines.extend([f"module {checker_name} #(", parameters, ") ("])
        else:
            lines.append(f"module {checker_name} (")
        lines.extend([ports, ");", ""])
        for helper in sorted(module_helpers.values(), key=lambda item: item["helper_id"]):
            evidence = helper.get("evidence", [{}])[0]
            lines.append(
                f"    // verification-only observation; evidence={evidence.get('file', '')}:{evidence.get('line', '')}"
            )
            lines.append(f"    wire {helper['helper_id']} = {helper['expression']};")
        if module_helpers:
            lines.append("")
        assumption_ids = assume_property_ids or set()
        for prop in module_properties:
            disable = f" disable iff ({prop.disable_iff})" if prop.disable_iff else ""
            label = "p_" + re.sub(r"[^A-Za-z0-9_$]", "_", prop.property_id)
            directive = "assume" if prop.property_id in assumption_ids else "assert"
            prop.sva = f"{label}: {directive} property (@(posedge {clock}){disable} ({prop.body}));"
            lines.extend(
                [
                    f"    // {prop.family} | region={prop.region_id} | source={prop.source} | confidence={prop.llm_confidence:.3f} | directive={directive}",
                    f"    {prop.sva}",
                    "",
                ]
            )
        connections = ", ".join(
            f".{name}({name if name in scoped_signals else f'$root.{top_module}.{name}'})"
            for name in port_names
        )
        if parameter_lines:
            overrides = [
                f".{_width_parameter(signal)}($bits({signal.name}[$left({signal.name})]))"
                if signal.kind.endswith("_array") else f".{_width_parameter(signal)}($bits({signal.name}))"
                for signal in symbolic
            ] + [f".{name}({name})" for name in constant_names] + [
                f".{_width_parameter(signal)}_{bound}(${bound.lower()}({signal.name}))"
                for signal in arrays for bound in ("LEFT", "RIGHT")]
            bind = f"bind {module} {checker_name} #({', '.join(overrides)}) u_microarch_checker ({connections});"
        else:
            bind = f"bind {module} {checker_name} u_microarch_checker ({connections});"
        lines.extend(["endmodule", "", bind, ""])
    rendered = "\n".join(lines)
    syntax = pyslang.syntax.SyntaxTree.fromText(rendered)
    if syntax.diagnostics:
        codes = ", ".join(str(diagnostic.code) for diagnostic in syntax.diagnostics)
        raise ValueError(f"generated SVA failed pyslang syntax validation: {codes}")
    path = Path(output_path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(rendered, encoding="utf-8")
    return rendered
