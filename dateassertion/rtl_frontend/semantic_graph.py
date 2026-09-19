"""Deterministic RTL semantic/dependence graph for Requirement 7.

The graph deliberately stays smaller than an EDA elaborator.  It records only
facts that can be read directly from the parsed RTL: declarations,
assignments, complete syntactic path guards, data/control/sequential edges,
clock/reset context, widths, and conservative semantic roles.
"""

from __future__ import annotations

from collections import defaultdict
import re
from typing import Any, Iterable

from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.parser import RTLDesign


ROLE_NAMES = {"predicate", "event", "control", "state", "data", "address", "counter", "payload"}
TIMING_NAMES = {"same_cycle", "next_cycle", "variable_latency", "unknown"}


def _macro_value(value: str, macros: dict[str, str]) -> str:
    result = value.strip()
    for _ in range(8):
        match = re.fullmatch(r"`?([A-Za-z_][A-Za-z0-9_$]*)", result)
        if not match or match.group(1) not in macros:
            break
        result = macros[match.group(1)].strip()
    return result


def width_bits(width: str, macros: dict[str, str] | None = None) -> int | None:
    """Convert common packed ranges and range macros to a bit count."""
    if not width:
        return 1
    macros = macros or {}
    text = width.strip()
    macro = re.fullmatch(r"\[\s*`([A-Za-z_][A-Za-z0-9_$]*)\s*\]", text)
    if macro and macro.group(1) in macros:
        text = "[" + _macro_value(macros[macro.group(1)], macros).strip("[]") + "]"
    range_match = re.fullmatch(r"\[\s*([^:]+)\s*:\s*([^\]]+)\s*\]", text)
    if not range_match:
        return None
    try:
        high = int(_macro_value(range_match.group(1), macros), 0)
        low = int(_macro_value(range_match.group(2), macros), 0)
    except ValueError:
        return None
    return abs(high - low) + 1


def _source(file: str, line: int, detail: str = "") -> dict[str, Any]:
    result: dict[str, Any] = {"file": file, "line": line}
    if detail:
        result["detail"] = detail
    return result


def _assignment_timing(kind: str) -> str:
    if kind == "nonblocking":
        return "next_cycle"
    if kind in {"blocking", "continuous"}:
        return "same_cycle"
    return "unknown"


def _enclosing_always(design: RTLDesign, module: str, file: str, line: int) -> Any | None:
    matches = [
        block for block in design.always_blocks
        if block.module == module and block.file == file and block.line_start <= line <= block.line_end
    ]
    return min(matches, key=lambda item: item.line_end - item.line_start) if matches else None


def _clock_reset(design: RTLDesign, assignment: Any) -> tuple[str | None, list[str]]:
    block = _enclosing_always(design, assignment.module, assignment.file, assignment.line)
    if block is None:
        return None, []
    events = re.findall(r"(?:posedge|negedge)\s+([A-Za-z_][A-Za-z0-9_$]*)", block.event_control)
    clock = events[0] if events else None
    reset_candidates = [
        name for name in expression_signals(assignment.guard)
        if re.search(r"(?:^|_)(?:rst|reset)(?:n|_n)?(?:$|_)", name, re.I)
    ]
    if len(events) > 1:
        reset_candidates.extend(events[1:])
    return clock, list(dict.fromkeys(reset_candidates))


def _uses(design: RTLDesign) -> dict[tuple[str, str], list[dict[str, Any]]]:
    result: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for assignment in design.assignments:
        for dependency in assignment.dependencies:
            result[(assignment.module, dependency)].append({
                "lhs": assignment.lhs,
                "kind": assignment.kind,
                "file": assignment.file,
                "line": assignment.line,
            })
        for dependency in expression_signals(assignment.guard):
            result[(assignment.module, dependency)].append({
                "lhs": assignment.lhs,
                "kind": "control",
                "file": assignment.file,
                "line": assignment.line,
            })
    return result


def infer_signal_role(design: RTLDesign, module: str, signal_name: str) -> dict[str, Any]:
    signal = design.module_signals.get(module, {}).get(signal_name)
    if signal is None:
        return {
            "signal": signal_name,
            "module": module,
            "role": "data",
            "role_candidates": [],
            "width": None,
            "basic_type": "unknown",
            "status": "AMBIGUOUS",
            "evidence": ["signal is not declared in the selected module"],
        }
    bits = width_bits(signal.width, design.macros)
    lowered = signal_name.lower()
    assignments = [item for item in design.assignments if item.module == module and item.lhs == signal_name]
    uses = _uses(design).get((module, signal_name), [])
    candidates: list[str] = []
    evidence: list[str] = []

    if bits == 1:
        candidates.append("predicate")
        evidence.append("declared width is one bit")
    if re.search(r"(?:valid|ready|done|start|finish|fire|req|ack|trigger|timeout|flush|stall|trap|irq)(?:$|_)", lowered):
        candidates.append("event")
        evidence.append("event/handshake naming and use pattern")
    if re.search(r"(?:addr|address|_pc$|^pc$|next_pc|reg_pc)", lowered):
        candidates.append("address")
        evidence.append("address/program-counter naming")
    if re.search(r"(?:count|counter|timer|cycle)", lowered):
        candidates.append("counter")
        evidence.append("counter/timer naming")
    if re.search(r"(?:wdata|rdata|payload|data_o$|data_i$|_data$)", lowered):
        candidates.append("payload")
        evidence.append("payload/read-write-data naming")
    if re.search(r"(?:state|_q$|_reg$|^reg_)", lowered) or any(item.kind == "nonblocking" for item in assignments):
        candidates.append("state")
        evidence.append("nonblocking storage assignment or state/register naming")
    if re.search(r"(?:enable|_en$|_we$|_re$|opcode|funct|select|sel|mask|hold)", lowered):
        candidates.append("control")
        evidence.append("decode/enable/control naming")
    if any(item["kind"] == "control" for item in uses):
        candidates.append("control")
        evidence.append("used in an assignment path guard")
    arithmetic = re.compile(r"(?:\+|-|\*|/|<<|>>|\^|\||&)")
    if bits != 1 and any(arithmetic.search(item.rhs) for item in assignments):
        candidates.append("data")
        evidence.append("assigned from an arithmetic/bitwise expression")
    if bits != 1 and not candidates:
        candidates.append("data")
        evidence.append("multi-bit value without a narrower deterministic role")

    candidates = list(dict.fromkeys(item for item in candidates if item in ROLE_NAMES))
    precedence = ["event", "address", "counter", "payload", "state", "control", "predicate", "data"]
    primary = next((item for item in precedence if item in candidates), "data")
    status = "DETERMINISTIC" if candidates else "AMBIGUOUS"
    return {
        "signal": signal_name,
        "module": module,
        "role": primary,
        "role_candidates": candidates,
        "width": bits,
        "declared_range": signal.width,
        "basic_type": "logic" if bits == 1 else "logic_vector" if bits else "unknown",
        "direction": signal.direction,
        "status": status,
        "evidence": evidence,
        "source": _source(signal.file, signal.line, "declaration"),
    }


def expression_width(expression: Any, design: RTLDesign, module: str) -> int | None:
    if not isinstance(expression, str) or not expression.strip():
        return None
    text = expression.strip()
    bare = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_$]*)(?:\[(\d+)(?::(\d+))?\])?", text)
    if bare:
        if bare.group(2):
            return abs(int(bare.group(2)) - int(bare.group(3) or bare.group(2))) + 1
        signal = design.module_signals.get(module, {}).get(bare.group(1))
        return width_bits(signal.width, design.macros) if signal else None
    if re.search(r"(?:==|!=|<=|>=|<|>|&&|\|\||!\s*[A-Za-z_(])", text):
        return 1
    literal_widths = [int(item) for item in re.findall(r"\b(\d+)\s*'[sS]?[bBoOdDhH]", text)]
    if literal_widths:
        return max(literal_widths)
    concat = re.fullmatch(r"\{\s*(\d+)\s*\{.*\}\s*\}", text, re.S)
    if concat:
        return int(concat.group(1))
    widths = [
        width_bits(design.module_signals[module][name].width, design.macros)
        for name in expression_signals(text)
        if name in design.module_signals.get(module, {})
    ]
    known = [item for item in widths if item is not None]
    return max(known) if known else None


def expression_role(expression: Any, design: RTLDesign, module: str) -> dict[str, Any]:
    if not isinstance(expression, str) or not expression.strip():
        return {"role": "unknown", "width": None, "status": "AMBIGUOUS", "evidence": ["empty expression"]}
    text = expression.strip()
    bits = expression_width(text, design, module)
    if bits == 1 or re.search(r"(?:==|!=|<=|>=|&&|\|\||^\s*!|\$rose|\$fell)", text):
        return {"role": "predicate", "width": 1, "status": "DETERMINISTIC", "evidence": ["Boolean/comparison expression"]}
    bare = re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", text)
    if bare:
        return infer_signal_role(design, module, text)
    return {
        "role": "data" if bits and bits > 1 else "unknown",
        "width": bits,
        "status": "DETERMINISTIC" if bits else "AMBIGUOUS",
        "evidence": ["expression width and operators inferred from syntax"],
    }


def assignment_timing(design: RTLDesign, module: str, target: str) -> dict[str, Any]:
    assignments = [item for item in design.assignments if item.module == module and item.lhs == target]
    timings = {_assignment_timing(item.kind) for item in assignments} - {"unknown"}
    if len(timings) == 1:
        timing = next(iter(timings))
        status = "DETERMINISTIC"
    elif len(timings) > 1:
        timing = "variable_latency"
        status = "AMBIGUOUS"
    else:
        timing = "unknown"
        status = "AMBIGUOUS"
    return {
        "target": target,
        "timing": timing,
        "status": status,
        "evidence": [
            {"kind": item.kind, "file": item.file, "line": item.line, "rhs": item.rhs}
            for item in assignments
        ],
    }


def build_semantic_graph(design: RTLDesign) -> dict[str, Any]:
    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    role_evidence: list[dict[str, Any]] = []
    for module, signals in sorted(design.module_signals.items()):
        for name, signal in sorted(signals.items()):
            role = infer_signal_role(design, module, name)
            role_evidence.append(role)
            nodes.append({
                "id": f"signal:{module}.{name}",
                "kind": "signal",
                "module": module,
                "name": name,
                "width": role["width"],
                "basic_type": role["basic_type"],
                "direction": signal.direction,
                "signal_kind": signal.kind,
                "constant_expression": signal.constant_expression,
                "role": role["role"],
                "source": _source(signal.file, signal.line),
            })
    assignment_records: list[dict[str, Any]] = []
    for index, assignment in enumerate(design.assignments, start=1):
        assignment_id = f"assignment:{index}"
        expression_id = f"expression:{index}:rhs"
        guard_id = f"expression:{index}:guard"
        timing = _assignment_timing(assignment.kind)
        clock, resets = _clock_reset(design, assignment)
        block = _enclosing_always(design, assignment.module, assignment.file, assignment.line)
        record = {
            "id": assignment_id,
            "module": assignment.module,
            "lhs": assignment.lhs,
            "rhs": assignment.rhs,
            "lhs_expression": assignment.lhs_expression or assignment.lhs,
            "assignment_kind": assignment.kind,
            "timing": timing,
            "guard": assignment.guard or "1'b1",
            "clock": clock,
            "event_control": block.event_control if block else None,
            "process_id": f"{block.file}:{block.line_start}:{block.line_end}" if block else None,
            "source_order": index,
            "reset": resets,
            "source": _source(assignment.file, assignment.line),
        }
        assignment_records.append(record)
        nodes.extend([
            {"id": assignment_id, "kind": "assignment", **{key: value for key, value in record.items() if key != "id"}},
            {"id": expression_id, "kind": "expression", "module": assignment.module, "text": assignment.rhs, "basic_type": expression_role(assignment.rhs, design, assignment.module)},
        ])
        if assignment.guard:
            nodes.append({"id": guard_id, "kind": "expression", "module": assignment.module, "text": assignment.guard, "basic_type": "predicate"})
        for dependency in assignment.dependencies:
            edges.append({
                "type": "DATA",
                "source": f"signal:{assignment.module}.{dependency}",
                "target": assignment_id,
                "evidence": _source(assignment.file, assignment.line, "RHS dependency"),
            })
        edges.append({"type": "DATA", "source": assignment_id, "target": f"signal:{assignment.module}.{assignment.lhs}", "evidence": _source(assignment.file, assignment.line, "assignment result")})
        # Index selects the destination element; this is selection control,
        # not an RHS value and not a Boolean guard to emit as an antecedent.
        for index_expr in re.findall(r"\[([^\]]+)\]", assignment.lhs_expression):
            for dependency in sorted(expression_signals(index_expr)):
                edges.append({"type": "CONTROL", "source": f"signal:{assignment.module}.{dependency}",
                              "target": assignment_id, "dependency_role": "write_index",
                              "evidence": _source(assignment.file, assignment.line, "indexed destination")})
        for dependency in sorted(expression_signals(assignment.guard)):
            edges.append({"type": "CONTROL", "source": f"signal:{assignment.module}.{dependency}", "target": assignment_id, "evidence": _source(assignment.file, assignment.line, assignment.guard)})
        if assignment.kind == "nonblocking":
            for dependency in assignment.dependencies:
                edges.append({"type": "SEQUENTIAL", "source": f"signal:{assignment.module}.{dependency}", "target": f"signal:{assignment.module}.{assignment.lhs}", "clock": clock, "evidence": _source(assignment.file, assignment.line)})

    return {
        "schema": "rtl-semantic-graph.v1",
        "source_digest": design.source_digest,
        "files": design.files,
        "node_count": len(nodes),
        "edge_count": len(edges),
        "edge_type_counts": {kind: sum(edge["type"] == kind for edge in edges) for kind in ("DATA", "CONTROL", "SEQUENTIAL")},
        "nodes": nodes,
        "edges": edges,
        "assignments": assignment_records,
        "roles": role_evidence,
    }


def connected_signal_cones(graph: dict[str, Any], module: str, signals: Iterable[str]) -> list[list[str]]:
    """Return undirected data/control components among a contract's signals."""
    selected = set(signals)
    adjacency: dict[str, set[str]] = defaultdict(set)
    assignment_inputs: dict[str, set[str]] = defaultdict(set)
    assignment_outputs: dict[str, set[str]] = defaultdict(set)
    prefix = f"signal:{module}."
    for edge in graph.get("edges", []):
        source, target = edge.get("source", ""), edge.get("target", "")
        if source.startswith(prefix) and target.startswith("assignment:"):
            assignment_inputs[target].add(source[len(prefix):])
        if source.startswith("assignment:") and target.startswith(prefix):
            assignment_outputs[source].add(target[len(prefix):])
    for assignment_id in assignment_inputs.keys() | assignment_outputs.keys():
        items = assignment_inputs[assignment_id] | assignment_outputs[assignment_id]
        for left in items:
            adjacency[left].update(items - {left})
    components: list[list[str]] = []
    remaining = set(selected)
    while remaining:
        root = remaining.pop()
        seen = {root}
        stack = [root]
        while stack:
            current = stack.pop()
            for neighbor in adjacency.get(current, set()):
                if neighbor in selected and neighbor not in seen:
                    seen.add(neighbor)
                    remaining.discard(neighbor)
                    stack.append(neighbor)
        components.append(sorted(seen))
    return sorted(components, key=lambda item: (-len(item), item))
