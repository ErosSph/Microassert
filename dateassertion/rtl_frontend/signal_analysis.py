"""Deterministic fan-in/fan-out summaries used as LLM evidence."""

from __future__ import annotations

from collections import defaultdict

from .parser import RTLDesign


def dependency_graph(design: RTLDesign, module: str | None = None) -> dict[str, dict[str, list[str]]]:
    fanin: dict[str, set[str]] = defaultdict(set)
    fanout: dict[str, set[str]] = defaultdict(set)
    known = set(design.module_signals.get(module, {})) if module else set(design.signals)
    for assignment in design.assignments:
        if module and assignment.module != module:
            continue
        for dependency in assignment.dependencies:
            if dependency in known and dependency != assignment.lhs:
                fanin[assignment.lhs].add(dependency)
                fanout[dependency].add(assignment.lhs)
    return {
        signal: {"fanin": sorted(fanin[signal]), "fanout": sorted(fanout[signal])}
        for signal in sorted(known)
        if fanin[signal] or fanout[signal]
    }
