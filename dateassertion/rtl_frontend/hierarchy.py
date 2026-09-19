"""Small hierarchy helpers kept separate from syntax extraction."""

from __future__ import annotations

from .parser import RTLDesign


def reachable_modules(design: RTLDesign, top: str) -> list[str]:
    """Return deterministic preorder of modules instantiated below ``top``."""
    modules = {module.name: module for module in design.modules}
    if top not in modules:
        raise ValueError(f"top module {top!r} not found; available: {sorted(modules)}")
    ordered: list[str] = []
    seen: set[str] = set()

    def walk(name: str) -> None:
        if name in seen or name not in modules:
            return
        seen.add(name)
        ordered.append(name)
        for instance in modules[name].instances:
            walk(instance["module"])

    walk(top)
    return ordered


def hierarchy_summary(design: RTLDesign, top: str) -> dict:
    modules = {module.name: module for module in design.modules}
    if top not in modules:
        raise ValueError(f"top module {top!r} not found; available: {sorted(modules)}")

    def walk(name: str, seen: set[str]) -> dict:
        module = modules[name]
        children = []
        for instance in module.instances:
            target = instance["module"]
            child = {"instance": instance["instance"], "module": target}
            if target in modules and target not in seen:
                child["children"] = walk(target, seen | {target})["children"]
            children.append(child)
        return {"module": name, "children": children}

    return walk(top, {top})
