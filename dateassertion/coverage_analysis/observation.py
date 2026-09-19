"""Safe verification-only observation helper validation and rendering."""

from __future__ import annotations

from pathlib import Path
import re
from typing import Any

from dateassertion.ir.schema import dump_json


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_$]*")
SAFE_BOOLEAN = re.compile(
    r"^[A-Za-z0-9_$'bBoOdDhHxXzZ_\s()!~&|^]+$"
)


def validate_observation_helpers(
    raw_helpers: Any,
    known_signals: set[str],
    allowed_files: set[str],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    accepted: list[dict[str, Any]] = []
    rejected: list[dict[str, Any]] = []
    if not isinstance(raw_helpers, list):
        return accepted, rejected
    used: set[str] = set()
    for raw in raw_helpers:
        reasons: list[str] = []
        if not isinstance(raw, dict):
            rejected.append({"helper": raw, "reasons": ["helper is not an object"]})
            continue
        helper_id = str(raw.get("helper_id", ""))
        expression = str(raw.get("expression", "")).strip()
        module = str(raw.get("module", ""))
        if not re.fullmatch(r"obs_[A-Za-z_][A-Za-z0-9_$]*", helper_id) or helper_id in used:
            reasons.append("helper_id must be a unique obs_* identifier")
        if not expression or not SAFE_BOOLEAN.fullmatch(expression):
            reasons.append("helper must be a pure boolean alias using only !, ~, &, |, ^ and parentheses")
        names = set(IDENT.findall(re.sub(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+", " ", expression)))
        invented = names - known_signals
        if invented:
            reasons.append(f"helper references unavailable signals: {sorted(invented)}")
        if len(names) < 2:
            reasons.append("helper must name a composite event rather than alias one signal")
        # Prohibit temporal functions, arithmetic, equality/comparison and ternaries.
        # This ensures a helper names an event/conjunction and cannot recompute a result.
        if re.search(r"\$|==|!=|<=|>=|[+*/%?:<>-]", expression):
            reasons.append("helper attempts temporal/arithmetic/comparison computation")
        evidence = []
        for item in raw.get("evidence", []) if isinstance(raw.get("evidence"), list) else []:
            file = str(item.get("file", "")) if isinstance(item, dict) else ""
            try:
                line = int(item.get("line", 0))
            except (TypeError, ValueError, AttributeError):
                line = 0
            if file not in allowed_files or line < 1 or not Path(file).is_file():
                continue
            lines = Path(file).read_text(encoding="utf-8", errors="replace").splitlines()
            if line > len(lines) or not (set(IDENT.findall(lines[line - 1])) & names):
                continue
            evidence.append({"file": file, "line": line, "source": lines[line - 1].strip()})
        if not evidence:
            reasons.append("helper has no source evidence containing a referenced signal")
        if not module:
            reasons.append("helper module is required")
        if reasons:
            rejected.append({"helper": raw, "reasons": reasons})
            continue
        used.add(helper_id)
        accepted.append(
            {
                "helper_id": helper_id,
                "module": module,
                "expression": expression,
                "signals": sorted(names),
                "evidence": evidence,
                "verification_only": True,
                "functional_behavior_changed": False,
                "safety_policy": "pure boolean event alias; no temporal/arithmetic/comparison logic",
            }
        )
    return accepted, rejected


def write_observation_artifacts(
    helpers: list[dict[str, Any]], output_dir: str | Path
) -> None:
    output = Path(output_dir)
    output.mkdir(parents=True, exist_ok=True)
    unique = {item["helper_id"]: item for item in helpers}
    ordered = [unique[name] for name in sorted(unique)]
    dump_json(output / "helpers.json", ordered)
    lines = [
        "// Verification-only helper fragments; embedded in generated assertion checkers.",
        "// These aliases do not drive or modify DUT state.",
    ]
    for helper in ordered:
        evidence = helper.get("evidence", [{}])[0]
        lines.append(
            f"// {helper['helper_id']} <- {evidence.get('file', '')}:{evidence.get('line', '')}"
        )
        lines.append(f"wire {helper['helper_id']} = {helper['expression']};")
    (output / "generated_helpers.sv").write_text("\n".join(lines) + "\n", encoding="utf-8")
