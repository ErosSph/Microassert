"""Parse JasperGold 21.12 per-cover-item exports without losing source evidence."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from pathlib import Path
import re
from typing import Any


@dataclass(frozen=True)
class CoverItem:
    cid: int
    status: str
    formal_status: str
    checker_status: str
    cover_item_type: str
    description: str
    expression: str
    module: str
    instance: str
    file: str
    line_start: int
    column_start: int
    line_end: int
    column_end: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def split_tcl_list(text: str) -> list[str]:
    """Split the brace-quoted Tcl list format emitted by check_cov -list."""
    result: list[str] = []
    index = 0
    length = len(text)
    while index < length:
        while index < length and text[index].isspace():
            index += 1
        if index >= length:
            break
        if text[index] == "{":
            index += 1
            depth = 1
            value: list[str] = []
            while index < length and depth:
                char = text[index]
                if char == "\\" and index + 1 < length:
                    value.extend((char, text[index + 1]))
                    index += 2
                    continue
                if char == "{":
                    depth += 1
                    value.append(char)
                elif char == "}":
                    depth -= 1
                    if depth:
                        value.append(char)
                else:
                    value.append(char)
                index += 1
            if depth:
                raise ValueError("unterminated brace in JasperGold Tcl list")
            result.append("".join(value))
            continue
        if text[index] == '"':
            index += 1
            value = []
            while index < length and text[index] != '"':
                if text[index] == "\\" and index + 1 < length:
                    index += 1
                value.append(text[index])
                index += 1
            index += index < length
            result.append("".join(value))
            continue
        value = []
        while index < length and not text[index].isspace():
            if text[index] == "\\" and index + 1 < length:
                index += 1
            value.append(text[index])
            index += 1
        result.append("".join(value))
    return result


def _record(payload: str) -> dict[str, str]:
    values = split_tcl_list(payload.strip())
    if len(values) % 2:
        raise ValueError(f"odd JasperGold cover-item record ({len(values)} fields)")
    return dict(zip(values[0::2], values[1::2]))


def parse_coverage_items(path: str | Path) -> list[CoverItem]:
    source = Path(path)
    if not source.is_file():
        return []
    by_id: dict[int, CoverItem] = {}
    for line_number, line in enumerate(source.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if "\t" not in line:
            continue
        status, payload = line.split("\t", 1)
        try:
            raw = _record(payload)
            cid = int(raw["cid"])
            location = re.fullmatch(r"\((\d+),(\d+)\)-\((\d+),(\d+)\)", raw.get("source_location", ""))
            if not location:
                continue
            item = CoverItem(
                cid=cid,
                status=status,
                formal_status=raw.get("formal_status", ""),
                checker_status=raw.get("checker_status", ""),
                cover_item_type=raw.get("cover_item_type", ""),
                description=raw.get("description", ""),
                expression=raw.get("expression", ""),
                module=raw.get("module", ""),
                instance=raw.get("instance", ""),
                file=raw.get("file", ""),
                line_start=int(location.group(1)),
                column_start=int(location.group(2)),
                line_end=int(location.group(3)),
                column_end=int(location.group(4)),
            )
        except (KeyError, ValueError) as exc:
            raise ValueError(f"invalid coverage item at {source}:{line_number}: {exc}") from exc
        previous = by_id.get(cid)
        if previous and previous.status != status:
            raise ValueError(f"cover item {cid} appears in conflicting statuses")
        by_id[cid] = item
    return sorted(by_id.values(), key=lambda item: item.cid)


def parse_coverage_statuses(path: str | Path) -> dict[int, set[str]]:
    """Parse overlapping exact Jasper status lists keyed by cover-item ID."""
    source = Path(path)
    if not source.is_file():
        return {}
    memberships: dict[int, set[str]] = {}
    for line_number, line in enumerate(source.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if "\t" not in line:
            continue
        status, payload = line.split("\t", 1)
        try:
            cid = int(_record(payload)["cid"])
        except (KeyError, ValueError) as exc:
            raise ValueError(f"invalid coverage status at {source}:{line_number}: {exc}") from exc
        memberships.setdefault(cid, set()).add(status)
    return memberships


def stimuli_coverage_summary(path: str | Path) -> dict[str, Any]:
    """Summarize independent Jasper stimuli coverage by RTL item type.

    Jasper status lists overlap, so this parser first unions memberships by
    cover-item ID and then assigns one deterministic outcome precedence:
    covered, unreachable/deadcode, uncovered, and finally unprocessed.
    """

    source = Path(path)
    records: dict[int, dict[str, Any]] = {}
    if source.is_file():
        for line_number, line in enumerate(
            source.read_text(encoding="utf-8", errors="replace").splitlines(), 1
        ):
            if "\t" not in line:
                continue
            status, payload = line.split("\t", 1)
            try:
                raw = _record(payload)
                cid = int(raw["cid"])
            except (KeyError, ValueError) as exc:
                raise ValueError(
                    f"invalid stimuli coverage item at {source}:{line_number}: {exc}"
                ) from exc
            record = records.setdefault(cid, {
                "cover_item_type": raw.get("cover_item_type", ""),
                "statuses": set(),
            })
            record["statuses"].add(status.lower())

    def metric(raw_type: str) -> dict[str, Any]:
        selected = [
            item for item in records.values()
            if item["cover_item_type"].lower() == raw_type
        ]
        covered = sum("covered" in item["statuses"] for item in selected)
        unreachable = sum(bool(
            {"unreachable", "deadcode"} & item["statuses"]
        ) and "covered" not in item["statuses"] for item in selected)
        uncovered = sum(
            "uncovered" in item["statuses"]
            and "covered" not in item["statuses"]
            and not ({"unreachable", "deadcode"} & item["statuses"])
            for item in selected
        )
        unprocessed = len(selected) - covered - unreachable - uncovered
        reachable = covered + uncovered
        return {
            "jasper_cover_item_type": raw_type,
            "covered": covered,
            "uncovered": uncovered,
            "unreachable_or_deadcode": unreachable,
            "unprocessed": unprocessed,
            "total": len(selected),
            "raw_percent": round(100 * covered / len(selected), 2) if selected else 0.0,
            "effective_reachable_denominator": reachable,
            "effective_percent": round(100 * covered / reachable, 2) if reachable else 0.0,
        }

    return {
        "statement": metric("statement"),
        "branch": metric("branch"),
        "toggle": metric("toggle"),
    }


def coverage_item_summary(items: list[CoverItem]) -> dict[str, Any]:
    counts = {
        status: sum(item.status == status for item in items)
        for status in ("covered_and_checked", "uncovered_or_unchecked", "unreachable_or_undetectable")
    }
    covered = counts["covered_and_checked"]
    reachable = covered + counts["uncovered_or_unchecked"]
    total = len(items)
    return {
        **counts,
        "total_items": total,
        "official_proof_core_coverage_percent": round(100.0 * covered / total, 2) if total else 0.0,
        "effective_reachable_denominator": reachable,
        "effective_reachable_coverage_percent": round(100.0 * covered / reachable, 2) if reachable else 0.0,
    }
