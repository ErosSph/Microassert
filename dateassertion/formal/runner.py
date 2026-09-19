"""Formal execution abstraction and normalized result values."""

from __future__ import annotations

from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any

from dateassertion.ir.schema import FormalRunResult, PropertyIR


class FormalRunner(ABC):
    @abstractmethod
    def run(
        self,
        rtl_files: list[str],
        property_file: str,
        top_module: str,
        properties: list[PropertyIR],
        output_dir: str | Path,
        config: dict[str, Any],
    ) -> FormalRunResult:
        raise NotImplementedError
