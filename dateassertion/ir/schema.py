"""Versioned intermediate representations for the microarchitecture pipeline."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from enum import Enum
from pathlib import Path
from typing import Any
import json


SCHEMA_VERSION = "microarch-ir.v1"


class ObjectType(str, Enum):
    FSM = "FSM"
    HANDSHAKE = "HANDSHAKE"
    REGISTER_UPDATE = "REGISTER_UPDATE"
    DATAPATH = "DATAPATH"
    PIPELINE = "PIPELINE"
    DECODE = "DECODE"
    REQUEST_RESPONSE = "REQUEST_RESPONSE"
    RESOURCE = "RESOURCE"
    # Dynamic object names are carried by RegionIR.extension_type.  Keeping a
    # single compiler-visible EXTENSION value prevents an LLM from changing the
    # downstream type system at runtime.
    EXTENSION = "EXTENSION"
    UNKNOWN = "UNKNOWN"


class PropertySource(str, Enum):
    SPEC_BACKED = "SPEC_BACKED"
    # Req8.7 reserves this stronger label for a supplied SPEC statement that
    # has exact source evidence, a concrete RTL signal mapping, and Formal
    # validation. SPEC_BACKED remains available for older pipelines.
    SPEC_CONFORMANCE = "SPEC_CONFORMANCE"
    RTL_STRUCTURAL = "RTL_STRUCTURAL"
    LLM_HYPOTHESIS = "LLM_HYPOTHESIS"


@dataclass
class SourceEvidence:
    rtl_files: list[str]
    line_start: int
    line_end: int
    snippet: str
    confidence: float = 0.0
    correctness_sources: list[str] = field(default_factory=list)


@dataclass
class SignalInfo:
    name: str
    width: str = ""
    direction: str = "internal"
    kind: str = "logic"
    module: str = ""
    file: str = ""
    line: int = 0
    constant_expression: str | None = None
    unpacked_dimensions: list[str] = field(default_factory=list)


@dataclass
class AssignmentInfo:
    lhs: str
    rhs: str
    kind: str
    guard: str
    module: str
    file: str
    line: int
    dependencies: list[str] = field(default_factory=list)
    # Preserve the indexed destination without changing the legacy base lhs.
    lhs_expression: str = ""


@dataclass
class VerificationRegion:
    region_id: str
    suggested_type: ObjectType
    module: str
    signals: list[str]
    dependencies: dict[str, list[str]]
    evidence: SourceEvidence
    metadata: dict[str, Any] = field(default_factory=dict)


@dataclass
class RegionIR:
    region_id: str
    type: ObjectType
    name: str
    module: str
    signals: dict[str, Any]
    events: dict[str, Any]
    attributes: dict[str, Any]
    evidence: SourceEvidence
    confidence: float
    analysis_source: str
    details: dict[str, Any] = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)
    ontology_classification: str = "CORE_OBJECT"
    extension_type: str | None = None


@dataclass
class ContractIR:
    """CPU-independent semantic contract consumed by template binding.

    All fields are deliberately data, not executable SVA.  Extension objects
    use the same representation as core objects and can only reach the SVA
    compiler through the fixed primitive vocabulary.
    """

    contract_id: str
    object_type: str
    ontology_classification: str
    region: str
    module: str
    state: list[str] = field(default_factory=list)
    events: dict[str, Any] = field(default_factory=dict)
    inputs: list[str] = field(default_factory=list)
    outputs: list[str] = field(default_factory=list)
    dependencies: dict[str, list[str]] = field(default_factory=dict)
    invariants: list[dict[str, Any]] = field(default_factory=list)
    update_rules: list[dict[str, Any]] = field(default_factory=list)
    hold_rules: list[dict[str, Any]] = field(default_factory=list)
    ordering: list[dict[str, Any]] = field(default_factory=list)
    causality: list[dict[str, Any]] = field(default_factory=list)
    stability: list[dict[str, Any]] = field(default_factory=list)
    data_integrity: list[dict[str, Any]] = field(default_factory=list)
    mutual_exclusion: list[dict[str, Any]] = field(default_factory=list)
    reset_behavior: list[dict[str, Any]] = field(default_factory=list)
    assumptions: list[dict[str, Any]] = field(default_factory=list)
    evidence: list[dict[str, Any]] = field(default_factory=list)
    reused_primitives: list[str] = field(default_factory=list)
    new_property_family_candidates: list[dict[str, Any]] = field(default_factory=list)


@dataclass
class TemplateBindingIR:
    binding_id: str
    contract_id: str
    region_id: str
    object_type: str
    ontology_classification: str
    level: int
    primitive: str
    property_family: str
    semantic_roles: dict[str, Any]
    status: str
    reason: str = ""
    property_id: str | None = None


@dataclass
class MicroarchitectureIR:
    design: str
    top_module: str
    regions: list[RegionIR]
    schema_version: str = SCHEMA_VERSION
    rtl_files: list[str] = field(default_factory=list)


@dataclass
class PropertyIR:
    property_id: str
    region_id: str
    object_type: ObjectType
    family: str
    template: str
    bindings: dict[str, Any]
    signals: list[str]
    source: str
    llm_confidence: float
    body: str
    disable_iff: str | None = "!resetn"
    description: str = ""
    sva: str = ""
    source_classification: str = PropertySource.RTL_STRUCTURAL.value
    iteration_added: int = 0
    coverage_gain: int | None = None
    lifecycle_status: str = "ACTIVE"
    review_status: str = "NONE"
    evidence: list[dict[str, Any]] = field(default_factory=list)
    target_module: str = ""
    hard_gap_cluster_id: str | None = None
    observation_helper_ids: list[str] = field(default_factory=list)


@dataclass
class FormalPropertyResult:
    property_id: str
    result: str
    runtime_seconds: float | None = None
    proof_core_items: int | None = None
    vacuity: str | None = None
    counterexample_path: str | None = None
    notes: str = ""
    classification: str = "UNKNOWN"
    source_classification: str = PropertySource.RTL_STRUCTURAL.value
    review_status: str = "NONE"
    target_count: int = 0
    target_summary: dict[str, int] = field(default_factory=dict)
    target_results: list[dict[str, Any]] = field(default_factory=list)
    target_vacuity_summary: dict[str, int] = field(default_factory=dict)


@dataclass
class FormalRunResult:
    status: str
    tool: str
    runtime_seconds: float
    log_path: str
    results: list[FormalPropertyResult] = field(default_factory=list)
    summary: dict[str, Any] = field(default_factory=dict)
    coverage: dict[str, Any] = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)


def _convert(value: Any) -> Any:
    if isinstance(value, Enum):
        return value.value
    if hasattr(value, "__dataclass_fields__"):
        return {key: _convert(item) for key, item in asdict(value).items()}
    if isinstance(value, dict):
        return {key: _convert(item) for key, item in value.items()}
    if isinstance(value, list):
        return [_convert(item) for item in value]
    return value


def dump_json(path: str | Path, value: Any) -> None:
    target = Path(path)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(_convert(value), indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def load_json(path: str | Path) -> Any:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def evidence_from_dict(data: dict[str, Any]) -> SourceEvidence:
    return SourceEvidence(**data)


def region_from_dict(data: dict[str, Any]) -> VerificationRegion:
    copied = dict(data)
    copied["suggested_type"] = ObjectType(copied["suggested_type"])
    copied["evidence"] = evidence_from_dict(copied["evidence"])
    return VerificationRegion(**copied)


def microarchitecture_from_dict(data: dict[str, Any]) -> MicroarchitectureIR:
    regions = []
    for raw in data["regions"]:
        copied = dict(raw)
        copied["type"] = ObjectType(copied["type"])
        copied["evidence"] = evidence_from_dict(copied["evidence"])
        regions.append(RegionIR(**copied))
    return MicroarchitectureIR(
        design=data["design"],
        top_module=data["top_module"],
        regions=regions,
        schema_version=data.get("schema_version", SCHEMA_VERSION),
        rtl_files=data.get("rtl_files", []),
    )


def properties_from_dict(data: list[dict[str, Any]]) -> list[PropertyIR]:
    result = []
    for raw in data:
        copied = dict(raw)
        copied["object_type"] = ObjectType(copied["object_type"])
        result.append(PropertyIR(**copied))
    return result
