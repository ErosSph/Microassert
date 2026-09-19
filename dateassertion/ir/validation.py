"""Strict validation at the two non-deterministic pipeline boundaries."""

from __future__ import annotations

import re
from typing import Any, Iterable

from .schema import MicroarchitectureIR, ObjectType, PropertyIR, RegionIR, VerificationRegion


IDENTIFIER = re.compile(r"^[A-Za-z_][A-Za-z0-9_$]*$")


class ValidationError(ValueError):
    pass


def _flatten_signal_values(value: Any) -> Iterable[str]:
    if isinstance(value, str):
        yield value
    elif isinstance(value, list):
        for item in value:
            yield from _flatten_signal_values(item)
    elif isinstance(value, dict):
        for item in value.values():
            yield from _flatten_signal_values(item)


def validate_candidate(region: VerificationRegion, known_signals: set[str]) -> None:
    if not region.region_id or not region.module:
        raise ValidationError("candidate region_id and module are required")
    unknown = set(region.signals) - known_signals
    if unknown:
        raise ValidationError(f"candidate {region.region_id} references unknown signals: {sorted(unknown)}")
    if region.evidence.line_start < 1 or region.evidence.line_end < region.evidence.line_start:
        raise ValidationError(f"candidate {region.region_id} has invalid evidence lines")


def validate_region_ir(region: RegionIR, candidate: VerificationRegion, known_signals: set[str]) -> None:
    if region.region_id != candidate.region_id:
        raise ValidationError("LLM changed region_id")
    if not isinstance(region.type, ObjectType):
        raise ValidationError("invalid object type")
    if not 0.0 <= float(region.confidence) <= 1.0:
        raise ValidationError("confidence must be in [0, 1]")
    referenced = set(_flatten_signal_values(region.signals))
    # Candidate-local validation is stronger than design-global validation and
    # prevents same-named signals in another module from laundering an LLM role.
    available = set(candidate.signals)
    invalid = {signal for signal in referenced if not IDENTIFIER.match(signal) or signal not in available}
    if invalid:
        raise ValidationError(f"region {region.region_id} contains invented or invalid signals: {sorted(invalid)}")
    expression_fields = [region.details.get(name) for name in ("enable", "update_expression", "expression")]
    expression_fields.extend(region.events.values())
    allowed_words = {"signed", "unsigned", "past", "stable", "true", "false"}
    for expression in expression_fields:
        if not isinstance(expression, str):
            continue
        cleaned = re.sub(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+", " ", expression)
        cleaned = re.sub(r"`[A-Za-z_][A-Za-z0-9_$]*", " ", cleaned)
        names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", cleaned)) - allowed_words
        invented = names - known_signals
        if invented:
            raise ValidationError(
                f"region {region.region_id} expression contains invented signals: {sorted(invented)}"
            )
    if region.type != ObjectType.UNKNOWN and not referenced:
        raise ValidationError(f"region {region.region_id} has no signal bindings")
    if region.ontology_classification not in {"CORE_OBJECT", "NEW_OBJECT_CANDIDATE"}:
        raise ValidationError(f"region {region.region_id} has invalid ontology classification")
    if region.type == ObjectType.EXTENSION:
        if region.ontology_classification != "NEW_OBJECT_CANDIDATE" or not region.extension_type:
            raise ValidationError(f"region {region.region_id} has an incomplete extension identity")
        payload = region.details.get("extension_candidate")
        if not isinstance(payload, dict) or not str(payload.get("reason", "")).strip():
            raise ValidationError(f"region {region.region_id} extension lacks behavioral reason")
        for key in ("state", "inputs", "outputs"):
            values = payload.get(key, [])
            if values is not None and not isinstance(values, list):
                raise ValidationError(f"region {region.region_id} extension {key} must be a list")
            invalid_values = [
                item for item in (values or [])
                if not isinstance(item, str) or not IDENTIFIER.match(item) or item not in available
            ]
            if invalid_values:
                raise ValidationError(f"region {region.region_id} extension {key} has invalid signals: {sorted(map(str, invalid_values))}")
        dependencies = payload.get("dependencies", {})
        if dependencies is not None and not isinstance(dependencies, dict):
            raise ValidationError(f"region {region.region_id} extension dependencies must be an object")
        for name, values in (dependencies or {}).items():
            if name not in available or not isinstance(values, list) or any(value not in available for value in values):
                raise ValidationError(f"region {region.region_id} extension dependency is not candidate-local: {name}")
        allowed_primitives = {
            "UPDATE", "HOLD", "CAUSALITY", "ORDERING", "STABILITY", "DATA_INTEGRITY",
            "MUTUAL_EXCLUSION", "PERSISTENCE", "CONSERVATION", "RESET", "PROGRESS",
            "CONTROL_ASSERT", "CONTROL_DEASSERT",
        }
        for invariant in payload.get("invariants", []) or []:
            if not isinstance(invariant, dict) or str(invariant.get("primitive", "")).upper() not in allowed_primitives:
                raise ValidationError(f"region {region.region_id} extension invariant uses an unknown primitive")
            roles = invariant.get("roles", {})
            if not isinstance(roles, dict):
                raise ValidationError(f"region {region.region_id} extension invariant roles must be an object")
            for value in _flatten_signal_values(roles):
                cleaned = re.sub(r"(?:\d+)?'[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+", " ", value)
                names = set(re.findall(r"[A-Za-z_][A-Za-z0-9_$]*", cleaned)) - allowed_words
                invented = names - available
                if invented:
                    raise ValidationError(f"region {region.region_id} extension invariant invents signals: {sorted(invented)}")
    elif region.ontology_classification != "CORE_OBJECT":
        raise ValidationError(f"region {region.region_id} core type has inconsistent classification")


def validate_microarchitecture(ir: MicroarchitectureIR, candidates: list[VerificationRegion], known_signals: set[str]) -> None:
    if ir.schema_version != "microarch-ir.v1":
        raise ValidationError(f"unsupported schema: {ir.schema_version}")
    by_id = {candidate.region_id: candidate for candidate in candidates}
    if len(by_id) != len(candidates):
        raise ValidationError("duplicate candidate ids")
    for region in ir.regions:
        if region.region_id not in by_id:
            raise ValidationError(f"IR region without candidate: {region.region_id}")
        validate_region_ir(region, by_id[region.region_id], known_signals)


def validate_properties(properties: list[PropertyIR], ir: MicroarchitectureIR, known_signals: set[str]) -> None:
    ids: set[str] = set()
    region_ids = {region.region_id for region in ir.regions}
    for prop in properties:
        if prop.property_id in ids:
            raise ValidationError(f"duplicate property id: {prop.property_id}")
        ids.add(prop.property_id)
        if prop.region_id not in region_ids and not any(item.get("coverage_region_id") == prop.region_id for item in prop.evidence):
            raise ValidationError(f"property {prop.property_id} references unknown region")
        unknown = set(prop.signals) - known_signals
        if unknown:
            raise ValidationError(f"property {prop.property_id} references unknown signals: {sorted(unknown)}")
        if not prop.family or not prop.template or not prop.body:
            raise ValidationError(f"property {prop.property_id} is incomplete")
