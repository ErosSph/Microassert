"""Audit the gap between a structural candidate and a complete architecture contract.

These are obligation schemas, NOT new executable SVA templates. A compiler must
still ground every role and validate its timing before emitting a property.
"""

ARCHITECTURE_OBLIGATIONS = {
    "REGISTER_FILE": {
        "reusable_primitives": ["INDEXED_READ", "INDEXED_WRITE", "HOLD", "DATA_INTEGRITY"],
        "mapping_status": "LOCAL_INDEXED_RELATIONS_ONLY_PENDING_SPEC",
        "missing": ["hierarchical_or_multidimensional_storage_observation", "SPEC_read_collision_policy",
                    "bypass_selection", "SPEC_reserved_register_policy"],
    },
    "LSU": {
        "reusable_primitives": ["UPDATE", "DATA_INTEGRITY", "STABILITY", "CAUSALITY"],
        "mapping_status": "LOCAL_DATAPATH_ONLY_PENDING_GROUNDING",
        "missing": ["SPEC_memory_interface_binding", "request_acceptance_and_response_events",
                    "alignment_exception_policy", "store_side_effects"],
    },
    "ITERATIVE_MULTIPLIER": {
        "reusable_primitives": ["RESET", "UPDATE", "HOLD", "CONTROL_ASSERT"],
        "mapping_status": "LOCAL_STEPS_ONLY_PENDING_GROUNDING",
        "missing": ["operand_snapshot_at_acceptance", "signedness_and_overflow",
                    "end_to_end_arithmetic_result", "proved_iteration_bound"],
    },
    "ITERATIVE_DIVIDER": {
        "reusable_primitives": ["RESET", "UPDATE", "HOLD", "CONTROL_ASSERT"],
        "mapping_status": "LOCAL_STEPS_ONLY_PENDING_GROUNDING",
        "missing": ["operand_snapshot_at_acceptance", "signedness_and_overflow", "divide_by_zero_policy",
                    "end_to_end_arithmetic_result", "proved_iteration_bound"],
    },
}


def architecture_contract_support(kind, certificate=None):
    entry = ARCHITECTURE_OBLIGATIONS.get(kind)
    if entry is None:
        return None
    observed_missing = (certificate or {}).get("composition_details", {}).get("unresolved_obligations", [])
    return {"schema": "architecture-contract-support.v1", "architecture": kind,
            "mapping_status": entry["mapping_status"],
            "reusable_primitives_requiring_grounding": list(entry["reusable_primitives"]),
            "unresolved_obligations": sorted(set(entry["missing"]) | set(observed_missing)),
            "full_architecture_contract_ready": False, "generated_sva_count": None,
            "interpretation": "Structural match only; no claim of generated or proven architecture correctness."}
