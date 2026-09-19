"""Simple evidence-backed verification-obligation model for Requirement 8.3."""

from __future__ import annotations

from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Any, Iterable


@dataclass(frozen=True)
class ObligationDefinition:
    name: str
    meaning: str
    region_kinds: tuple[str, ...]
    evidence_rule: str


# This is intentionally a small ontology layer.  Applicability is not inferred
# from the region kind alone: a matching, statically grounded candidate with RTL
# evidence is also required below.
OBLIGATION_DEFINITIONS: tuple[ObligationDefinition, ...] = (
    ObligationDefinition("RESET", "state/register reset behavior", ("FSM", "ALWAYS_BLOCK_CLUSTER", "MODULE", "PIPELINE_VALID_FLOW"), "parsed reset assignment"),
    ObligationDefinition("LEGAL_STATE", "state remains in its encoded legal set", ("FSM",), "explicit state encoding and state register"),
    ObligationDefinition("TRANSITION", "state transition follows an RTL transition edge", ("FSM",), "parsed state transition assignment"),
    ObligationDefinition("HOLD", "state/register remains stable when disabled", ("FSM", "ALWAYS_BLOCK_CLUSTER", "MODULE"), "explicit complementary hold condition"),
    ObligationDefinition("REGISTER_UPDATE", "guarded register update uses its RTL source", ("ALWAYS_BLOCK_CLUSTER", "MODULE", "PIPELINE_VALID_FLOW"), "guarded nonblocking assignment"),
    ObligationDefinition("NO_SPURIOUS_WRITE", "register holds outside its update condition", ("ALWAYS_BLOCK_CLUSTER", "MODULE", "PIPELINE_VALID_FLOW"), "exact hold complement of an update"),
    ObligationDefinition("PERSISTENCE", "request remains asserted until completion", ("HANDSHAKE",), "request/completion pair plus registered persistence relation"),
    ObligationDefinition("STABILITY", "payload/control remains stable while waiting", ("HANDSHAKE", "PIPELINE_VALID_FLOW"), "wait condition and stable payload relation"),
    ObligationDefinition("REQUEST_CAUSALITY", "request/control cause reaches its effect", ("HANDSHAKE",), "parsed request/control assignment"),
    ObligationDefinition("COMPLETION", "an accepted request has an evidenced completion relation", ("HANDSHAKE",), "request/completion relation with bounded timing"),
    ObligationDefinition("DATAFLOW_INTEGRITY", "consumer data equals its evidenced producer expression", ("HANDSHAKE", "MODULE", "ALWAYS_BLOCK_CLUSTER", "PIPELINE_VALID_FLOW"), "exact parsed data assignment"),
    ObligationDefinition("CONTROL_PROPAGATION", "control propagates to a downstream effect", ("MODULE", "ALWAYS_BLOCK_CLUSTER", "PIPELINE_VALID_FLOW"), "exact parsed one-bit control assignment"),
    ObligationDefinition("CONTROL_DEASSERTION", "control deassertion propagates through an alias", ("HANDSHAKE", "MODULE", "ALWAYS_BLOCK_CLUSTER", "PIPELINE_VALID_FLOW"), "exact one-bit alias and its complement"),
    ObligationDefinition("CROSS_REGION_DATAFLOW", "data/control traverses a bounded semantic path", ("HANDSHAKE", "MODULE", "ALWAYS_BLOCK_CLUSTER", "PIPELINE_VALID_FLOW"), "two exact assignment edges crossing a region boundary"),
)


def definition_document() -> dict[str, Any]:
    return {
        "schema": "region_flow.3-verification-obligation-definitions.v1",
        "applicability_rule": (
            "An obligation is Applicable only when its ontology region-kind rule matches and at least "
            "one candidate survives deterministic grounding/static validation with explicit RTL evidence."
        ),
        "definitions": [
            {
                "name": item.name,
                "meaning": item.meaning,
                "ontology_region_kinds": list(item.region_kinds),
                "required_rtl_evidence": item.evidence_rule,
            }
            for item in OBLIGATION_DEFINITIONS
        ],
    }


def build_applicability_matrix(
    regions_doc: dict[str, Any], candidates: Iterable[Any]
) -> dict[str, Any]:
    """Return every ontology cell and the exact evidence supporting applicability."""

    definitions = {item.name: item for item in OBLIGATION_DEFINITIONS}
    by_pair: dict[tuple[str, str], list[Any]] = defaultdict(list)
    for candidate in candidates:
        if candidate.rtl_evidence and candidate.rtl_relation:
            by_pair[(candidate.region_id, candidate.obligation)].append(candidate)
    rows = []
    counts: Counter[str] = Counter()
    region_ids = set()
    for region in sorted(regions_doc.get("regions", []), key=lambda item: item["region_id"]):
        region_id = region["region_id"]
        region_ids.add(region_id)
        kind = region.get("kind", "MODULE")
        ontology_names = {item.name for item in OBLIGATION_DEFINITIONS if kind in item.region_kinds}
        evidenced_names = {name for (rid, name) in by_pair if rid == region_id}
        cells = []
        for name in sorted(ontology_names | evidenced_names):
            definition = definitions.get(name)
            kind_matches = definition is None or kind in definition.region_kinds
            evidence_candidates = by_pair.get((region_id, name), [])
            applicable = kind_matches and bool(evidence_candidates)
            status = "APPLICABLE" if applicable else "NOT_APPLICABLE"
            counts[status] += 1
            if not kind_matches:
                reason = "ONTOLOGY_NOT_APPLICABLE"
            elif not evidence_candidates:
                reason = "INSUFFICIENT_EVIDENCE"
            else:
                reason = "RTL_EVIDENCE_PRESENT"
            evidence = []
            for candidate in evidence_candidates:
                for item in candidate.rtl_evidence:
                    evidence.append({
                        "candidate_id": candidate.candidate_id,
                        "files": item.get("files", []),
                        "line_start": item.get("line_start"),
                        "line_end": item.get("line_end"),
                        "snippet": item.get("snippet", ""),
                    })
            cells.append({
                "obligation": name,
                "status": status,
                "applicable": applicable,
                "reason": reason,
                "candidate_ids": sorted(item.candidate_id for item in evidence_candidates),
                "rtl_evidence": evidence,
            })
        rows.append({
            "region_id": region_id,
            "region_kind": kind,
            "module": region.get("module"),
            "obligations": cells,
        })
    # A candidate must never disappear merely because an upstream region
    # document omitted its region.  Keep such cells explicit and auditable.
    for (region_id, name), evidence_candidates in sorted(by_pair.items()):
        if region_id in region_ids:
            continue
        counts["APPLICABLE"] += 1
        rows.append({
            "region_id": region_id,
            "region_kind": evidence_candidates[0].region_kind,
            "module": evidence_candidates[0].module,
            "obligations": [{
                "obligation": name,
                "status": "APPLICABLE",
                "applicable": True,
                "reason": "RTL_EVIDENCE_PRESENT_REGION_SYNTHESIZED",
                "candidate_ids": sorted(item.candidate_id for item in evidence_candidates),
                "rtl_evidence": [evidence for item in evidence_candidates for evidence in item.rtl_evidence],
            }],
        })
    applicable_pairs = sorted(
        [list(pair) for pair, values in by_pair.items() if values]
    )
    return {
        "schema": "region_flow.3-obligation-applicability.v1",
        "definitions": definition_document(),
        "regions": rows,
        "counts": dict(counts),
        "applicable_obligations": len(applicable_pairs),
        "applicable_region_obligation_pairs": applicable_pairs,
    }
