"""Select bounded feedback work by exact overlap with current unchecked items.

This is greedy maximum coverage of mapped *opportunities*, not a prediction
that Jasper will cover these items. No SVA text is removed or deduplicated.
"""
from collections import defaultdict
import re


_IDENTIFIER = r"[A-Za-z_$][A-Za-z0-9_$]*"
_ONE_BIT_LITERAL = r"(?:0|1|1'[bBdD][01])"


def _strip_outer_parentheses(expression):
    """Remove only parentheses that enclose the whole expression."""

    value = str(expression or "").strip()
    while value.startswith("(") and value.endswith(")"):
        depth = 0
        encloses_all = True
        for index, char in enumerate(value):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0 and index != len(value) - 1:
                    encloses_all = False
                    break
            if depth < 0:
                return value
        if depth != 0 or not encloses_all:
            return value
        value = value[1:-1].strip()
    return value


def _one_bit_value(value):
    normalized = str(value).replace("_", "").lower()
    return {"0": 0, "1'b0": 0, "1'd0": 0, "1": 1, "1'b1": 1, "1'd1": 1}.get(normalized)


def _certain_boolean_literal(expression):
    """Return a syntactic truth relation without assuming the signal width.

    ``!signal`` and ``signal == 0`` mean the vector is zero; a bare signal is
    merely truthy (nonzero); and ``signal == 1`` means its exact numeric value
    is one.  In particular, bitwise ``~signal`` is deliberately unsupported.
    """

    value = _strip_outer_parentheses(expression)
    inverse = re.fullmatch(rf"!\s*({_IDENTIFIER})", value)
    if inverse:
        return inverse.group(1), "ZERO"
    direct = re.fullmatch(rf"({_IDENTIFIER})", value)
    if direct:
        return direct.group(1), "TRUTHY"
    equality = re.fullmatch(
        rf"({_IDENTIFIER})\s*==\s*({_ONE_BIT_LITERAL})|({_ONE_BIT_LITERAL})\s*==\s*({_IDENTIFIER})",
        value,
    )
    if not equality:
        return None
    if equality.group(1):
        bit = _one_bit_value(equality.group(2))
        return equality.group(1), "ZERO" if bit == 0 else "ONE"
    bit = _one_bit_value(equality.group(3))
    return equality.group(4), "ZERO" if bit == 0 else "ONE"


def _trigger_implies_disabled(trigger, disabled):
    """Check only width-independent implications between parsed relations."""

    trigger_signal, trigger_relation = trigger
    disabled_signal, disabled_relation = disabled
    if trigger_signal != disabled_signal:
        return False
    return (
        trigger_relation == disabled_relation
        or (trigger_relation == "ONE" and disabled_relation == "TRUTHY")
    )


def _property_antecedent(body):
    """Extract a simple implication antecedent; nested/ambiguous bodies skip."""

    value = str(body or "")
    operators = [operator for operator in ("|->", "|=>") if operator in value]
    if len(operators) != 1:
        return None
    before, _operator, after = value.partition(operators[0])
    if not before.strip() or not after.strip() or operators[0] in after:
        return None
    return _strip_outer_parentheses(before)


def _certain_reset_guard_contradiction(prop):
    """Return an audit record iff ``disable iff`` and trigger assert one bit.

    This intentionally does not simplify Boolean expressions.  It handles only
    an exact identifier, its unary inverse, or equality to a one-bit literal;
    every compound guard remains eligible for normal Formal evaluation.
    """

    disabled = _certain_boolean_literal(getattr(prop, "disable_iff", ""))
    antecedent = _property_antecedent(getattr(prop, "body", ""))
    trigger = _certain_boolean_literal(antecedent) if antecedent is not None else None
    if not disabled or not trigger or not _trigger_implies_disabled(trigger, disabled):
        return None
    signal, relation = disabled
    return {
        "property_id": prop.property_id,
        "reason": "DISABLE_IFF_AND_ANTECEDENT_ASSERT_SAME_RESET_VALUE",
        "disposition": "DEFERRED_PENDING_EXPORT",
        "reset_signal": signal,
        "reset_value": {"ZERO": 0, "ONE": 1}.get(relation, "NONZERO"),
        "disable_relation": relation,
        "antecedent_relation": trigger[1],
        "disable_iff": prop.disable_iff,
        "antecedent": antecedent,
    }


def select_current_gap_work(entries, records, budget):
    by_node = defaultdict(set)
    for row in records:
        if row.get("official_status") != "uncovered_or_unchecked" or row.get("gap_type") == "D_NON_ACTIONABLE":
            continue
        for nid in row.get("graph_node_ids", []):
            by_node[nid].add(str(row.get("rtl_item_id", row["cid"])))
    opportunities = []
    anchors = []
    eligible_indices = []
    excluded = []
    for index, entry in enumerate(entries):
        contradiction = _certain_reset_guard_contradiction(entry["property"])
        if contradiction:
            excluded.append({**contradiction, "entry_index": index})
            continue
        metadata = entry.get("metadata", {})
        # Only exact assignment anchors, not all contextual signals or a
        # whole Region's nodes, may claim an opportunity for this assertion.
        ids = {metadata.get("assignment_id")}
        ids.update(metadata.get("assignment_ids", []))
        evidence = metadata.get("primary_binding_evidence", {})
        ids.add(evidence.get("candidate_anchor_node_id"))
        ids.update(e.get("graph_node_id") for e in entry["property"].evidence if isinstance(e, dict))
        ids = {nid for nid in ids if isinstance(nid, str) and nid.startswith("assignment:")}
        anchors.append(ids)
        opportunities.append(set().union(*(by_node[nid] for nid in ids)))
        eligible_indices.append(index)
    remaining = list(range(len(eligible_indices)))
    chosen, covered, rows = [], set(), []
    for _ in range(min(max(0, budget), len(eligible_indices))):
        # Stable FIFO ties preserve fairness for equal/unknown opportunity.
        best = max(remaining, key=lambda i: (len(opportunities[i] - covered), -i))
        marginal = opportunities[best] - covered
        entry_index = eligible_indices[best]
        rows.append({"property_id": entries[entry_index]["property"].property_id,
                     "assignment_anchors": sorted(anchors[best]),
                     "current_unchecked_items": len(opportunities[best]),
                     "marginal_unchecked_items": len(marginal),
                     "marginal_item_ids": sorted(marginal)})
        covered.update(marginal)
        chosen.append(best)
        remaining.remove(best)
    fifo = set().union(*opportunities[:max(0, budget)])
    audit = {"policy": "GREEDY_CURRENT_MAPPED_GAP_COVERAGE", "selected": rows,
             "candidate_records": len(entries), "eligible_candidate_records": len(eligible_indices),
             "selected_records": len(chosen),
             "fifo_mapped_unchecked_union": len(fifo),
             "selected_mapped_unchecked_union": len(covered),
             "predicted_formal_gain": None, "sva_deduplication": False,
             "excluded_reset_guard_contradictions": excluded}
    selected_indices = {eligible_indices[index] for index in chosen}
    # Excluded entries remain in the deferred queue so the caller exports them
    # and can reconsider them if their generated SVA changes in a later round.
    return (
        [entries[index] for index in sorted(selected_indices)],
        [entry for index, entry in enumerate(entries) if index not in selected_indices],
        audit,
    )
