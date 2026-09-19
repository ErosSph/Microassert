"""Small complete-family predicates used by structural invariant contracts."""
import re
from dateassertion.rtl_frontend.graph_motif_matching import expression, unparen, literal, compact, bare_name, same_clock, conjunction


def reset_guard_asserted(guard, reset_asserted):
    name = reset_asserted.lstrip("!")
    low = reset_asserted.startswith("!")
    for term in conjunction(expression(guard)):
        if not low and bare_name(str(term)) == name:
            return True
        if low and str(term.kind) == "SyntaxKind.UnaryLogicalNotExpression" and bare_name(str(term.operand)) == name:
            return True
        if str(term.kind) in {"SyntaxKind.EqualityExpression", "SyntaxKind.CaseEqualityExpression", "SyntaxKind.WildcardEqualityExpression"}:
            for signal, value in ((term.left,term.right),(term.right,term.left)):
                if bare_name(str(signal)) == name and literal(compact(unparen(value))) == (0 if low else 1):
                    return True
    return False


def indexed_access(rhs):
    """Return (bank, dynamic address, selected-arm guard), never infer x0 intent."""
    ast = unparen(expression(rhs))
    guard = ""
    match = re.fullmatch(r"([A-Za-z_][\w$]*)\[([A-Za-z_][\w$]*)\]", compact(ast))
    if match:
        return match[1], match[2], guard
    if ast is not None and str(ast.kind) == "SyntaxKind.ConditionalExpression":
        for selected, other, negate in ((ast.left,ast.right,False),(ast.right,ast.left,True)):
            match = re.fullmatch(r"([A-Za-z_][\w$]*)\[([A-Za-z_][\w$]*)\]", compact(unparen(selected)))
            if match and literal(compact(unparen(other))) == 0:
                predicate = str(ast.predicate).strip()
                return match[1], match[2], f"!({predicate})" if negate else predicate
    return None


def constant_value(matcher, node, text=None):
    """Bounded literal expressions only; never eval RTL or overrideable parameters."""
    def value(ast, depth=0):
        ast = unparen(ast)
        if ast is None or depth > 8:
            return None
        name = compact(ast)
        result = matcher.constants[node.get("module")].get(name, literal(name))
        if result is not None:
            return result
        kind = str(ast.kind).split(".")[-1]
        if kind not in {"LogicalShiftLeftExpression", "LogicalShiftRightExpression"}:
            return None
        a, b = value(ast.left, depth+1), value(ast.right, depth+1)
        if a is None or b is None or not 0 <= b <= 1024:
            return None
        return a << b if kind == "LogicalShiftLeftExpression" else a >> b
    return value(expression(text if text is not None else node.get("rhs", "")))


def onehot_progress(m, state):
    idx = m.index
    nodes = [idx.nodes[a] for a in m.family(state)]
    name = idx.nodes[state]["name"]
    if not nodes or not same_clock(nodes):
        return "missing_complete_same_clock_family", set(), {}
    seeds, shifts = [], []
    for n in nodes:
        if n.get("lhs_expression", name) != name:
            return "partial_destination", set(), {}
        v = constant_value(m, n)
        if v is not None:
            if v < 0 or v & (v-1):
                return "non_onehot_initializer", set(), {}
            seeds.append(v)
            continue
        if bare_name(n.get("rhs")) == name:
            continue
        ast = unparen(expression(n.get("rhs", "")))
        if ast is None or str(ast.kind).split(".")[-1] not in {"LogicalShiftLeftExpression", "LogicalShiftRightExpression"}:
            return "unsupported_mask_update", set(), {}
        if bare_name(str(ast.left)) != name or state not in idx.assignment_inputs[n["id"]]:
            return "no_literal_self_shift_dependency", set(), {}
        amount = constant_value(m, n, str(ast.right))
        if amount is None or amount < 1:
            return "unknown_shift_amount", set(), {}
        shifts.append(n["id"])
    consumers = {e["target"] for e in idx.outgoing[state]["CONTROL"]
                 if e["target"] in idx.assignment_target and idx.assignment_target[e["target"]] != state}
    if not shifts or not any(seeds) or not consumers:
        return "no_initialized_progress_consumer", set(), {}
    return None, set(m.family(state)) | consumers | {state}, {
        "state": name, "initial_constants": sorted(set(seeds)), "shift_assignments": shifts,
        "encoding": "onehot_or_zero_shift_mask", "full_producer_family_checked": True,
        "unresolved_obligations": ["reset_reachability", "SPEC_iteration_meaning", "completion_bound"]}


def enabled_pipeline(m, roles):
    idx = m.index
    widths = {idx.signal_width(roles[r]) for r in ("source", "middle", "sink")}
    if len(widths) != 1 or None in widths:
        return "different_or_unknown_width", set(), {}
    family = [idx.nodes[a] for r in ("middle", "sink") for a in m.family(roles[r])]
    if not same_clock(family):
        return "different_clock_family", set(), {}
    conditional, evidence = [], set()
    for dst, src in (("middle", "source"), ("sink", "middle")):
        d, s = idx.nodes[roles[dst]]["name"], idx.nodes[roles[src]]["name"]
        for aid in m.family(roles[dst]):
            n = idx.nodes[aid]
            if n.get("lhs_expression", d) != d:
                return "partial_stage_update", set(), {}
            if bare_name(n["rhs"]) in {d, s} or constant_value(m, n) == 0:
                evidence.add(aid)
                continue
            ast = unparen(expression(n["rhs"]))
            if ast is None or str(ast.kind) != "SyntaxKind.ConditionalExpression":
                return "non_copy_stage_operation", set(), {}
            if {bare_name(str(ast.left)), bare_name(str(ast.right))} != {d, s}:
                return "not_copy_self_hold_arms", set(), {}
            if not (idx.assignment_inputs[aid] - {roles[dst], roles[src]}):
                return "missing_enable_dependency", set(), {}
            conditional.append(aid)
            evidence.add(aid)
    if not conditional:
        return "use_existing_unconditional_copy_pattern", set(), {}
    return None, evidence, {"conditional_assignments": conditional,
        "encoding": "two_clocked_copy_hold_stages", "unresolved_obligations": ["enable_alignment", "SPEC_flush_priority", "transaction_latency"]}
