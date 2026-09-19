"""Verified joins of RTL producer families, never names or weighted scores.

Each recognizer closes a VF2 seed using actual typed edges and records which
part of a larger microarchitecture remains a SPEC / observation obligation.
"""
from functools import lru_cache
import re

from dateassertion.rtl_frontend.graph_motif_matching import (
    expression, unparen, compact, literal, bare_name, base_name, conjunction, same_clock, clock_event)


def kind(ast):
    ast = unparen(ast)
    return str(ast.kind).split(".")[-1] if ast is not None else ""


def indexed(text):
    return re.fullmatch(r"([A-Za-z_][\w$]*)\[([A-Za-z_][\w$]*)\]", compact(text))


class CompositeMotifs:
    def __init__(self, matcher):
        self.m = matcher
        self.idx = matcher.index
        self.by_module = {}
        for a in self.idx.assignment_target:
            self.by_module.setdefault(self.idx.nodes[a]["module"], []).append(a)
        self.witnesses = {}
        self.decode_family = lru_cache(maxsize=None)(self.decode_family)

    def key(self, motif, roles):
        return motif["id"], tuple(sorted(roles.items()))

    def verify(self, motif, roles):
        failure, nodes, detail = getattr(self, motif["extension"])(motif, roles)
        if failure is None:
            # Keep the actual inputs and control witnesses of every joined
            # assignment in the certificate, not just the destination nodes.
            for aid in set(nodes) | set(roles.values()):
                if aid in self.idx.assignment_target:
                    nodes |= self.idx.assignment_inputs[aid] | self.idx.assignment_controls[aid]
                    nodes.add(self.idx.assignment_target[aid])
            self.witnesses[self.key(motif, roles)] = (nodes, detail)
        return failure

    def equations(self, signal):
        return [self.idx.nodes[a] for a in self.m.family(signal)]

    def encoded(self, text, owner, dependency_type="DATA"):
        dependencies = (self.idx.assignment_controls if dependency_type == "CONTROL" else self.idx.assignment_inputs)[owner["id"]]
        return [(base, field, value) for base, field, value in self.m.equalities(text, owner)
                if self.m.names.get((owner["module"], base)) in dependencies
                and (self.idx.signal_width(self.m.names.get((owner["module"], base), "")) or 0) > 1]

    def decode_family(self, target, seen=(), depth=0):
        if depth > 8 or target in seen or not self.m.attrs.get(target, {}).get("bit"):
            return False, frozenset()
        producers = self.m.family(target)
        if not producers:
            return False, frozenset()
        family = self.equations(target)
        if len(family) > 1 and (None in {n.get("process_id") for n in family} or
                               len({n.get("process_id") for n in family}) != 1):
            return False, frozenset()
        if any(n.get("timing") == "next_cycle" for n in family) and not same_clock(family):
            return False, frozenset()
        evidence, supported = {target}, False
        for a in producers:
            node = self.idx.nodes[a]
            if target in self.idx.assignment_inputs[a] | self.idx.assignment_controls[a]:
                return False, frozenset()
            value = self.m.constant_value(node)
            if value == 0:
                evidence.add(a)
                continue
            if value == 1:
                if not self.encoded(node.get("guard", ""), node, "CONTROL"):
                    return False, frozenset()
                support, extra = True, set()
            else:
                support, extra = self.decode_expression(expression(node.get("rhs", "")), node,
                                                         seen + (target,), depth)
            if not support:
                return False, frozenset()
            supported = True
            evidence.update({a} | set(extra) | self.idx.assignment_inputs[a] | self.idx.assignment_controls[a])
        return supported, frozenset(evidence)

    def decode_expression(self, ast, owner, seen, depth):
        ast = unparen(ast)
        typ = kind(ast)
        if typ in {"EqualityExpression", "CaseEqualityExpression", "WildcardEqualityExpression"}:
            return bool(self.encoded(str(ast), owner)), set()
        if typ in {"LogicalAndExpression", "BinaryAndExpression", "LogicalOrExpression", "BinaryOrExpression"}:
            left, a = self.decode_expression(ast.left, owner, seen, depth)
            right, b = self.decode_expression(ast.right, owner, seen, depth)
            ok = (left or right) if "And" in typ else (left and right)
            return ok, set(a) | set(b)
        if typ == "UnaryBitwiseOrExpression" and kind(ast.operand) == "ConcatenationExpression":
            children = [self.decode_expression(n, owner, seen, depth) for n in unparen(ast.operand).expressions
                        if str(n.kind) != "TokenKind.Comma"]
            return bool(children) and all(c[0] for c in children), set().union(*(set(c[1]) for c in children))
        name = bare_name(str(ast)) if ast is not None else None
        source = self.m.names.get((owner["module"], name))
        if source and source in self.idx.assignment_inputs[owner["id"]]:
            return self.decode_family(source, seen, depth + 1)
        return False, set()

    def decode(self, motif, roles):
        ok, extra = self.decode_family(roles["result"])
        # Provenance is not functional identity. At a register boundary a
        # single already-decoded Boolean (possibly gated) is history, not a
        # fresh decode. Accept a local field decision or a combination of at
        # least two decoded terms. This is conservative and name-independent.
        for owner in self.equations(roles["result"]):
            if owner.get("timing") != "next_cycle" or self.m.constant_value(owner) in {0, 1}:
                continue
            local_decision = []
            ast = expression(owner.get("rhs", ""))
            if ast is not None:
                ast.visit(lambda n: local_decision.extend(self.encoded(str(unparen(n)), owner))
                          if kind(n) in {"EqualityExpression", "WildcardEqualityExpression", "CaseEqualityExpression"} else None)
            decoded_inputs = {s for s in self.idx.assignment_inputs[owner["id"]]
                              if s != roles["result"] and self.decode_family(s)[0]}
            if not local_decision and len(decoded_inputs) < 2:
                ok = False
        selectors = set()
        for a in extra:
            if a in self.idx.assignment_target:
                n = self.idx.nodes[a]
                selectors.update(eq[0] for eq in self.encoded(n.get("rhs", ""), n))
                selectors.update(eq[0] for eq in self.encoded(n.get("guard", ""), n, "CONTROL"))
        return (None if ok else "unsupported_boolean_producer_family", set(extra),
                {"encoding": "composed_boolean_decode", "max_producer_hops": 8,
                 "selector_signals": sorted(selectors)})

    def onehot_progress(self, motif, roles):
        from dateassertion.rtl_frontend.invariant_patterns import onehot_progress
        return onehot_progress(self.m, roles["state"])

    def enabled_pipeline(self, motif, roles):
        from dateassertion.rtl_frontend.invariant_patterns import enabled_pipeline
        return enabled_pipeline(self.m, roles)

    def distinct_contexts(self, a, b):
        return [(x, y) for x in self.encoded(a.get("guard", ""), a, "CONTROL")
                for y in self.encoded(b.get("guard", ""), b, "CONTROL")
                if x[1] == y[1] and x[2] != y[2]]

    def case_alu(self, motif, roles):
        a, b = (self.idx.nodes[roles[r]] for r in ("first", "second"))
        if not a.get("process_id") or a.get("process_id") != b.get("process_id") or any(
                n.get("timing") != "same_cycle" for n in (a, b)):
            return "not_same_combinational_process", set(), {}
        if not self.distinct_contexts(a, b):
            return "no_distinct_encoded_operation_guards", set(), {}
        ca, ea = self.m.alu_evidence(a["id"])
        cb, eb = self.m.alu_evidence(b["id"])
        if not (("arithmetic" in ca and cb & {"logic", "shift"}) or
                ("arithmetic" in cb and ca & {"logic", "shift"})):
            return "missing_distinct_selected_operations", set(), {}
        return None, ea | eb, {"operation_guards": [a["guard"], b["guard"]],
                                "encoding": "guarded_operation_family"}

    def register_file(self, motif, roles):
        bank = self.idx.nodes[roles["bank"]]
        write = self.idx.nodes[roles["write"]]
        dest = indexed(write.get("lhs_expression", ""))
        if not dest or dest[1] != bank["name"]:
            return "missing_dynamic_write_index", set(), {}
        address = self.m.names.get((bank["module"], dest[2]))
        if not address or not any(e.get("dependency_role") == "write_index" and e["source"] == address
                                  for e in self.idx.incoming[write["id"]]["CONTROL"]):
            return "missing_write_index_edge", set(), {}
        if self.idx.nodes[address].get("direction") == "constant":
            return "write_index_not_dynamic", set(), {}
        addresses = []
        for role in ("read_a", "read_b"):
            node = self.idx.nodes[roles[role]]
            src = indexed(node.get("rhs", ""))
            if motif.get("gated_reads"):
                from dateassertion.rtl_frontend.invariant_patterns import indexed_access
                access = indexed_access(node.get("rhs", ""))
                src = (None,access[0],access[1]) if access and access[2] else None
            if node.get("timing") != "same_cycle" or not src or src[1] != bank["name"]:
                return "not_combinational_indexed_read", set(), {}
            source_id = self.m.names.get((bank["module"], src[2]))
            if not source_id or source_id not in self.idx.assignment_inputs[node["id"]]:
                return "missing_read_index_data_edge", set(), {}
            addresses.append(source_id)
        if addresses[0] == addresses[1]:
            return "same_read_address_not_two_ports", set(), {}
        return None, {address, *addresses}, {
            "storage": bank["name"], "write_address": dest[2], "write_data": write["rhs"],
            "write_guard": write["guard"], "read_addresses": [self.idx.nodes[a]["name"] for a in addresses],
            "unresolved_obligations": ["x0_policy", "read_write_collision_priority", "symbolic_address_observer"],
            "encoding": "indexed_clocked_multi_read_bank"}

    def output_paths(self, source, depth=0, seen=()):
        if source in seen or depth > 2:
            return []
        if self.idx.nodes[source].get("direction") == "output":
            return [(source, set())]
        paths = []
        for e in self.idx.outgoing[source]["DATA"]:
            a = e["target"]
            if a not in self.idx.assignment_target or self.idx.nodes[a].get("timing") != "same_cycle":
                continue
            target = self.idx.assignment_target[a]
            for output, nodes in self.output_paths(target, depth + 1, seen + (source,)):
                paths.append((output, nodes | {a, target, source}))
        return paths

    def lsu(self, motif, roles):
        idx, m = self.idx, self.m
        address = roles["address"]
        addr_paths = self.output_paths(address)
        if not addr_paths:
            return "address_does_not_reach_output", set(), {}
        module = idx.nodes[address]["module"]
        # Source-level byte/half-word transformations: require shared raw
        # input data, two differently selected operations, and address guards.
        loads, stores = [], []
        for a in self.by_module[module]:
            n = idx.nodes[a]
            if n.get("timing") != "same_cycle" or kind(expression(n.get("rhs", ""))) != "ConcatenationExpression":
                continue
            if not self.encoded(n.get("guard", ""), n, "CONTROL"):
                continue
            inputs = {s for s in idx.assignment_inputs[a] if idx.nodes[s].get("direction") == "input"
                      and re.search(r"\b" + re.escape(idx.nodes[s]["name"]) + r"\s*\[\s*\d+\s*:\s*\d+\s*\]", n["rhs"])}
            if len(inputs) == 1 and self.output_paths(idx.assignment_target[a]):
                loads.append((a, inputs))
            if len(inputs) >= 2 and idx.nodes[idx.assignment_target[a]].get("direction") == "output":
                stores.append((a, inputs))
        def terms(n):
            return {compact(x) for x in conjunction(expression(n.get("guard", ""))) if literal(str(x)) != 1}
        for la, li in loads:
            for sa, si in stores:
                ln, sn = idx.nodes[la], idx.nodes[sa]
                if not li <= si or not self.distinct_contexts(ln, sn):
                    continue
                address_witness = set()
                for node in (ln, sn):
                    matching = [(out, path) for out, path in addr_paths if any(
                        terms(idx.nodes[a]) and terms(idx.nodes[a]) <= terms(node)
                        for a in path if a in idx.assignment_target)]
                    if not matching:
                        break
                    out, path = matching[0]
                    address_witness.update(path | {out})
                else:
                    out, read_path = self.output_paths(idx.assignment_target[la])[0]
                    extra = address_witness | read_path | {la, sa, out, idx.assignment_target[la],
                                                          idx.assignment_target[sa]} | li | si
                    return None, extra, {"load_assignment": la, "store_assignment": sa,
                        "load_context": ln["guard"], "store_context": sn["guard"],
                        "encoding": "subword_read_modify_write_datapath",
                        "unresolved_obligations": ["SPEC_memory_interface_binding", "request_acceptance_and_response_events",
                                                   "alignment_exception_policy", "store_side_effects"]}
        return "no_connected_subword_load_store_contexts", set(), {}

    def self_shift(self, n):
        ast = unparen(expression(n.get("rhs", "")))
        return "Shift" in kind(ast) and bare_name(str(ast.left)) == n["lhs"] and literal(str(ast.right)) not in {None, 0}

    def zero_test(self, n, signal):
        for ast in conjunction(expression(n.get("guard", ""))):
            if kind(ast) == "UnaryLogicalNotExpression" and bare_name(str(ast.operand)) == signal:
                return True
            if any(eq[0] == signal and literal(eq[2]) == 0 for eq in self.m.equalities(str(ast), n)):
                return True
        return False

    def iterative(self, motif, roles):
        m, idx = self.m, self.idx
        arithmetic, shift = (idx.nodes[roles[r]] for r in ("arithmetic", "shift"))
        operation = "AddExpression" if motif["operation"] == "add" else "SubtractExpression"
        if kind(expression(arithmetic["rhs"])) != operation or not self.self_shift(shift) or not same_clock([arithmetic, shift]):
            return "not_connected_clocked_arithmetic_and_shift", set(), {}
        state_name = idx.nodes[roles["state"]]["name"]
        shift_name = idx.nodes[roles["shift_state"]]["name"]
        guard = arithmetic.get("guard", "")
        if motif["operation"] == "subtract":
            if not {roles["state"], roles["shift_state"]} <= idx.assignment_controls[arithmetic["id"]]:
                return "missing_comparison_control_edges", set(), {}
            comparisons = []
            ast = expression(guard)
            if ast is not None:
                ast.visit(lambda n: comparisons.append(unparen(n)) if kind(n) in {
                    "LessThanExpression", "LessThanEqualExpression", "GreaterThanExpression", "GreaterThanEqualExpression"} else None)
            if not any({base_name(n.left), base_name(n.right)} == {state_name, shift_name} for n in comparisons):
                return "no_operand_comparison_guard", set(), {}
        else:
            bit_operands = [match[1] for term in conjunction(expression(guard))
                            if (match := re.fullmatch(r"([A-Za-z_][\w$]*)\[0\]", compact(term)))]
            bit_steps = [n for name in bit_operands
                         if (sid := m.names.get((arithmetic["module"], name))) in idx.assignment_controls[arithmetic["id"]]
                         for n in self.equations(sid)
                         if self.self_shift(n) and clock_event(n) == clock_event(arithmetic)]
            if not bit_steps:
                return "no_clocked_multiplier_bit_shift", set(), {}
        initializers = [n for n in self.equations(roles["shift_state"]) if n["id"] != shift["id"]
                        and clock_event(n) == clock_event(shift)
                        and any(idx.nodes[s].get("direction") == "input" for s in idx.assignment_inputs[n["id"]])]
        if not initializers:
            return "no_operand_initialization", set(), {}
        for response_id in self.by_module[arithmetic["module"]]:
            response = idx.nodes[response_id]
            target = idx.assignment_target[response_id]
            if idx.nodes[target].get("direction") != "output" or not m.attrs[target].get("bit") or m.constant_value(response) != 1:
                continue
            if clock_event(response) != clock_event(arithmetic):
                continue
            for progress in sorted(idx.assignment_controls[response_id], key=m.node_order.__getitem__):
                if not (idx.signal_width(progress) or 0) > 1 or not self.zero_test(response, idx.nodes[progress]["name"]):
                    continue
                for update in self.equations(progress):
                    if clock_event(update) != clock_event(arithmetic):
                        continue
                    if not (self.self_shift(update) or m.recurrence(update, idx.nodes[progress]["name"], False)):
                        continue
                    # Shared actual control dependency ties progress and work
                    # to one lifecycle; a nearby independent counter is not enough.
                    controls = idx.assignment_controls[arithmetic["id"]] & idx.assignment_controls[update["id"]]
                    resets = {m.names.get((arithmetic["module"], s)) for s in arithmetic.get("reset", [])}
                    if not controls - resets:
                        continue
                    extra = {progress, update["id"], response_id, target} | {n["id"] for n in initializers}
                    if motif["operation"] != "subtract":
                        extra |= {n["id"] for n in bit_steps}
                    return None, extra, {"progress_state": idx.nodes[progress]["name"],
                        "completion_output": idx.nodes[target]["name"], "completion_guard": response["guard"],
                        "step_assignment": arithmetic["id"], "progress_assignment": update["id"],
                        "encoding": "conditional_shift_arithmetic_iteration",
                        "unresolved_obligations": ["operand_snapshot_at_acceptance", "signedness_and_overflow",
                                                   "end_to_end_arithmetic_result", "proved_iteration_bound"]}
        return "no_progress_to_completion_lifecycle", set(), {}
