"""Anchor-local, attributed directed subgraph monomorphism using VF2.

MATCH means a structural certificate exists, not that an ISA/protocol or SVA
has been proved. Unsupported encodings are omitted rather than scored up.
No LLM, training, DUT names, confidence threshold, or weighted classification.
"""
from __future__ import annotations

from collections import Counter, defaultdict
from functools import lru_cache
import hashlib
import re
import time

import networkx as nx
import pyslang

from dateassertion.rtl_frontend.graph_motif_library import LIBRARY_VERSION, MOTIFS
from dateassertion.rtl_frontend.graph_patterns import ALL_PATTERNS, TypedGraphIndex


def compact(value):
    return re.sub(r"\s+", "", str(value or ""))


@lru_cache(maxsize=32768)
def _parse_expression(text):
    tree = pyslang.syntax.SyntaxTree.fromText(f"module __m; wire __v = ({text}); endmodule")
    if len(tree.diagnostics):
        return tree, None
    found = []
    tree.root.visit(lambda n: found.append(n.expr) if str(n.kind) == "SyntaxKind.EqualsValueClause" else None)
    return tree, found[0] if found else None


def expression(text):
    # pyslang syntax nodes borrow their arena; retain the tree in the cache.
    return _parse_expression(text)[1]


def unparen(node):
    while node is not None and str(node.kind) == "SyntaxKind.ParenthesizedExpression":
        node = node.expression
    return node


def literal(text):
    value = compact(text).lower().replace("_", "")
    if re.fullmatch(r"[0-9]+", value):
        return int(value)
    if value in {"'0", "'1"}:
        return int(value[-1])
    match = re.fullmatch(r"(?:[0-9]+)?'s?([bodh])([0-9a-f]+)", value)
    if match:
        try:
            return int(match[2], {"b": 2, "o": 8, "d": 10, "h": 16}[match[1]])
        except ValueError:
            pass
    return None


def conjunction(node):
    node = unparen(node)
    if node is None:
        return []
    if str(node.kind) == "SyntaxKind.LogicalAndExpression":
        return conjunction(node.left) + conjunction(node.right)
    return [node]


def base_name(node):
    text = compact(unparen(node))
    # Slices are selector identities, not a name-based functional heuristic.
    match = re.fullmatch(r"([A-Za-z_][A-Za-z0-9_$]*)(?:\[[^\]]+\])?", text)
    return match[1] if match else None


def bare_name(text):
    value = compact(unparen(expression(str(text))))
    return value if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", value) else None


def positive_equalities(text, constants=None):
    result = []
    for node in conjunction(expression(str(text))):
        if str(node.kind) not in {"SyntaxKind.EqualityExpression", "SyntaxKind.CaseEqualityExpression",
                                  "SyntaxKind.WildcardEqualityExpression"}:
            continue
        for selector, value in ((node.left, node.right), (node.right, node.left)):
            if base_name(selector) and (literal(str(unparen(value))) is not None or
                                       compact(unparen(value)) in (constants or {})):
                result.append((base_name(selector), compact(selector), compact(value)))
    return result


def positive_bit(text, name):
    for node in conjunction(expression(str(text))):
        if compact(unparen(node)) == name:
            return True
        if str(node.kind) in {"SyntaxKind.EqualityExpression", "SyntaxKind.CaseEqualityExpression"}:
            if (compact(node.left) == name and literal(str(node.right)) == 1 or
                    compact(node.right) == name and literal(str(node.left)) == 1):
                return True
    return False


def clock_event(node):
    # Older saved graphs omit event polarity: do NOT guess posedge.
    event, clock = node.get("event_control"), node.get("clock")
    if not event or not clock:
        return None
    match = re.search(r"\b(posedge|negedge)\s+" + re.escape(clock) + r"\b", event)
    return (clock, match[1]) if match else None


def same_clock(nodes):
    events = {clock_event(node) for node in nodes}
    return len(events) == 1 and None not in events


class Matcher:
    def __init__(self, graph, feature_mode="full"):
        self.feature_mode = feature_mode
        self.index = TypedGraphIndex(graph)
        self.node_order = {node_id: i for i, node_id in enumerate(self.index.nodes)}
        self.node_at = {i: node_id for node_id, i in self.node_order.items()}
        self.attrs = {}
        self.rejections = Counter()
        self.searches = 0
        self.extensions = None
        self.alu_evidence = lru_cache(maxsize=None)(self.alu_evidence)
        self.names = {(n.get("module"), n.get("name")): key for key, n in self.index.nodes.items()
                      if n.get("kind") == "signal"}
        self.constants = defaultdict(dict)
        for n in self.index.nodes.values():
            if n.get("signal_kind") == "localparam" and n.get("constant_expression"):
                value = literal(n["constant_expression"])
                if value is not None:
                    self.constants[n["module"]][n["name"]] = value
        transforms = {"AddExpression", "SubtractExpression", "MultiplyExpression", "DivideExpression",
                      "ModExpression", "BinaryAndExpression", "BinaryOrExpression", "BinaryXorExpression",
                      "LogicalShiftLeftExpression", "LogicalShiftRightExpression",
                      "ArithmeticShiftLeftExpression", "ArithmeticShiftRightExpression",
                      "UnaryMinusExpression", "UnaryBitwiseNotExpression"}
        for key, node in self.index.nodes.items():
            attr = {"kind": node.get("kind"), "anchor": False}
            if node.get("kind") == "signal":
                width = self.index.signal_width(key)
                attr.update(bit=width == 1, wide=width is not None and width > 1,
                            output=node.get("direction") == "output",
                            array=str(node.get("signal_kind", "")).endswith("_array"))
            elif node.get("kind") == "assignment":
                from dateassertion.rtl_frontend.invariant_patterns import indexed_access
                rhs = str(node.get("rhs", ""))
                ast = unparen(expression(rhs))
                kinds = []
                if ast is not None:
                    ast.visit(lambda n: kinds.append(str(n.kind).split(".")[-1]))
                value = self.constant_value(node)
                root = str(ast.kind).split(".")[-1] if ast is not None else ""
                attr.update(zero=value == 0, one=value == 1, constant=value is not None,
                            sequential=node.get("timing") == "next_cycle" and clock_event(node) is not None,
                            copy=bare_name(rhs) is not None,
                            equality_guard=bool(self.equalities(node.get("guard", ""), node)),
                            equality_rhs=bool(self.equalities(rhs, node)),
                            transform=bool(set(kinds) & transforms),
                            shift=root in {"LogicalShiftLeftExpression", "LogicalShiftRightExpression",
                                           "ArithmeticShiftLeftExpression", "ArithmeticShiftRightExpression"},
                            compare=root in {"EqualityExpression", "CaseEqualityExpression", "InequalityExpression",
                                             "LessThanExpression", "LessThanEqualExpression", "GreaterThanExpression",
                                             "GreaterThanEqualExpression"},
                            multiply=root == "MultiplyExpression", divide=root in {"DivideExpression", "ModExpression"},
                            mux=root == "ConditionalExpression",
                            indexed_read=bool(re.fullmatch(r"[A-Za-z_][\w$]*\[[A-Za-z_][\w$]*\]", compact(rhs))),
                            gated_indexed_read=bool((access := indexed_access(rhs)) and access[2]),
                            addsub=root in {"AddExpression", "SubtractExpression"},
                            selection=root == "ConditionalExpression" or self.masked_selection(ast))
            self.attrs[key] = attr

    def family(self, target):
        return self.index.assignments_by_target.get(target, [])

    def constant_value(self, node):
        text = compact(unparen(expression(str(node.get("rhs", "")))))
        return self.constants[node.get("module")].get(text, literal(text))

    def equalities(self, text, node):
        return positive_equalities(text, self.constants[node.get("module")])

    @staticmethod
    def masked_selection(ast):
        """Recognize OR of at least two replicated-control AND data terms."""
        ast = unparen(ast)
        if ast is None or str(ast.kind) != "SyntaxKind.BinaryOrExpression":
            return False
        def terms(n):
            n = unparen(n)
            return terms(n.left) + terms(n.right) if str(n.kind) == "SyntaxKind.BinaryOrExpression" else [n]
        return all(str(n.kind) == "SyntaxKind.BinaryAndExpression" and any(
            str(unparen(side).kind) == "SyntaxKind.MultipleConcatenationExpression"
            for side in (n.left, n.right)) for n in terms(ast))

    def recurrence(self, node, state, dynamic):
        ast = unparen(expression(node.get("rhs", "")))
        if ast is None or str(ast.kind) not in {"SyntaxKind.AddExpression", "SyntaxKind.SubtractExpression"}:
            return False
        other = None
        if bare_name(str(ast.left)) == state:
            other = ast.right
        elif str(ast.kind) == "SyntaxKind.AddExpression" and bare_name(str(ast.right)) == state:
            other = ast.left
        if other is None:
            return False
        value = self.constants[node.get("module")].get(compact(other), literal(str(other)))
        if not dynamic:
            return value is not None and value != 0
        source = bare_name(str(other))
        return value is None and source is not None and source != state

    def alu_evidence(self, assignment_id):
        """Compose arithmetic + logic/shift through actual DATA producer edges.

        Follow selected data arms, never conditions/replicated control masks.
        Stop at state, module boundary, cycles and six producer hops. The
        bound is a documented encoding limit, not a match-count truncation.
        """
        idx = self.index
        evidence, categories = set(), set()
        root = idx.nodes[assignment_id]
        def visit(node, owner, depth, seen):
            node = unparen(node)
            if node is None:
                return
            kind = str(node.kind).split(".")[-1]
            if kind == "ConditionalExpression":
                visit(node.left, owner, depth, seen)
                visit(node.right, owner, depth, seen)
                return
            if kind == "BinaryAndExpression":
                left, right = unparen(node.left), unparen(node.right)
                if str(left.kind) == "SyntaxKind.MultipleConcatenationExpression":
                    visit(right, owner, depth, seen)
                    return
                if str(right.kind) == "SyntaxKind.MultipleConcatenationExpression":
                    visit(left, owner, depth, seen)
                    return
            # OR joins masked branches; it is selection logic, not an ALU op.
            join = self.masked_selection(node)
            if kind in {"AddExpression", "SubtractExpression"}:
                categories.add("arithmetic")
                return
            if kind in {"BinaryAndExpression", "BinaryXorExpression", "UnaryBitwiseNotExpression"} or (
                    kind == "BinaryOrExpression" and not join):
                categories.add("logic")
                return
            if "Shift" in kind:
                categories.add("shift")
                return
            # An operator's *inputs* may contain sign normalization, address
            # logic, etc. They are not additional selected ALU operations.
            # In particular a conditional signed multiply is not an ALU just
            # because its operand preparation uses subtraction / inversion.
            if kind in {"MultiplyExpression", "DivideExpression", "ModExpression"}:
                return
            source = self.names.get((root["module"], base_name(node)))
            if source and source in idx.assignment_inputs[owner] and depth < 6 and source not in seen:
                for producer in self.family(source):
                    n = idx.nodes[producer]
                    if n.get("timing") == "same_cycle":
                        evidence.update((source, producer))
                        visit(expression(n.get("rhs", "")), producer, depth + 1, seen | {source})
                return
            for attribute in ("left", "right", "operand"):
                child = getattr(node, attribute, None)
                if child is not None:
                    visit(child, owner, depth, seen)
        visit(expression(root.get("rhs", "")), assignment_id, 0, set())
        return categories, evidence

    def local_host(self, anchor, kind):
        idx = self.index
        assignments = set(self.family(anchor))
        if kind in {"PIPELINE", "FSM", "ITERATIVE_MULTIPLIER", "ITERATIVE_DIVIDER"}:
            for a in list(assignments):
                for source in idx.assignment_inputs[a]:
                    assignments.update(self.family(source))
        elif kind == "HANDSHAKE":
            assignments.update(idx.controls(anchor))
        elif kind == "REGISTER_FILE":
            assignments.update(e["target"] for e in idx.outgoing[anchor]["DATA"]
                               if e["target"] in idx.assignment_target)
        nodes = {anchor} | assignments
        for a in assignments:
            nodes.update(idx.assignment_inputs[a] | idx.assignment_controls[a])
            if a in idx.assignment_target:
                nodes.add(idx.assignment_target[a])
        module = idx.nodes[anchor].get("module")
        nodes = {n for n in nodes if idx.nodes.get(n, {}).get("module") == module}
        host = nx.DiGraph()
        for n in sorted(nodes):
            host.add_node(n, **{**self.attrs[n], "anchor": n == anchor})
        for n in sorted(nodes):
            for typ, edges in idx.outgoing[n].items():
                for edge in edges:
                    target = edge["target"]
                    if target not in nodes:
                        continue
                    if not host.has_edge(n, target):
                        host.add_edge(n, target, types=set())
                    host[n][target]["types"].add(typ)
        return host

    def predicates(self, motif, roles):
        if motif.get("extension"):
            if self.extensions is None:
                from dateassertion.rtl_frontend.composite_motifs import CompositeMotifs
                self.extensions = CompositeMotifs(self)
            return self.extensions.verify(motif, roles)
        idx = self.index
        nodes = {role: idx.nodes[key] for role, key in roles.items()}
        kind = motif["kind"]
        name = lambda role: nodes[role].get("name")
        family = lambda role: [idx.nodes[a] for a in self.family(roles[role])]
        rhs_value = self.constant_value
        if kind in {"COUNTER", "ACCUMULATOR"}:
            producers = family("state")
            dynamic = kind == "ACCUMULATOR"
            if not same_clock(producers):
                return "different_or_unknown_clock"
            if not self.recurrence(nodes["update"], name("state"), dynamic):
                return "not_supported_recurrence"
            if any(rhs_value(n) is None and bare_name(n.get("rhs")) != name("state") and
                   not self.recurrence(n, name("state"), dynamic) for n in producers):
                return "mixed_recurrence_family"
        if kind == "ALU":
            categories, _ = self.alu_evidence(roles["select"])
            if nodes["select"].get("timing") != "same_cycle":
                return "not_combinational_selection"
            if "arithmetic" not in categories or not categories & {"logic", "shift"}:
                return "missing_selected_arithmetic_and_logic"
        if motif["id"] == "decode_boolean_equation":
            node = nodes["compare"]
            if not any(eq[0] == name("selector") for eq in self.equalities(node.get("rhs", ""), node)):
                return "selector_not_compared_to_constant"
            if len(self.family(roles["result"])) != 1:
                return "not_single_producer"
            if roles["result"] in idx.assignment_inputs[roles["compare"]] | idx.assignment_controls[roles["compare"]]:
                return "state_feedback_not_decode"
            return None
        if motif["id"] == "split_next_state_feedback":
            if bare_name(nodes["register"].get("rhs")) != name("next"):
                return "not_exact_next_state_copy"
            if rhs_value(nodes["transition"]) == rhs_value(nodes["alternative"]):
                return "no_distinct_next_values"
            if not same_clock(family("state")):
                return "different_or_unknown_clock"
            if any(rhs_value(n) is None and bare_name(n.get("rhs")) not in {name("state"), name("next")}
                   for n in family("state")):
                return "other_state_producer"
            if any(n.get("timing") != "same_cycle" or
                   rhs_value(n) is None and bare_name(n.get("rhs")) != name("state")
                   for n in family("next")):
                return "non_constant_next_state_family"
            node = nodes["transition"]
            if not any(eq[0] == name("state") for eq in self.equalities(node.get("guard", ""), node)):
                return "no_explicit_state_condition"
            return None
        if kind == "DECODE":
            default, branch = nodes["default"], nodes["branch"]
            if not any(eq[0] == name("selector") for eq in self.equalities(branch.get("guard", ""), branch)):
                return "selector_not_compared_to_constant"
            if not default.get("process_id") or default.get("process_id") != branch.get("process_id"):
                return "missing_or_different_process"
            if default.get("source_order", default.get("source", {}).get("line", 0)) >= branch.get("source_order", branch.get("source", {}).get("line", 0)):
                return "default_order_not_established"
            dguard = {compact(n) for n in conjunction(expression(default.get("guard", "")))
                      if literal(str(n)) != 1}
            bguard = {compact(n) for n in conjunction(expression(branch.get("guard", "")))}
            if not dguard <= bguard:
                return "default_not_in_override_context"
            if any(rhs_value(n) not in {0, 1} for n in family("result")):
                return "non_boolean_producer"
            if any(roles["result"] in idx.assignment_inputs[a] | idx.assignment_controls[a]
                   for a in self.family(roles["result"])):
                return "state_feedback_not_decode"
        elif kind == "FSM":
            if rhs_value(nodes["transition"]) == rhs_value(nodes["alternative"]):
                return "no_distinct_next_values"
            producers = family("state")
            if not same_clock(producers):
                return "different_or_unknown_clock"
            if any(rhs_value(n) is None and bare_name(n.get("rhs")) != name("state") for n in producers):
                return "arithmetic_or_dynamic_next_value"
            guard = nodes["transition"].get("guard", "")
            if not (any(eq[0] == name("state") for eq in self.equalities(guard, nodes["transition"])) or
                    self.attrs[roles["state"]].get("bit") and positive_bit(guard, name("state"))):
                return "no_explicit_state_condition"
        elif kind == "PIPELINE":
            if any(bare_name(nodes[a].get("rhs")) != name(s) for a, s in (("first", "source"), ("second", "middle"))):
                return "not_exact_copy"
            widths = {idx.signal_width(roles[r]) for r in ("source", "middle", "sink")}
            if len(widths) != 1 or None in widths:
                return "different_or_unknown_width"
            producers = family("middle") + family("sink")
            if not same_clock(producers):
                return "different_or_unknown_clock"
            for target, source in (("middle", "source"), ("sink", "middle")):
                for n in family(target):
                    if rhs_value(n) is None and bare_name(n.get("rhs")) not in {name(target), name(source)}:
                        return "non_copy_producer"
            if roles["source"] in idx.sequential_successors(roles["middle"]) | idx.sequential_successors(roles["sink"]):
                return "local_feedback_not_pipeline"
        elif kind == "HANDSHAKE":
            if not positive_bit(nodes["set"].get("guard", ""), name("request")):
                return "request_not_positive_condition"
            if not all(positive_bit(nodes[r].get("guard", ""), name("active")) for r in ("clear", "respond")):
                return "active_not_positive_condition"
            if compact(nodes["clear"].get("guard")) != compact(nodes["respond"].get("guard")):
                return "completion_contexts_differ"
            if not same_clock([nodes[r] for r in ("set", "clear", "respond")]):
                return "different_or_unknown_clock"
            if any(rhs_value(n) not in {0, 1} for n in family("active")):
                return "non_boolean_active_family"
        return None

    def find(self, motif, anchor):
        required = nx.DiGraph()
        for role, attrs in motif["nodes"].items():
            required.add_node(role, **attrs)
        for source, target, typ in motif["edges"]:
            if not required.has_edge(source, target):
                required.add_edge(source, target, types=set())
            required[source][target]["types"].add(typ)
        host = self.local_host(anchor, motif["kind"])
        node_match = lambda actual, wanted: all(actual.get(k) == v for k, v in wanted.items()
            if self.feature_mode == "full" or k in {"kind", "anchor"})
        if not node_match(host.nodes[anchor], required.nodes[motif["anchor"]]):
            return None
        # Cheap necessary attribute-count test; never replaces VF2 confirmation.
        if any(not any(node_match(a, wanted) for _, a in host.nodes(data=True))
               for _, wanted in required.nodes(data=True)):
            return None
        self.searches += 1
        # VF2 uses sets internally. Stable integer handles prevent Python string
        # hash randomization or signal renaming from changing witness choice.
        stable_host = nx.DiGraph()
        for node in sorted(host, key=self.node_order.__getitem__):
            stable_host.add_node(self.node_order[node], **host.nodes[node])
        for source, target, attrs in host.edges(data=True):
            stable_host.add_edge(self.node_order[source], self.node_order[target], **attrs)
        matcher = nx.algorithms.isomorphism.DiGraphMatcher(
            stable_host, required, node_match=node_match,
            edge_match=lambda actual, wanted: wanted["types"] <= actual["types"])
        for mapping in matcher.subgraph_monomorphisms_iter():
            roles = {role: self.node_at[node] for node, role in mapping.items()}
            rejection = self.predicates(motif, roles) if self.feature_mode == "full" else None
            if rejection:
                self.rejections[f"{motif['id']}:{rejection}"] += 1
                continue
            return self.candidate(motif, roles)
        return None

    def candidate(self, motif, roles):
        idx = self.index
        anchor = roles[motif["anchor"]]
        module = idx.nodes[anchor]["module"]
        core = set(roles.values())
        composed = set()
        detail = {}
        if motif.get("extension") and self.feature_mode == "full":
            composed, detail = self.extensions.witnesses[self.extensions.key(motif, roles)]
            composed = set(composed)
            core.update(composed)
        elif motif["kind"] == "ALU" and self.feature_mode == "full":
            _, composed = self.alu_evidence(roles["select"])
            core.update(composed)
        # Preserve complete producer families for every written witness signal.
        targets = {idx.assignment_target[a] for a in core if a in idx.assignment_target}
        for target in targets:
            for a in self.family(target):
                core.add(a)
                core.update(idx.assignment_inputs[a] | idx.assignment_controls[a])
        edges = []
        for source, target, typ in motif["edges"]:
            edges.append(next(e for e in idx.outgoing[roles[source]][typ] if e["target"] == roles[target]))
        certificate = {"library_version": LIBRARY_VERSION, "motif_id": motif["id"],
                       "algorithm": ("VF2_seed_with_verified_dependency_composition"
                                     if motif.get("extension") and self.feature_mode == "full"
                                     else "VF2_directed_subgraph_monomorphism"), "roles": roles,
                       "required_edges": edges,
                       "feature_mode": self.feature_mode,
                       "composition_details": detail,
                       "scope_limitations": motif.get("limitation"),
                       "composed_node_ids": sorted(composed),
                       "composed_edges": [e for e in idx.graph["edges"]
                                          if e["source"] in composed | set(roles.values())
                                          and e["target"] in composed | set(roles.values())] if composed else [],
                       "satisfied_predicates": motif["predicates"] if self.feature_mode == "full" else [],
                       "source_evidence": {r: idx.nodes[n].get("source") for r, n in roles.items()},
                       "semantic_status": "STRUCTURAL_MATCH_NOT_SPEC_PROOF" if self.feature_mode == "full"
                                          else "TOPOLOGY_ONLY_ABLATION_NOT_FUNCTION_CLASSIFICATION"}
        digest = hashlib.sha1(f"{motif['id']}:{anchor}".encode()).hexdigest()[:12]
        return {"candidate_id": f"motif_{motif['id']}_{digest}", "kind": motif["kind"],
                "module": module, "anchor_nodes": [anchor], "anchor_signals": [idx.nodes[anchor]["name"]],
                "core_node_ids": sorted(core), "detection_status": "MATCH",
                # Compatibility only: all zero, never a classification confidence.
                "score": 0.0, "pattern_scores": {k: 0.0 for k in ALL_PATTERNS},
                "score_semantics": "UNUSED_LEGACY_SCHEMA_FIELD",
                "matched_features": [{"feature": p, "satisfied": True} for p in motif["predicates"]]
                                    if self.feature_mode == "full" else [],
                "decision_basis": ("attributed_seed_and_dependency_composition" if motif.get("extension")
                                   else "attributed_directed_subgraph_monomorphism") if self.feature_mode == "full"
                                  else "typed_topology_only_ablation",
                "match_certificate": certificate}


def match_graph_motifs(graph, *, max_candidates_per_kind=None, feature_mode="full"):
    if feature_mode not in {"full", "topology"}:
        raise ValueError("invalid feature mode")
    if max_candidates_per_kind is not None and max_candidates_per_kind < 1:
        raise ValueError("max_candidates_per_kind must be positive")
    started = time.perf_counter()
    matcher = Matcher(graph, feature_mode)
    raw = []
    for motif in MOTIFS:
        for anchor in sorted(matcher.index.assignments_by_target):
            candidate = matcher.find(motif, anchor)
            if candidate:
                raw.append(candidate)
    groups = defaultdict(list)
    for item in raw:
        groups[item["kind"], item["module"]].append(item)
    # Source order, not a confidence ranking; caps are explicit resource policy.
    def source_order(item):
        n = matcher.index.nodes[item["anchor_nodes"][0]]
        return (n.get("source", {}).get("file", ""), n.get("source", {}).get("line", 0), item["candidate_id"])
    selected = [p for key in sorted(groups) for p in sorted(groups[key], key=source_order)[:max_candidates_per_kind]]
    return {"schema": "microarchitecture-graph-patterns.v2", "method": "attributed_directed_subgraph_monomorphism_vf2",
            "library_version": LIBRARY_VERSION, "signal_names_used_for_scoring": False,
            "feature_mode": feature_mode,
            "weighted_scores_used": False, "max_candidates_per_kind_per_module": max_candidates_per_kind,
            "edge_semantics": {"types": ["DATA", "CONTROL", "SEQUENTIAL"], "direction_preserved": True},
            "patterns": selected,
            "summary": {"candidate_count": len(selected), "before_cap": len(raw), "truncated": len(raw)-len(selected),
                        "by_kind": {k: sum(p["kind"] == k for p in selected) for k in ALL_PATTERNS},
                        "by_status": {"MATCH": len(selected), "AMBIGUOUS": 0},
                        "vf2_searches": matcher.searches, "predicate_rejections": dict(matcher.rejections),
                        "elapsed_seconds": time.perf_counter()-started},
            "limitations": ["Not complete for arbitrary equivalent RTL encodings",
                            "No SPEC or protocol correctness claim from a motif",
                            "Clocked motifs require explicit event metadata; reparse older saved graphs",
                            "No cross-module port flattening; existing cross-region edges are retained"]}
