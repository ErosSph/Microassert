"""Experimental Region-bound template instantiation; not the main flow."""
from collections import defaultdict
from copy import deepcopy
from dataclasses import asdict
import hashlib
import re
from dateassertion.experimental.region_templates import PACKS
from dateassertion.ontology.primitives import bind_extension_primitives, expression_signals
from dateassertion.ir.schema import ContractIR
from dateassertion.rtl_frontend.invariant_patterns import reset_guard_asserted

def guard(node):
    return node.get('guard') or "1'b1"

def is_true(expr):
    return re.sub(r'[\s()]', '', expr) in {'1', "1'b1"}

def effective_guard(node, family):
    """Last procedural write wins; only used after single-process family gate."""
    later = [guard(other) for other in family if other['source_order'] > node['source_order']]
    if any(is_true(g) for g in later):
        return "1'b0"
    return guard(node) if not later else '('+guard(node)+') && !('+' || '.join('('+g+')' for g in later)+')'

def family_rejection(family, clock, allow_comb=False, reset=None):
    if not family:
        return 'NO_PRODUCER'
    if len({n.get('process_id') for n in family}) != 1:
        return 'MULTIPLE_PROCESSES'
    if any(n.get('lhs_expression', n['lhs']) != n['lhs'] for n in family):
        return 'PARTIAL_OR_INDEXED_DESTINATION'
    timing = {n.get('timing') for n in family}
    if timing == {'next_cycle'}:
        for n in family:
            event = n.get('event_control', '')
            allowed = {'posedge '+clock}
            if reset:
                reset_name = reset.lstrip('!')
                edge = 'negedge' if reset.startswith('!') else 'posedge'
                if reset_name in n.get('reset', []):
                    allowed.add('posedge '+clock+' or '+edge+' '+reset_name)
            if n.get('clock') != clock or event not in allowed:
                return 'UNSUPPORTED_CLOCK_OR_EVENT'
    elif not allow_comb or timing != {'same_cycle'}:
        return 'NOT_SUPPORTED_TIMING'
    return ''

def generate(design, graph, patterns, clock, reset):
    from dateassertion.pipeline.architecture_contracts import compile_architecture_contracts
    nodes = {n['id']: n for n in graph['nodes']}
    families = defaultdict(list)
    for n in graph['nodes']:
        if n['kind'] == 'assignment':
            families[(n['module'], n['lhs'])].append(n)
    for family in families.values():
        family.sort(key=lambda n: n['source_order'])
    inventory, contracts, properties, audits, skipped = [], [], [], [], []
    source_rows = {}
    known = {module: set(signals) for module, signals in design.module_signals.items()}

    def emit(region, recipe, primitive, roles, evidence):
        token = hashlib.sha256(repr((region['region_id'], recipe['id'], roles, evidence)).encode()).hexdigest()[:14]
        pid = 'kb_'+token
        ev = [dict(files=[nodes[n]['source']['file']], line_start=nodes[n]['source']['line'],
                   line_end=nodes[n]['source']['line'], node_id=n) for n in evidence if n in nodes and nodes[n].get('source')]
        contract = ContractIR(contract_id='contract_'+pid, object_type=region['kind'],
            ontology_classification='NEW_OBJECT_CANDIDATE', region=region['region_id'], module=region['module'],
            invariants=[dict(primitive=primitive, roles=roles, semantics='RTL_STRUCTURAL knowledge-pack obligation, not independent SPEC correctness')],
            reused_primitives=[primitive], evidence=ev)
        contracts.append(asdict(contract))
        compiled, bindings = bind_extension_primitives([contract], known, reset)
        if not compiled:
            skipped.append(dict(region_id=region['region_id'], recipe=recipe['id'], roles=roles,
                                reason='COMPILE_REJECTED', bindings=[asdict(b) for b in bindings]))
            return None
        assert len(compiled) == 1
        prop = compiled[0]
        prop.property_id = pid
        prop.source = 'region-knowledge-pack+typed-graph+fixed-primitive'
        prop.source_classification = 'RTL_STRUCTURAL'
        prop.description = region['kind']+'/'+recipe['id']+': '+recipe['name']
        properties.append(prop)
        source_rows[pid] = dict(region_id=region['region_id'], kind=region['kind'], recipe_id=recipe['id'],
            primitive=primitive, roles=roles, evidence_node_ids=evidence, contract_id=contract.contract_id)
        return pid

    for pat in patterns['patterns']:
        kind = pat['kind']
        cert = pat['match_certificate']
        if kind not in PACKS or cert['motif_id'] not in PACKS[kind]['motifs']:
            skipped.append(dict(candidate_id=pat['candidate_id'], kind=kind, reason='NO_KNOWLEDGE_PACK'))
            continue
        region = dict(region_id='region_'+pat['candidate_id'], module=pat['module'], kind=kind,
            core_node_ids=pat['core_node_ids'], match_certificate=cert, targets=[], sva_templates=[])
        for role in PACKS[kind]['targets']:
            node = nodes.get(cert['roles'].get(role))
            if node and node['kind'] == 'signal':
                region['targets'].append(node['name'])
        # Split-state binding requires its own comb-to-clock composition, not a
        # guessed one-cycle rule on the combinational next-state signal.
        split = kind == 'FSM' and cert['roles'].get('next', cert['roles'].get('state')) != cert['roles'].get('state')
        for recipe in PACKS[kind]['recipes']:
            before = len(properties)
            row = deepcopy(recipe)
            if recipe['binder'] == 'invariant':
                extra, _, _, audit = compile_architecture_contracts(design, graph, {'regions':[region]}, reset)
                audits.extend(audit)
                for prop in extra:
                    if prop.template == recipe['primitive']:
                        emit(region, recipe, prop.template, prop.bindings, [e['node_id'] for e in prop.evidence if e.get('node_id')])
            elif split:
                skipped.append(dict(region_id=region['region_id'], recipe=recipe['id'], reason='SPLIT_NEXT_STATE_NOT_IMPLEMENTED'))
            else:
                targets = list(region['targets'])
                if recipe['binder'] == 'state_effect':
                    state_node = cert['roles'].get('state')
                    controlled = {edge['target'] for edge in graph['edges'] if edge['source'] == state_node and edge['type'] == 'CONTROL'}
                    targets = sorted({nodes[n]['lhs'] for n in controlled if nodes.get(n, {}).get('kind') == 'assignment'}-set(targets))
                for target in targets:
                    family = families[(region['module'], target)]
                    reason = family_rejection(family, clock, allow_comb=kind == 'DECODE', reset=reset)
                    if reason:
                        skipped.append(dict(region_id=region['region_id'], recipe=recipe['id'], target=target, reason=reason))
                        continue
                    ids = [n['id'] for n in family]
                    # Combinational expressions using procedural temporaries are
                    # not safely re-evaluated in a concurrent property.
                    local_written = {n['lhs'] for n in nodes.values() if n['kind'] == 'assignment' and n.get('process_id') == family[0].get('process_id')}
                    if recipe['binder'] == 'hold':
                        writes = [guard(n) for n in family if n['rhs'].strip() != target]
                        if not writes or any(is_true(g) for g in writes):
                            continue
                        condition = '!('+' || '.join('('+g+')' for g in writes)+')'
                        emit(region, recipe, 'HOLD', dict(CONDITION=condition, TARGET=target), ids)
                        continue
                    for n in family:
                        g = effective_guard(n, family)
                        if g == "1'b0":
                            skipped.append(dict(region_id=region['region_id'], recipe=recipe['id'], assignment=n['id'], reason='UNCONDITIONALLY_OVERWRITTEN'))
                            continue
                        if n['timing'] == 'same_cycle' and (expression_signals(n['rhs']+' '+g) & local_written):
                            skipped.append(dict(region_id=region['region_id'], recipe=recipe['id'], assignment=n['id'], reason='COMBINATIONAL_PROCEDURAL_DEPENDENCY'))
                            continue
                        is_reset = reset_guard_asserted(guard(n), reset)
                        rhs = n['rhs'].strip()
                        literal = 1 if rhs in {'1', "1'b1"} else 0 if rhs in {'0', "1'b0"} else None
                        op = recipe['binder']
                        if op == 'reset':
                            if is_reset:
                                emit(region, recipe, 'RESET', dict(RESET=g, TARGET=target, VALUE=rhs), ids)
                            continue
                        if op in {'update', 'state_effect'} and (is_reset or rhs == target):
                            continue
                        if op == 'state_effect' and not any(e['source'] == cert['roles'].get('state') and e['target'] == n['id'] and e['type'] == 'CONTROL' for e in graph['edges']):
                            continue
                        if op == 'one' and literal != 1 or op == 'zero' and literal != 0 or op == 'equation' and literal is not None:
                            continue
                        if re.search(r"'(?:[sS])?[bBoOhH]?[xXzZ?]", rhs):
                            skipped.append(dict(region_id=region['region_id'], recipe=recipe['id'], assignment=n['id'], reason='UNKNOWN_VALUE_NOT_AN_EXPECTED_VALUE'))
                            continue
                        delay = 1 if n['timing'] == 'next_cycle' else 0
                        roles = dict(CONDITION=g, TARGET=target, DELAY=delay)
                        if recipe['primitive'] == 'UPDATE':
                            roles['VALUE'] = rhs
                        emit(region, recipe, recipe['primitive'], roles, ids)
            row['property_ids'] = [p.property_id for p in properties[before:]]
            row['status'] = 'INSTANTIATED' if row['property_ids'] else 'NOT_APPLICABLE_OR_UNSUPPORTED'
            region['sva_templates'].append(row)
        inventory.append(region)
    assert len({p.property_id for p in properties}) == len(properties), 'Unexpected repeated instance identity'
    return dict(regions=inventory, contracts=contracts, properties=properties, property_index=source_rows,
                skipped=skipped, invariant_audit=audits)

def guard_boolean_abstraction(text):
    """Sound over-approximation for unsatisfiability checks, not RTL reachability.

Treat non-Boolean subexpressions as independent predicates; normalize explicit
equality/inequality complements. SAT means only 'not ruled out by this check'.
"""
    import z3
    text = text.strip()
    def unwrap(s):
        while s.startswith('(') and s.endswith(')'):
            depth, outer = 0, True
            for i, char in enumerate(s):
                depth += (char == '(')-(char == ')')
                if depth == 0 and i < len(s)-1:
                    outer = False
                    break
            if not outer:
                break
            s = s[1:-1].strip()
        return s
    text = unwrap(text)
    for operator, constructor in [('||', z3.Or), ('&&', z3.And)]:
        depth, start, pieces = 0, 0, []
        i = 0
        while i < len(text):
            char = text[i]
            depth += (char in '([')-(char in ')]')
            if depth == 0 and text[i:i+2] == operator:
                pieces.append(text[start:i])
                start = i+2
                i += 1
            i += 1
        if pieces:
            return constructor(*[guard_boolean_abstraction(s) for s in pieces+[text[start:]]])
    if text.startswith('!'):
        return z3.Not(guard_boolean_abstraction(text[1:]))
    compact = re.sub(r'\s+', '', text)
    if compact in {'0', "1'b0"}:
        return z3.BoolVal(False)
    if compact in {'1', "1'b1"}:
        return z3.BoolVal(True)
    # Only normalize one top-level scalar comparison, never an arbitrary RHS.
    match = re.fullmatch(r'([A-Za-z_][\w$]*)\s*(!=\?|==\?|!=|==)\s*([A-Za-z_][\w$]*|[0-9]+\x27[bBdDhH][0-9a-fA-F_]+)', text)
    if match:
        lhs, op, rhs = match.groups()
        atom = z3.Bool(lhs+('==?' if '?' in op else '==')+rhs)
        return z3.Not(atom) if op.startswith('!') else atom
    return z3.Bool(compact)
