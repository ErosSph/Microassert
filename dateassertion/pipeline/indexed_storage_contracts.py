"""Element-level array contracts with sampled write addresses and write priority.

Only identified register banks, one-dimensional unpacked storage, module-visible
indices and single-process producer families. No memory assumptions/scoreboard.
"""
import re
from dateassertion.ontology.primitives import expression_signals
from dateassertion.rtl_frontend.graph_motif_matching import compact, clock_event
from dateassertion.rtl_frontend.invariant_patterns import indexed_access


def indexed_storage_records(design, matcher, inventory):
    idx = matcher.index
    records, rejected, seen = [], [], set()
    def index(text, bank):
        match = re.fullmatch(re.escape(bank) + r"\[([A-Za-z_][\w$]*)\]", compact(text))
        return match[1] if match else None
    def bindable(module, expressions):
        symbols = design.module_signals.get(module, {})
        names = set().union(*(expression_signals(e) for e in expressions))
        return all(n in symbols and symbols[n].kind not in {"integer", "genvar"}
                   and not symbols[n].kind.endswith("_array") for n in names)
    def later_guard(node, family, current_index=None, bank=None):
        terms = [node.get("guard") or "1'b1"]
        for other in family:
            if other.get("source_order",0) <= node.get("source_order",0):
                continue
            guard = other.get("guard") or "1'b1"
            if bank is not None:
                addr = index(other.get("lhs_expression", ""), bank)
                if addr is None:
                    return None
                guard = f"({guard}) && (({addr}) == ({current_index}))"
            terms.append(f"!({guard})")
        return " && ".join(f"({t})" for t in terms)
    for region in inventory.get("regions", []):
        if region.get("kind") != "REGISTER_FILE":
            continue
        cert = region.get("match_certificate") or {}
        bank_id = cert.get("roles", {}).get("bank")
        if bank_id not in idx.nodes or bank_id in seen:
            continue
        seen.add(bank_id)
        bank = idx.nodes[bank_id]["name"]
        module = region["module"]
        info = design.module_signals.get(module, {}).get(bank)
        if info is None or len(info.unpacked_dimensions) != 1:
            rejected.append({"module":module,"bank":bank,"reason":"missing_single_dimension_observation_metadata"})
            continue
        family = [idx.nodes[a] for a in matcher.family(bank_id)]
        processes = {n.get("process_id") for n in family}
        if None in processes or len(processes) != 1 or not all(clock_event(n) for n in family):
            rejected.append({"module":module,"bank":bank,"reason":"multiple_or_unknown_storage_writer_processes"})
            continue
        for node in family:
            address = index(node.get("lhs_expression", ""), bank)
            guard = later_guard(node, family, address, bank) if address else None
            if not guard or not bindable(module,[address,node["rhs"],guard]):
                rejected.append({"module":module,"node_id":node["id"],"reason":"unbound_write_index_value_or_priority"})
                continue
            if matcher.names.get((module,address)) not in idx.assignment_controls[node["id"]]:
                continue
            records.append((region,"INDEXED_WRITE",{"CONDITION":guard,"BANK":bank,"INDEX":address,"VALUE":node["rhs"]},
                            {n["id"] for n in family}|{bank_id}))
        consumers = {e["target"] for e in idx.outgoing[bank_id]["DATA"] if e["target"] in idx.assignment_target}
        for aid in sorted(consumers):
            node = idx.nodes[aid]
            access = indexed_access(node.get("rhs", ""))
            address = access[1] if access and access[0] == bank else None
            if not address or node.get("timing") != "same_cycle" or node.get("lhs_expression",node["lhs"]) != node["lhs"]:
                continue
            target = idx.assignment_target[aid]
            producers = [idx.nodes[a] for a in matcher.family(target)]
            if len({n.get("process_id") for n in producers}) != 1:
                continue
            # Multiple continuous drivers share process_id=None, not a process.
            if len(producers)>1 and node.get("process_id") is None:
                continue
            guard = later_guard(node, producers)
            if guard and access[2]:
                guard = f"({guard}) && ({access[2]})"
            if not guard or not bindable(module,[address,guard,node["lhs"]]):
                continue
            records.append((region,"INDEXED_READ",{"CONDITION":guard,"BANK":bank,"INDEX":address,"TARGET":node["lhs"]},
                            {n["id"] for n in producers}|{bank_id,target}))
    return records, rejected
