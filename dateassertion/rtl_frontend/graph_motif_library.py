"""Versioned structural motifs, not signal-name rules or weighted features.

Edges below must occur literally in the RTL graph. Additional host edges are
allowed (monomorphism). Family predicates in graph_motif_matching close the
semantic checks that cannot be expressed by node/edge labels alone.
"""

LIBRARY_VERSION = "rtl-attributed-motifs.v4"


def signal(**attributes):
    return {"kind": "signal", **attributes}


def assignment(**attributes):
    return {"kind": "assignment", **attributes}


MOTIFS = (
    {"id": "decode_boolean_equation", "kind": "DECODE", "anchor": "result",
     "nodes": {"selector": signal(wide=True), "compare": assignment(equality_rhs=True),
               "result": signal(bit=True, anchor=True)},
     "edges": [("selector", "compare", "DATA"), ("compare", "result", "DATA")],
     "predicates": ["selector_compared_to_constant", "single_boolean_equation_producer",
                    "no_result_feedback"]},
    {"id": "decode_default_override", "kind": "DECODE", "anchor": "result",
     "nodes": {"selector": signal(wide=True), "default": assignment(zero=True),
               "branch": assignment(one=True, equality_guard=True),
               "result": signal(bit=True, anchor=True)},
     "edges": [("selector", "branch", "CONTROL"), ("default", "result", "DATA"),
               ("branch", "result", "DATA")],
     "predicates": ["selector_compared_to_constant", "same_process_default_precedes_override",
                    "default_guard_is_branch_prefix", "boolean_producer_family_no_feedback"]},
    {"id": "constant_state_feedback", "kind": "FSM", "anchor": "state",
     "nodes": {"state": signal(anchor=True),
               "transition": assignment(sequential=True, constant=True),
               "alternative": assignment(sequential=True, constant=True)},
     "edges": [("state", "transition", "CONTROL"), ("transition", "state", "DATA"),
               ("alternative", "state", "DATA")],
     "predicates": ["distinct_constant_next_values", "constant_or_hold_producer_family",
                    "same_clock_event", "explicit_state_condition"]},
    {"id": "two_copy_register_stages", "kind": "PIPELINE", "anchor": "sink",
     "nodes": {"source": signal(), "first": assignment(sequential=True, copy=True),
               "middle": signal(), "second": assignment(sequential=True, copy=True),
               "sink": signal(anchor=True)},
     "edges": [("source", "first", "DATA"), ("first", "middle", "DATA"),
               ("middle", "second", "DATA"), ("second", "sink", "DATA"),
               ("source", "middle", "SEQUENTIAL"), ("middle", "sink", "SEQUENTIAL")],
     "predicates": ["exact_copy_rhs", "equal_known_widths", "same_clock_event",
                    "copy_reset_hold_only_families", "no_local_feedback"]},
    {"id": "split_next_state_feedback", "kind": "FSM", "anchor": "state",
     "nodes": {"state": signal(anchor=True), "transition": assignment(constant=True),
               "alternative": assignment(constant=True), "next": signal(),
               "register": assignment(sequential=True, copy=True)},
     "edges": [("state", "transition", "CONTROL"), ("transition", "next", "DATA"),
               ("alternative", "next", "DATA"), ("next", "register", "DATA"),
               ("register", "state", "DATA"), ("next", "state", "SEQUENTIAL")],
     "predicates": ["constant_or_hold_next_state_family", "distinct_constant_next_values",
                    "exact_next_state_register_copy", "same_clock_event", "explicit_state_condition"]},
    {"id": "request_active_response", "kind": "HANDSHAKE", "anchor": "active",
     "nodes": {"request": signal(bit=True), "set": assignment(sequential=True, one=True),
               "active": signal(bit=True, anchor=True),
               "clear": assignment(sequential=True, zero=True),
               "respond": assignment(sequential=True, one=True),
               "response": signal(bit=True, output=True)},
     "edges": [("request", "set", "CONTROL"), ("set", "active", "DATA"),
               ("active", "clear", "CONTROL"), ("clear", "active", "DATA"),
               ("active", "respond", "CONTROL"), ("respond", "response", "DATA")],
     "predicates": ["positive_request_and_active_conditions", "same_completion_guard",
                    "same_clock_event", "boolean_active_family"],
     "limitation": "Lifecycle motif only; protocol acceptance and liveness are not proven."},
    {"id": "clocked_register_assignment", "kind": "REGISTER_UPDATE", "anchor": "result",
     "nodes": {"update": assignment(sequential=True), "result": signal(anchor=True)},
     "edges": [("update", "result", "DATA")],
     "predicates": ["known_clock_event"]},
    {"id": "operator_data_transform", "kind": "DATAPATH", "anchor": "result",
     "nodes": {"operand": signal(), "transform": assignment(transform=True),
               "result": signal(anchor=True)},
     "edges": [("operand", "transform", "DATA"), ("transform", "result", "DATA")],
     "predicates": ["operator_ast_with_literal_data_dependency"]},
)

# These are supported structural classes, not a claim to exhaust a CPU SPEC.
# Operator classes intentionally overlap DATAPATH; ALU is a composed region.
def operator_motif(kind, attribute):
    return {"id": kind.lower() + "_operator", "kind": kind, "anchor": "result",
            "nodes": {"operand": signal(), "operation": assignment(**{attribute: True}),
                      "result": signal(anchor=True)},
            "edges": [("operand", "operation", "DATA"), ("operation", "result", "DATA")],
            "predicates": ["root_operator_" + attribute, "actual_operand_dependency"]}


MOTIFS += tuple(operator_motif(k, a) for k, a in (
    ("SHIFTER", "shift"), ("COMPARATOR", "compare"),
    ("MULTIPLIER", "multiply"), ("DIVIDER", "divide"), ("MUX", "mux")))
MOTIFS += tuple({
    "id": kind.lower() + "_feedback", "kind": kind, "anchor": "state",
    "nodes": {"state": signal(anchor=True), "update": assignment(sequential=True, addsub=True)},
    "edges": [("state", "update", "DATA"), ("update", "state", "DATA"),
              ("state", "state", "SEQUENTIAL")],
    "predicates": ["same_clock_event", "self_add_subtract_" + operand,
                   "other_producers_are_reset_hold_or_same_recurrence"],
} for kind, operand in (("COUNTER", "nonzero_constant"), ("ACCUMULATOR", "dynamic_operand")))
MOTIFS += ({
    "id": "selected_arithmetic_logic_cone", "kind": "ALU", "anchor": "result",
    "nodes": {"operand": signal(), "select": assignment(selection=True), "result": signal(anchor=True)},
    "edges": [("operand", "select", "DATA"), ("select", "result", "DATA")],
    "predicates": ["connected_combinational_selected_data_cone",
                   "arithmetic_and_logic_or_shift_branches", "data_operations_not_selector_operations"],
    "limitation": "ALU-like selected operation cone; ISA operation map needs SPEC binding. No cross-module flattening.",
},)

MOTIFS += (
    {"id": "composed_boolean_decode", "kind": "DECODE", "anchor": "result",
     "nodes": {"input": signal(), "equation": assignment(), "result": signal(bit=True, anchor=True)},
     "edges": [("input", "equation", "DATA"), ("equation", "result", "DATA")],
     "predicates": ["boolean_producer_family_grounded_in_encoded_selectors",
                    "every_or_arm_has_decode_evidence", "no_combinational_or_state_feedback"],
     "extension": "decode"},
    {"id": "guarded_operation_family", "kind": "ALU", "anchor": "result",
     "nodes": {"first": assignment(), "second": assignment(), "result": signal(anchor=True)},
     "edges": [("first", "result", "DATA"), ("second", "result", "DATA")],
     "predicates": ["same_process_combinational_operation_family", "distinct_encoded_guard_values",
                    "selected_arithmetic_and_logic_or_shift"], "extension": "case_alu"},
    {"id": "indexed_clocked_multi_read_bank", "kind": "REGISTER_FILE", "anchor": "bank",
     "nodes": {"bank": signal(array=True, anchor=True), "write": assignment(sequential=True),
               "read_a": assignment(indexed_read=True), "read_b": assignment(indexed_read=True),
               "out_a": signal(), "out_b": signal()},
     "edges": [("write", "bank", "DATA"), ("bank", "read_a", "DATA"),
               ("bank", "read_b", "DATA"), ("read_a", "out_a", "DATA"), ("read_b", "out_b", "DATA")],
     "predicates": ["dynamic_indexed_clocked_write", "two_distinct_combinational_read_addresses",
                    "same_storage_bank", "literal_write_index_dependency"], "extension": "register_file",
     "limitation": "Multi-read indexed register bank candidate; x0, bypass and collision policy require SPEC."},
    {"id": "address_subword_load_store", "kind": "LSU", "anchor": "address",
     "nodes": {"operand": signal(), "add": assignment(addsub=True), "address": signal(anchor=True)},
     "edges": [("operand", "add", "DATA"), ("add", "address", "DATA")],
     "predicates": ["address_calculation_reaches_output", "subword_load_and_store_merge",
                    "distinct_operation_contexts_share_encoded_selector", "address_context_covers_each_operation"],
     "extension": "lsu",
     "limitation": "Read-modify-write subword LSU datapath signature; not complete LSU protocol / exceptions."},
)

MOTIFS += ({
    "id": "gated_indexed_multi_read_bank", "kind": "REGISTER_FILE", "anchor": "bank",
    "nodes": {"bank":signal(array=True,anchor=True),"write":assignment(sequential=True),
              "read_a":assignment(gated_indexed_read=True),"read_b":assignment(gated_indexed_read=True),
              "out_a":signal(),"out_b":signal()},
    "edges": [("write","bank","DATA"),("bank","read_a","DATA"),("bank","read_b","DATA"),
              ("read_a","out_a","DATA"),("read_b","out_b","DATA")],
    "predicates": ["dynamic_indexed_clocked_write","two_distinct_guarded_array_read_addresses",
                   "zero_alternative_arm","literal_read_write_index_dependencies"],
    "extension":"register_file", "gated_reads":True,
    "limitation":"Conditional zero/array read bank candidate; reserved-register intent requires SPEC.",
},)
MOTIFS += tuple({
    "id": "iterative_" + operation + "_shift_feedback", "kind": kind, "anchor": "state",
    "nodes": {"shift_state": signal(), "shift": assignment(sequential=True),
              "arithmetic": assignment(sequential=True, addsub=True), "state": signal(anchor=True)},
    "edges": [("shift_state", "shift", "DATA"), ("shift", "shift_state", "DATA"),
              ("shift_state", "arithmetic", "DATA"), ("state", "arithmetic", "DATA"),
              ("arithmetic", "state", "DATA"), ("state", "state", "SEQUENTIAL"),
              ("shift_state", "shift_state", "SEQUENTIAL")],
    "predicates": ["same_clock_connected_shift_arithmetic_recurrence", "conditional_" + operation,
                   "operand_initialization", "progress_state_drives_completion_output"],
    "extension": "iterative", "operation": operation,
    "limitation": "Iterative algorithm candidate; result mathematics and cycle bound are separate obligations.",
} for kind, operation in (("ITERATIVE_MULTIPLIER", "add"), ("ITERATIVE_DIVIDER", "subtract")))

MOTIFS += (
    {"id": "onehot_shift_progress", "kind": "ONEHOT_PROGRESS", "anchor": "state",
     "nodes": {"state": signal(wide=True, anchor=True), "shift": assignment(sequential=True, shift=True)},
     "edges": [("state", "shift", "DATA"), ("shift", "state", "DATA"), ("state", "state", "SEQUENTIAL")],
     "predicates": ["complete_same_clock_producer_family", "zero_or_power_of_two_initializers",
                    "logical_self_shift_or_hold_only", "progress_controls_other_assignment"],
     "extension": "onehot_progress",
     "limitation": "Shift-mask progress candidate, not proof of algorithm completion or latency."},
    {"id": "enabled_copy_register_stages", "kind": "PIPELINE", "anchor": "sink",
     "nodes": {"source": signal(), "first": assignment(sequential=True), "middle": signal(),
               "second": assignment(sequential=True), "sink": signal(anchor=True)},
     "edges": [("source", "first", "DATA"), ("first", "middle", "DATA"),
               ("middle", "second", "DATA"), ("second", "sink", "DATA"),
               ("source", "middle", "SEQUENTIAL"), ("middle", "sink", "SEQUENTIAL")],
     "predicates": ["same_clock_equal_width", "conditional_copy_self_hold",
                    "actual_enable_control_or_data_dependency", "complete_copy_reset_hold_families"],
     "extension": "enabled_pipeline",
     "limitation": "Two register stages with conditional copy/hold; no inferred fixed transaction latency."},
)
