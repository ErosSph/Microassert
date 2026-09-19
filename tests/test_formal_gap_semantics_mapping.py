from dateassertion.coverage_analysis.proof_core import CoverItem

from dateassertion.pipeline.formal_gap_semantics import (
    build_elaborated_toggle_mapping_index,
    resolve_elaborated_toggle_producers,
)


def _item(*, instance="g[3].u_child", module="child:(WIDTH=8)"):
    return CoverItem(
        1, "uncovered_or_unchecked", "Uncovered or Unchecked", "Unchecked", "toggle",
        f'toggle for signal bit "{instance}.din[7]"', "", module, instance,
        "/rtl/child.sv", 7, 1, 7, 2,
    )


def _graph():
    nodes = [
        {"id": "signal:child.din", "kind": "signal", "module": "child", "name": "din",
         "direction": "input", "source": {"file": "/rtl/child.sv", "line": 7}},
        {"id": "signal:parent.payload", "kind": "signal", "module": "parent", "name": "payload",
         "direction": "internal", "source": {"file": "/rtl/parent.sv", "line": 21}},
        {"id": "assignment:parent_payload", "kind": "assignment", "module": "parent", "lhs": "payload",
         "source": {"file": "/rtl/parent.sv", "line": 30}},
    ]
    return {
        "nodes": nodes,
        "edges": [{"type": "DATA", "source": "assignment:parent_payload", "target": "signal:parent.payload"}],
    }


def _design_map(*, connection=True, semantic_kind="DATA", duplicate_source=False):
    edge = {
        "id": "cross:payload", "type": "CROSS_MODULE", "semantic_kind": semantic_kind,
        "direction": "input", "port": "din", "parent_expression": "payload",
        "source": {"instance_path": "top.parent", "module": "parent", "signal": "payload"},
        "target": {"instance_path": "top.parent.g[3].u_child", "module": "child", "signal": "din"},
    }
    edges = [edge] if connection else []
    if duplicate_source:
        edges.append({
            **edge, "id": "cross:other",
            "source": {"instance_path": "top.parent", "module": "parent", "signal": "other_payload"},
        })
    return {
        "instances": [{
            "path": "top.parent.g[3].u_child", "module": "child",
            "parent_path": "top.parent", "parent_module": "parent",
        }],
        "cross_module_dependencies": edges,
    }


def test_parameterized_generated_input_toggle_maps_to_exact_parent_producer():
    graph = _graph()
    design_map = _design_map()
    result = resolve_elaborated_toggle_producers(
        _item(), graph, design_map,
        mapping_index=build_elaborated_toggle_mapping_index(graph, design_map),
    )

    assert result == {
        "resolved": True,
        "producer_resolution": "EXACT_CROSS_MODULE_DATA_PORT",
        "diagnosis_reason": "declaration toggle traced through one exact elaborated DATA input-port connection to parent assignment producers",
        "signal_node_ids": ["signal:child.din", "signal:parent.payload"],
        "producer_assignment_ids": ["assignment:parent_payload"],
        "cross_module_evidence": ["cross:payload"],
    }


def test_cross_module_mapping_rejects_non_data_or_ambiguous_connections():
    non_data = resolve_elaborated_toggle_producers(
        _item(), _graph(), _design_map(semantic_kind="CONTROL"),
    )
    assert not non_data["resolved"]
    assert non_data["producer_resolution"] == "NO_EXACT_DATA_PORT_CONNECTION"

    ambiguous = resolve_elaborated_toggle_producers(
        _item(), _graph(), _design_map(duplicate_source=True),
    )
    assert not ambiguous["resolved"]
    assert ambiguous["producer_resolution"] == "AMBIGUOUS_EXACT_DATA_PORT_CONNECTION"


def test_mapping_does_not_invent_producer_when_exact_source_lacks_assignment():
    graph = _graph()
    graph["edges"] = []

    result = resolve_elaborated_toggle_producers(_item(), graph, _design_map())

    assert not result["resolved"]
    assert result["producer_resolution"] == "EXACT_PORT_SOURCE_WITHOUT_LOCAL_PRODUCER"
    assert result["producer_assignment_ids"] == []


def test_cross_module_recovery_does_not_attach_parent_obligation_to_child_region():
    from dateassertion.pipeline.feedback_regions import localize_refinement_gaps
    graph = _graph()
    child = {"region_id": "a_child", "module": "child", "kind": "DATAPATH",
             "core_node_ids": ["signal:child.din"], "signals": ["din"], "coi": {"node_ids": []}}
    parent = {"region_id": "z_parent", "module": "parent", "kind": "DATAPATH",
              "core_node_ids": ["assignment:parent_payload"], "signals": ["payload"], "coi": {"node_ids": []}}
    without_parent = localize_refinement_gaps([_item()], graph, [child], design_map=_design_map())[0]
    assert without_parent["gap_type"] == "A_REGION_GAP"
    assert without_parent["existing_region_ids"] == []
    with_parent = localize_refinement_gaps([_item()], graph, [child, parent], design_map=_design_map())[0]
    assert with_parent["gap_type"] == "B_CONTRACT_GAP"
    assert with_parent["existing_region_ids"] == ["z_parent"]
