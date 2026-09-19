from pathlib import Path
import pytest
from dateassertion.rtl_frontend.parser import parse_rtl
from dateassertion.rtl_frontend.semantic_graph import build_semantic_graph
from dateassertion.rtl_frontend.graph_patterns import detect_graph_patterns, anonymize_signal_names
from dateassertion.ontology.primitives import _compile
from dateassertion.pipeline.architecture_contracts import compile_architecture_contracts

FIXTURE = Path(__file__).with_name("fixtures_graph_motifs_v4.sv")

def artifacts():
    design = parse_rtl([FIXTURE])
    graph = build_semantic_graph(design)
    patterns = detect_graph_patterns(graph)["patterns"]
    return design, graph, patterns

def test_progress_and_enabled_pipeline_positive_and_negative():
    _,g,patterns=artifacts()
    found={(p["module"],p["kind"]) for p in patterns}
    assert ("progress_mask","ONEHOT_PROGRESS") in found
    assert ("non_onehot_mask","ONEHOT_PROGRESS") not in found
    assert ("enabled_stages","PIPELINE") in found
    assert ("non_copy_stages","PIPELINE") not in found
    edges={(e["source"],e["target"],e["type"]) for e in g["edges"]}
    for p in patterns:
        c=p["match_certificate"]
        assert all((e["source"],e["target"],e["type"]) in edges for e in c["required_edges"]+c["composed_edges"])

def test_register_boundary_keeps_union_but_not_single_derived_history():
    _,_,patterns=artifacts()
    found={p["anchor_signals"][0] for p in patterns if p["module"]=="decode_history_boundary" and p["kind"]=="DECODE"}
    assert "merged" in found and "history" not in found

def test_invariants_use_fixed_compiler_and_do_not_claim_spec():
    d,g,patterns=artifacts()
    regions={"regions":[{**p,"region_id":p["candidate_id"]} for p in patterns]}
    props,bindings,meta,audit=compile_architecture_contracts(d,g,regions,"reset")
    assert any(p.template=="ONEHOT_STATE" and p.target_module=="progress_mask" for p in props)
    assert any(p.template=="STATE_LEGAL" and "3'd5" in p.body for p in props)
    assert all(p.source_classification=="RTL_STRUCTURAL" and p.disable_iff=="reset" for p in props)
    assert len(bindings)==len(props)==len(meta)
    assert all(not c.get("SPEC_conformance",False) for c in audit["candidates"])

def test_new_patterns_are_name_invariant():
    _,g,patterns=artifacts()
    renamed,mapping=anonymize_signal_names(g)
    def signature(ps,translate):
        return {(p["module"],p["kind"],tuple(sorted(translate.get(n,n) for n in p["core_node_ids"]))) for p in ps}
    assert signature(patterns,mapping)==signature(detect_graph_patterns(renamed)["patterns"],{})

@pytest.mark.parametrize("primitive,roles",[("STATE_LEGAL",{"TARGET":"state","VALUES":[]}),
    ("STATE_LEGAL",{"TARGET":"state","VALUES":["unknown_signal"]}),
    ("STATE_LEGAL",{"TARGET":"state","VALUES":["3'b7"]}),
    ("STATE_LEGAL",{"TARGET":"state","VALUES":["3'dff"]}),
    ("STATE_LEGAL",{"TARGET":"state","VALUES":["0'd0"]}),("ONEHOT_STATE",{})])
def test_invalid_invariant_roles_rejected(primitive,roles):
    assert _compile(primitive,{"roles":roles}) is None

def test_indexed_properties_sample_address_and_preserve_write_priority(tmp_path):
    from dateassertion.generators.sva_generator import generate_sva
    d,g,patterns=artifacts()
    regions={'regions':[{**p,'region_id':p['candidate_id']} for p in patterns if p['module']=='indexed_bank']}
    props,_,_,_=compile_architecture_contracts(d,g,regions,'reset')
    assert len(props)==4
    write=next(p for p in props if p.template=='INDEXED_WRITE' and p.bindings['INDEX']=='wa')
    assert 'storage[$past(wa)]' in write.body and '$past(wd)' in write.body
    assert 'wb' in write.bindings['CONDITION'] and 'en2' in write.bindings['CONDITION']
    assert d.module_signals['indexed_bank']['storage'].unpacked_dimensions == ['[15:0]']
    rendered=generate_sva(props,d.signals,'indexed_bank',tmp_path/'bank.sv',clock='clk',reset='reset',module_signals=d.module_signals)
    assert 'storage [WIDTH_STORAGE_LEFT:WIDTH_STORAGE_RIGHT]' in rendered
    assert '$left(storage)' in rendered and '$right(storage)' in rendered

def test_indexed_templates_require_array_role_and_sample_write_index():
    roles={'CONDITION':'we','BANK':'bank','INDEX':'addr','VALUE':'data'}
    body,_=_compile('INDEXED_WRITE',{'roles':roles})
    assert body=='(we) |=> bank[$past(addr)] == $past(data)'
    assert _compile('INDEXED_READ',{'roles':roles}) is None

def test_gated_array_read_has_selected_arm_condition():
    d,g,patterns=artifacts()
    bank=next(p for p in patterns if p['module']=='gated_bank' and p['kind']=='REGISTER_FILE')
    regions={'regions':[{**bank,'region_id':bank['candidate_id']}]}
    props,_,_,_=compile_architecture_contracts(d,g,regions,'reset')
    reads=[p for p in props if p.template=='INDEXED_READ']
    assert len(reads)==2
    assert all(p.bindings['INDEX'] in p.bindings['CONDITION'] for p in reads)

def test_uninitialized_mask_gets_seed_and_preservation_not_global_assertion():
    d,g,patterns=artifacts()
    regions={'regions':[{**p,'region_id':p['candidate_id']} for p in patterns if p['module']=='uninitialized_mask']}
    props,_,_,_=compile_architecture_contracts(d,g,regions,'reset')
    assert len(props)==1 and props[0].template=='ONEHOT_STEP'
    assert 'start' in props[0].bindings['SEED']
    assert ' |=> $onehot0(mask)' in props[0].body

@pytest.mark.parametrize('module,kind,edge_type', [
    ('progress_mask','ONEHOT_PROGRESS','SEQUENTIAL'),
    ('enabled_stages','PIPELINE','SEQUENTIAL'),
    ('gated_bank','REGISTER_FILE','DATA'),
])
def test_new_motifs_require_literal_core_edges(module,kind,edge_type):
    from copy import deepcopy
    _,g,patterns=artifacts()
    match=next(p for p in patterns if p['module']==module and p['kind']==kind)
    edge=next(e for e in match['match_certificate']['required_edges'] if e['type']==edge_type)
    broken=deepcopy(g)
    key=lambda e:(e['source'],e['target'],e['type'])
    broken['edges']=[e for e in broken['edges'] if key(e)!=key(edge)]
    assert not any(p['module']==module and p['kind']==kind for p in detect_graph_patterns(broken)['patterns'])

@pytest.mark.parametrize('guard,reset,expected', [
    ('reset','reset',True), ('!(reset)','reset',False),
    ('!resetn && enable','!resetn',True), ('resetn && enable','!resetn',False),
    ("resetn == 1'b0",'!resetn',True), ('reset || start','reset',False),
])
def test_global_invariant_reset_guard_requires_asserted_polarity(guard,reset,expected):
    from dateassertion.rtl_frontend.invariant_patterns import reset_guard_asserted
    assert reset_guard_asserted(guard,reset) == expected
