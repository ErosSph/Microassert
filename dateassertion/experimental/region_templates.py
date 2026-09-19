"""Demo knowledge packs: matching specification + assertion recipes, not DUT names.

Recipes are optional obligations subject to their applicability conditions. A recipe
may instantiate many properties. Shared primitives are not counted as new syntax.
"""
from copy import deepcopy
from dateassertion.rtl_frontend.graph_motif_library import MOTIFS, LIBRARY_VERSION

VERSION = 'region-sva-packs.demo.v1'


def recipe(key, name, binder, primitive, requires):
    return dict(id=key, name=name, binder=binder, primitive=primitive, requires=requires)


PACKS = {
    'FSM': dict(
        motifs=['constant_state_feedback', 'split_next_state_feedback'],
        targets=['state'],
        recipes=[
            recipe('legal', '状态编码合法', 'invariant', 'STATE_LEGAL', '完整常量写入族；非平凡合法集合'),
            recipe('reset', '状态复位', 'reset', 'RESET', '同钟完整标量赋值；可识别复位条件'),
            recipe('transition', '条件状态转移', 'update', 'UPDATE', '直接反馈 FSM；完整非复位有效写入条件'),
            recipe('hold', '未更新时保持状态', 'hold', 'HOLD', '完整写入族；存在未写入或显式自保持条件'),
            recipe('state_effect', '状态控制的寄存输出', 'state_effect', 'UPDATE', '状态到赋值的直接 CONTROL 边；完整目标写入族'),
        ]),
    'DECODE': dict(
        motifs=['decode_boolean_equation', 'decode_default_override', 'composed_boolean_decode'],
        targets=['result'],
        recipes=[
            recipe('hit', '译码命中置位', 'one', 'CONTROL_ASSERT', '一位目标；有效分支写 1；绑定实际时延'),
            recipe('miss', '译码未命中清零', 'zero', 'CONTROL_DEASSERT', '有效分支写 0；排除后续覆盖赋值'),
            recipe('equation', '译码布尔表达式一致', 'equation', 'UPDATE', '非字面量表达式；完整控制条件；无过程内临时量依赖'),
        ]),
    'REGISTER_UPDATE': dict(
        motifs=['clocked_register_assignment'], targets=['result'],
        recipes=[
            recipe('reset', '寄存器复位', 'reset', 'RESET', '识别复位分支及复位值'),
            recipe('update', '条件数据更新', 'update', 'UPDATE', '完整有效写入条件；同钟全标量写入'),
            recipe('hold', '不写入时保持', 'hold', 'HOLD', '所有写入来源均已纳入，包含 default/X 写入'),
        ]),
    'PIPELINE': dict(
        motifs=['two_copy_register_stages', 'enabled_copy_register_stages'],
        targets=['middle', 'sink'],
        recipes=[
            recipe('transfer', '逐级有效传递', 'update', 'UPDATE', '已匹配同宽同钟复制链；每一级使用自己的有效写入条件'),
            recipe('stall_hold', '各级停顿保持', 'hold', 'HOLD', '完整写入族的未写入或自保持条件；不假设共享 stall'),
            recipe('reset', '各级复位', 'reset', 'RESET', '该级实际存在复位分支'),
        ]),
    'ONEHOT_PROGRESS': dict(
        motifs=['onehot_shift_progress'], targets=['state'],
        recipes=[
            recipe('initialized_legal', '已初始化状态独热', 'invariant', 'ONEHOT_STATE', '合法移位/保持写入族及可识别复位初始化'),
            recipe('seed_step', '种子建立与独热保持', 'invariant', 'ONEHOT_STEP', '合法种子但没有可识别复位初始化；不能宣称启动前合法'),
        ]),
}

FORMS = {
    'RESET': '(RESET) |=> TARGET == (VALUE)',
    'UPDATE': 'DELAY=0: (CONDITION) |-> TARGET == (VALUE); DELAY=1: (CONDITION) |=> TARGET == $past(VALUE)',
    'HOLD': '(CONDITION) |=> $stable(TARGET)',
    'CONTROL_ASSERT': '(CONDITION) |->/|=> TARGET (operator selected by DELAY)',
    'CONTROL_DEASSERT': '(CONDITION) |->/|=> !TARGET (operator selected by DELAY)',
    'STATE_LEGAL': "(1'b1) |-> TARGET inside {VALUES}",
    'ONEHOT_STATE': "(1'b1) |-> $onehot0(TARGET)",
    'ONEHOT_STEP': '((SEED) || $onehot0(TARGET)) |=> $onehot0(TARGET)',
}


def resolved_library():
    motifs = {m['id']: m for m in MOTIFS}
    result = {}
    for kind, pack in PACKS.items():
        entry = deepcopy(pack)
        entry['match_patterns'] = [deepcopy(motifs[mid]) for mid in pack['motifs']]
        for rule in entry['recipes']:
            rule['sva_form'] = FORMS[rule['primitive']]
            rule['compiler'] = 'dateassertion.ontology.primitives._compile'
        result[kind] = entry
    return dict(version=VERSION, matcher_library=LIBRARY_VERSION, packs=result,
        non_goals=['FIFO not implemented', 'No SPEC-completeness claim', 'No feedback loop implemented in this demo',
                   'No arithmetic reference model, liveness bound, or end-to-end transaction proof inferred from a label'])
