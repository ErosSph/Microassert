from pathlib import Path
import json

import pytest

from dateassertion.cli import main, fingerprint
from dateassertion.config import load_config

ROOT = Path(__file__).resolve().parents[1]
CONFIG = ROOT/'configs/example.yaml'


def test_config_paths_independent_of_cwd(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    cfg = load_config(CONFIG)
    assert Path(cfg['design']['rtl_files'][0]).is_file()
    assert cfg['feedback']['deduplicate_sva'] is False
    assert cfg['design']['role'] == 'USER_DESIGN'
    assert cfg['design_flow']['max_candidates_per_kind_per_module'] is None
    assert cfg['llm']['proxy'] is None
    assert len(fingerprint(cfg)) == 64


def test_inline_credentials_rejected(tmp_path):
    config = tmp_path/'bad.yaml'
    config.write_text('design: {}\nllm:\n  api_key: fixture-secret\n')
    with pytest.raises(ValueError, match='Inline credentials'):
        load_config(config)


def test_environment_overrides_without_serializing_api_key(monkeypatch):
    monkeypatch.setenv('LLM_BASE_URL', 'https://fixture.invalid/v1')
    monkeypatch.setenv('LLM_MODEL', 'fixture-model')
    monkeypatch.setenv('LLM_API_KEY', 'fixture-secret-value')
    cfg = load_config(CONFIG)
    assert cfg['llm']['base_url'] == 'https://fixture.invalid/v1'
    assert cfg['llm']['model'] == 'fixture-model'
    assert 'fixture-secret-value' not in json.dumps(cfg)


@pytest.mark.parametrize('experimental,expected', [(False,1),(True,36)])
def test_offline_cli_smoke(tmp_path, experimental, expected):
    argv=['analyze','--config',str(CONFIG),'--output',str(tmp_path)]
    if experimental:
        argv.append('--region-templates')
    assert main(argv) == 0
    rows=json.loads((tmp_path/'properties.json').read_text())
    assert len(rows) == expected
    assert (tmp_path/'assertions.sv').read_text().count(': assert property (') == expected
    before=(tmp_path/'properties.json').read_bytes()
    assert main(argv) == 1  # Do not overwrite a previous experiment.
    assert (tmp_path/'properties.json').read_bytes() == before


def test_generic_provider_omits_proprietary_thinking(monkeypatch):
    from dateassertion.llm.client import DeepSeekClient, DeepSeekConfig
    import io
    requests=[]
    class Opener:
        def open(self, request, timeout):
            requests.append(json.loads(request.data))
            return io.BytesIO(b'{"choices":[{"message":{"content":"{\\"ok\\":true}"}}]}')
    monkeypatch.setenv('LLM_API_KEY', 'fixture-key')
    client=DeepSeekClient(DeepSeekConfig(provider='openai-compatible',api_key_env='LLM_API_KEY',base_url='https://fixture.invalid/v1'))
    monkeypatch.setattr(client,'_opener',lambda:Opener())
    assert client.complete_json('JSON','JSON')[0] == {'ok':True}
    assert 'thinking' not in requests[0] and 'enable_thinking' not in requests[0]
    assert client._endpoint_urls() == ['https://fixture.invalid/v1/chat/completions']


def test_full_driver_resume_and_raw_export_with_mocked_expensive_stages(tmp_path, monkeypatch):
    """Real driver/file layout, mocked LLM/Jasper orchestration (not a proof)."""
    from dateassertion import cli
    from dateassertion.pipeline import design_flow, feedback_loop
    from dateassertion.ir.schema import PropertyIR, ObjectType, dump_json
    calls=[]
    cfg=load_config(CONFIG)
    prop=PropertyIR(property_id='local_1',region_id='region',object_type=ObjectType.FSM,
        family='PRIMITIVE_STATE_LEGAL',template='STATE_LEGAL',bindings={},signals=['state'],
        body="1'b1 |-> state inside {0,1,2}",target_module='controller',disable_iff='!rst_n',source='test',llm_confidence=1.0)
    def initial(target, config, output):
        calls.append('initial')
        dump_json(output/target['design_id']/'local_candidates.json',[prop])
        dump_json(output/target['design_id']/'composition_properties.json',[])
    def feedback(target, config, initial, output, rounds):
        calls.append('feedback')
        for i in range(1,rounds+1):
            root=output/'rounds'/f'round_{i:02d}'
            dump_json(root/'local/generated_properties.json',[])
            dump_json(root/'composition/generated_properties.json',[])
    monkeypatch.setattr(cli,'require_llm',lambda c:None)
    monkeypatch.setattr(cli,'require_formal',lambda c:None)
    monkeypatch.setattr(design_flow,'_run_design',initial)
    monkeypatch.setattr(feedback_loop,'run_feedback',feedback)
    assert cli.run_flow(cfg,tmp_path,0)['generated'] == 1
    assert cli.run_flow(cfg,tmp_path,1)['generated'] == 1
    assert calls == ['initial','feedback']
    cfg['formal']['prove_time_limit']='601s'
    with pytest.raises(RuntimeError,match='Inputs/config/code changed'):
        cli.run_flow(cfg,tmp_path,1)


def test_packaged_resources_exist():
    import dateassertion
    package=Path(dateassertion.__file__).parent
    for name in ['defaults.yaml','formal/report_effective.tcl','ontology/core_ontology.json',
                 'llm/prompts/spec_behaviors.txt','llm/prompts/composition_constraints.txt']:
        assert (package/name).is_file(), name


def test_failed_stage_is_not_left_running(tmp_path, monkeypatch):
    monkeypatch.delenv('LLM_API_KEY', raising=False)
    assert main(['run','--config',str(CONFIG),'--output',str(tmp_path),'--rounds','0']) == 1
    assert json.loads((tmp_path/'status.json').read_text())['status'] == 'FAILED'


def test_release_no_workstation_paths_or_secret_note_dependency():
    root=ROOT/'dateassertion'
    for path in root.rglob('*'):
        if path.is_file() and path.suffix in {'.py','.txt','.yaml','.json','.tcl'}:
            content=path.read_text()
            assert '/data2/home/' not in content, path
            assert 'codex.md' not in content, path
    assert not list(root.rglob('*requirement*.py'))
