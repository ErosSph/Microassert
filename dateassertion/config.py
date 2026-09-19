"""Portable configuration; credentials are environment-only."""
from copy import deepcopy
import os
from pathlib import Path
import re
import shutil
import yaml


def merge(base, updates):
    result = deepcopy(base)
    for key, value in updates.items():
        result[key] = merge(result[key], value) if isinstance(value, dict) and isinstance(result.get(key), dict) else deepcopy(value)
    return result


def load_config(filename):
    path = Path(filename).resolve()
    raw = yaml.safe_load(path.read_text())
    if not isinstance(raw, dict) or not isinstance(raw.get('design'), dict):
        raise ValueError('Config must contain a design mapping')
    def reject_secrets(value):
        if isinstance(value, dict):
            for key, item in value.items():
                if key.lower() in {'api_key', 'access_token', 'password', 'secret'}:
                    raise ValueError('Inline credentials are forbidden; use api_key_env')
                reject_secrets(item)
        elif isinstance(value, list):
            for item in value:
                reject_secrets(item)
    reject_secrets(raw)
    cfg = merge(yaml.safe_load(Path(__file__).with_name('defaults.yaml').read_text()), raw)
    target = cfg['design']
    for name in ['design_id', 'top', 'clock', 'reset']:
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_$]*', str(target.get(name, ''))):
            raise ValueError(f'design.{name} must be an unescaped identifier')
    def absolute(value):
        text = os.path.expandvars(os.path.expanduser(str(value)))
        if re.search(r'\$\{?[A-Za-z_]', text):
            raise ValueError(f'Unset environment variable in path: {text}')
        resolved = Path(text)
        return str((path.parent / resolved).resolve()) if not resolved.is_absolute() else str(resolved)
    if not isinstance(target.get('rtl_files'), list) or not target['rtl_files']:
        raise ValueError('design.rtl_files must be a non-empty ordered list')
    for field in ['rtl_files', 'include_dirs']:
        target[field] = [absolute(p) for p in target.get(field, [])]
        for item in target[field]:
            if not Path(item).exists():
                raise FileNotFoundError(item)
    target.setdefault('validation_scope', 'full_cpu')
    target.setdefault('role', 'USER_DESIGN')
    target.setdefault('reset_active_low', True)
    spec = target.get('spec', {})
    if spec.get('local_path'):
        spec['local_path'] = absolute(spec['local_path'])
        if not Path(spec['local_path']).is_file():
            raise FileNotFoundError(spec['local_path'])
    if spec.get('download_cache_path'):
        spec['download_cache_path'] = absolute(spec['download_cache_path'])
    spec.setdefault('source_url', 'local:specification')
    spec.setdefault('repository_revision', 'local')
    spec.setdefault('repository_path', Path(spec.get('local_path', 'spec.md')).name)
    spec.setdefault('target_module', target['top'])
    spec.setdefault('line_ranges', [[1, 1000000]])
    target['spec'] = spec
    for key, env in [('base_url', 'LLM_BASE_URL'), ('model', 'LLM_MODEL')]:
        if os.environ.get(env):
            cfg['llm'][key] = os.environ[env]
    if cfg['llm']['provider'] not in {'openai-compatible', 'qwen', 'deepseek'}:
        raise ValueError('llm.provider must be openai-compatible, qwen or deepseek')
    formal = cfg['formal']
    executable = os.environ.get('JASPERGOLD_BIN', formal['executable'])
    formal['executable'] = shutil.which(executable) or absolute(executable)
    if formal.get('license_file'):
        formal['license_file'] = absolute(formal['license_file'])
    cfg['design_flow']['designs'] = [target]
    return cfg


def require_llm(cfg):
    llm = cfg['llm']
    if 'your-provider.example' in llm['base_url'] or llm['model'] == 'your-model-name':
        raise ValueError('Set LLM_BASE_URL and LLM_MODEL, or configure llm.base_url/model')
    if not os.environ.get(llm['api_key_env']):
        raise ValueError('Missing API credential environment variable: '+llm['api_key_env'])


def require_formal(cfg):
    executable = cfg['formal']['executable']
    if not Path(executable).is_file() or not os.access(executable, os.X_OK):
        raise ValueError('Set JASPERGOLD_BIN to an executable JasperGold installation')
