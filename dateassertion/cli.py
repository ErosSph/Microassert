"""Public CLI: portable inputs, explicit costly stages, preserved evidence."""
import argparse
from collections import Counter
from copy import deepcopy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import sys
import time

from .config import load_config, require_formal, require_llm
from .ir.schema import dump_json, properties_from_dict


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def design_artifacts(cfg):
    from .rtl_frontend.parser import parse_rtl
    from .rtl_frontend.semantic_graph import build_semantic_graph
    from .rtl_frontend.hierarchical_design import build_hierarchical_design_map
    target = cfg['design']
    design = parse_rtl(target['rtl_files'], include_dirs=target['include_dirs'])
    if target['top'] not in design.module_signals:
        raise ValueError('Configured top not present in parsed RTL: '+target['top'])
    graph = build_semantic_graph(design)
    hierarchy = build_hierarchical_design_map(design, graph, target['top'], include_dirs=target['include_dirs'])
    return design, graph, hierarchy


def render(properties, design, target, folder):
    from .generators.sva_generator import generate_sva
    dump_json(folder/'properties.json', properties)
    generate_sva(properties, design.signals, target['top'], folder/'assertions.sv',
                 clock=target['clock'], reset=target['reset'], module_signals=design.module_signals)


def analyze(cfg, output, experimental=False):
    from .pipeline.semantic_slicing import build_verification_regions
    from .pipeline.architecture_contracts import compile_architecture_contracts
    design, graph, hierarchy = design_artifacts(cfg)
    target = cfg['design']
    reset = ('!' if target['reset_active_low'] else '')+target['reset']
    regions = build_verification_regions(design, graph, hierarchy)
    reachable = {i['module'] for i in hierarchy['instances']}
    regions['regions'] = [r for r in regions['regions'] if r['module'] in reachable]
    if experimental:
        from .experimental.region_binding import generate
        from .experimental.region_templates import resolved_library
        from .rtl_frontend.graph_patterns import detect_graph_patterns
        matches = detect_graph_patterns(graph)
        matches['patterns'] = [p for p in matches['patterns'] if p['module'] in reachable]
        result = generate(design, graph, matches, target['clock'], reset)
        properties = result.pop('properties')
        for key, value in result.items():
            dump_json(output/(key+'.json'), value)
        dump_json(output/'knowledge_base.json', resolved_library())
    else:
        properties, bindings, metadata, audit = compile_architecture_contracts(design, graph, regions, reset)
        dump_json(output/'regions.json', regions)
        dump_json(output/'binding_audit.json', audit)
    design.save(output/'rtl_structure.json')
    dump_json(output/'typed_semantic_graph.json', graph)
    dump_json(output/'hierarchy.json', hierarchy)
    render(properties, design, target, output)
    summary = {'mode': 'experimental-region-templates' if experimental else 'structural-analysis',
               'properties': len(properties), 'llm_used': False, 'formal_run': False,
               'spec_conformance_claimed': False, 'deduplicated': False}
    dump_json(output/'summary.json', summary)
    return summary


def fingerprint(cfg):
    target = cfg['design']
    paths = set()
    for item in target['rtl_files']+target['include_dirs']:
        p = Path(item)
        paths.update([p] if p.is_file() else [x for x in p.rglob('*') if x.suffix in {'.v','.sv','.vh','.svh'}])
    if target['spec'].get('local_path'):
        paths.add(Path(target['spec']['local_path']))
    package = Path(__file__).parent
    code = {str(p.relative_to(package)): sha(p) for p in package.rglob('*')
            if p.is_file() and p.suffix in {'.py','.txt','.json','.yaml','.tcl'}}
    doc = {'config': cfg, 'inputs': {str(p):sha(p) for p in sorted(paths)}, 'implementation': code}
    return hashlib.sha256(json.dumps(doc, sort_keys=True).encode()).hexdigest()


def export_raw(cfg, output, rounds):
    target = cfg['design']
    initial = output/'initial'/target['design_id']
    sources = [(0, 'local', initial/'local_candidates.json'),
               (0, 'composition', initial/'composition_properties.json')]
    for i in range(1, rounds+1):
        root = output/'feedback'/'rounds'/f'round_{i:02d}'
        sources += [(i, kind, root/kind/'generated_properties.json') for kind in ['local','composition']]
    rows, provenance = [], []
    for number, kind, path in sources:
        for index, row in enumerate(read(path)):
            rows.append(row)
            provenance.append({'round': number, 'kind': kind, 'source': str(path),
                               'index': index, 'property_id': row['property_id'], 'source_sha256': sha(path)})
    if len({p['property_id'] for p in rows}) != len(rows):
        raise RuntimeError('Repeated property labels; refusing to silently discard records')
    design, _, _ = design_artifacts(cfg)
    folder = output/'raw_exports'/f'round_{rounds:02d}'
    render(properties_from_dict(rows), design, target, folder)
    dump_json(folder/'provenance.json', provenance)
    manifest = {'generated': len(rows), 'deduplicated': False, 'proof_status_filter': None,
                'counts': dict(Counter(p['kind'] for p in provenance)), 'sva_sha256':sha(folder/'assertions.sv')}
    dump_json(folder/'manifest.json', manifest)
    return manifest


def run_flow(cfg, output, rounds):
    from .pipeline.design_flow import _run_design
    from .pipeline.feedback_loop import run_feedback
    require_llm(cfg)
    require_formal(cfg)
    if not cfg['design']['spec'].get('local_path'):
        raise ValueError('Full flow requires design.spec.local_path')
    if rounds < 0:
        raise ValueError('--rounds must be nonnegative')
    target = cfg['design']
    identity = fingerprint(cfg)
    marker = output/'input_identity.json'
    if marker.exists() and read(marker)['sha256'] != identity:
        raise RuntimeError('Inputs/config/code changed; use a fresh output directory')
    dump_json(marker, {'sha256':identity})
    initial = output/'initial'/target['design_id']
    complete = initial/'completed.json'
    if not complete.exists():
        _run_design(target, cfg, output/'initial')
        dump_json(complete, {'status':'COMPLETE'})
    if rounds:
        run_feedback(target, cfg, initial, output/'feedback', rounds=rounds)
    return export_raw(cfg, output, rounds)


def prove(cfg, properties_file, output):
    from .formal.jaspergold import JasperGoldRunner
    require_formal(cfg)
    design, _, _ = design_artifacts(cfg)
    props = properties_from_dict(read(properties_file))
    render(props, design, cfg['design'], output)
    formal = {**cfg['formal'], **{k:cfg['design'][k] for k in ['clock','reset','reset_active_low','include_dirs']}}
    result = JasperGoldRunner().run(design.files, str(output/'assertions.sv'), cfg['design']['top'], props, output/'formal', formal)
    dump_json(output/'formal_results.json', result)
    return {'status': result.status, 'summary':result.summary}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for action in ['doctor','check-llm','analyze','run','formal','export','measure','collect']:
        p = sub.add_parser(action)
        p.add_argument('--config', required=True)
        if action not in {'doctor','check-llm'}:
            p.add_argument('--output', required=True)
        if action in {'formal','measure'}:
            p.add_argument('--properties', required=True)
        if action == 'analyze':
            p.add_argument('--region-templates', action='store_true', help='Experimental Region-bound knowledge packs')
        if action in {'run','export'}:
            p.add_argument('--rounds', type=int, help='Feedback cutoff; 0 means initial only')
    args = parser.parse_args(argv)
    owns_run = False
    try:
        cfg = load_config(args.config)
        if args.command == 'doctor':
            print(json.dumps({'python':sys.version.split()[0], 'rtl_inputs_exist':True,
                  'llm_key_present':bool(os.environ.get(cfg['llm']['api_key_env'])),
                  'jasper_executable_found':Path(cfg['formal']['executable']).is_file()}, indent=2))
            return 0
        if args.command == 'check-llm':
            from .llm.client import DeepSeekClient
            from .pipeline.contract_validation import _llm_config
            require_llm(cfg)
            result, meta = DeepSeekClient(_llm_config(cfg['llm'])).complete_json('Return JSON only.', 'Return {"ok": true}.')
            if result != {'ok':True}:
                raise ValueError('Provider did not return the requested JSON object')
            print(json.dumps({'ok':True, 'model':meta.get('response_model'), 'usage':meta.get('usage')}))
            return 0
        output = Path(args.output).resolve()
        output.mkdir(parents=True, exist_ok=True)
        with (output/'.run.lock').open('a') as lock:
            fcntl.flock(lock.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            if args.command in {'analyze','formal','measure'} and (output/'status.json').exists():
                raise ValueError('Preserving existing artifacts; use a new output directory')
            owns_run = True
            dump_json(output/'status.json', {'stage':args.command, 'status':'RUNNING', 'pid':os.getpid()})
            dump_json(output/'resolved_config.json', cfg)
            if args.command == 'analyze':
                result = analyze(cfg, output, args.region_templates)
            elif args.command in {'run','export'}:
                rounds = args.rounds if args.rounds is not None else cfg['feedback']['feedback_rounds']
                result = (run_flow if args.command == 'run' else export_raw)(cfg, output, rounds)
            elif args.command == 'formal':
                result = prove(cfg, args.properties, output)
            elif args.command == 'measure':
                from .pipeline.native_measurements import run_measurements
                require_formal(cfg)
                design, _, _ = design_artifacts(cfg)
                props = properties_from_dict(read(args.properties))
                render(props, design, cfg['design'], output)
                result = run_measurements(design, cfg['design'], cfg, output/'assertions.sv', props, output/'measurements')
            else:
                from .pipeline.native_measurements import collect_measurements
                result = collect_measurements(output/'measurements')
            failed = args.command == 'formal' and result.get('status') == 'ERROR'
            dump_json(output/'status.json', {'stage':args.command, 'status':'FAILED' if failed else 'COMPLETE', 'finished_unix':time.time()})
            print(json.dumps(result, default=str, indent=2))
            return 1 if failed else 0
    except Exception as exc:
        # Never echo credentials from a provider/proxy exception to an artifact.
        message = str(exc)
        for name, value in os.environ.items():
            if value and ('API_KEY' in name or 'TOKEN' in name):
                message = message.replace(value, '[REDACTED]')
        if owns_run:
            dump_json(output/'error.json', {'stage':args.command, 'error':message})
            dump_json(output/'status.json', {'stage':args.command, 'status':'FAILED', 'finished_unix':time.time()})
        print(type(exc).__name__+': '+message, file=sys.stderr)
        return 1
