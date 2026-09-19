"""Scan tracked release files without printing any matching secret contents."""
from pathlib import Path
import re
import subprocess
import sys

root=Path(__file__).resolve().parents[1]
result=subprocess.run(['git','ls-files','-z'],cwd=root,capture_output=True,check=True)
paths=[root/name for name in result.stdout.decode().split('\0') if name]
rules={
    'private_key': re.compile(rb'-----BEGIN (?:OPENSSH |RSA |EC )?PRIVATE KEY-----'),
    'api_token': re.compile(rb'\b(?:sk-[A-Za-z0-9_-]{24,}|gh[pousr]_[A-Za-z0-9]{30,})\b'),
    'workstation_path': re.compile(rb'/data2/home/[A-Za-z0-9_]+/'),
}
failures=[]
for path in paths:
    rel=path.relative_to(root)
    if any(p in {'outputs','benchmarks','.venv','.env'} for p in rel.parts):
        failures.append((str(rel),'forbidden_tracked_artifact'))
    if path.is_symlink():
        failures.append((str(rel),'symlink_requires_review'))
        continue
    if not path.is_file():
        continue
    data=path.read_bytes()
    if len(data)>2_000_000:
        failures.append((str(rel),'unexpected_large_file'))
    for name,pattern in rules.items():
        if pattern.search(data):
            failures.append((str(rel),name))
for path,rule in failures:
    print(f'{rule}: {path}')
print(f'Scanned {len(paths)} tracked files; findings={len(failures)}')
sys.exit(bool(failures))
