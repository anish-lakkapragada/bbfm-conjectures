#!/usr/bin/env python3
"""Build every project module with Lake, then record the verified source hashes.

Modules are requested in dependency order to keep memory use bounded. Each
invocation still uses the standard Lake build graph and writes normal artifacts.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    return {p.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.'): p
            for p in [ROOT / 'BBFM.lean', *sorted((ROOT / 'BBFM').rglob('*.lean'))]}


def build_order(files):
    ordered, done, active = [], set(), set()
    def visit(name):
        if name in done:
            return
        if name in active:
            raise RuntimeError(f'Import cycle at {name}')
        active.add(name)
        for line in re.findall(r'^import\s+([^\n]+)', files[name].read_text(), re.M):
            for dep in line.split('--')[0].split():
                if dep.startswith('BBFM'):
                    if dep not in files:
                        raise RuntimeError(f'Missing local import {dep} in {name}')
                    visit(dep)
        active.remove(name)
        done.add(name)
        ordered.append(name)
    visit('BBFM')
    if set(ordered) != set(files):
        raise RuntimeError(f'Unbuilt sources: {set(files) - set(ordered)}')
    return ordered


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--clean', action='store_true', help='Remove only this project build directory first')
    parser.add_argument('--check-only', action='store_true', help='Check source layout and proof mechanisms without building')
    parser.add_argument('--existing-build', action='store_true',
                        help='Verify the existing build directly through Lake, without serial scheduling')
    args = parser.parse_args()
    if args.clean and args.existing_build:
        parser.error('--clean and --existing-build cannot be combined')
    files = sources()
    order = build_order(files)
    for name, path in files.items():
        text = path.read_text()
        if re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\b', text, re.M):
            raise RuntimeError(f'Unaccepted proof mechanism in {name}')
        if '/Users/' in text or 'file://' in text:
            raise RuntimeError(f'Nonportable path in {name}')
    print(f'Source checks passed: {len(files)} modules.', flush=True)
    if args.check_only:
        return
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['LEAN_NUM_THREADS'] = '1'
    report = ROOT / '.verification'
    logs = report / 'logs'
    logs.mkdir(parents=True, exist_ok=True)
    success = report / 'SUCCESS.json'
    success.unlink(missing_ok=True)
    if args.clean:
        import shutil
        shutil.rmtree(ROOT / '.lake/build', ignore_errors=True)
    start = time.monotonic()
    initial_hashes = {p.relative_to(ROOT).as_posix(): digest(p) for p in files.values()}
    config_hashes = {name: digest(ROOT / name) for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
    receipts = []
    scheduled = [] if args.existing_build else order
    for i, name in enumerate(scheduled, 1):
        command = ['lake', 'build', '+' + name]
        print(f'[{i}/{len(order)}] {name}', flush=True)
        tick = time.monotonic()
        log = logs / (name + '.log')
        with log.open('w') as out:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
        elapsed = round(time.monotonic() - tick, 3)
        receipts.append(dict(module=name, command=command, returncode=result.returncode,
                             seconds=elapsed, log=log.relative_to(ROOT).as_posix()))
        (report / 'modules.json').write_text(json.dumps(receipts, indent=2) + '\n')
        if result.returncode:
            print(log.read_text()[-16000:], flush=True)
            raise SystemExit(result.returncode)
        print(f'  passed ({elapsed}s)', flush=True)
    # Check the ordinary public build entry point as well.
    result = subprocess.run(['lake', 'build'], cwd=ROOT, env=env, capture_output=True, text=True)
    (report / 'lake-build.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        print(result.stdout + result.stderr)
        raise SystemExit(result.returncode)
    # Force the theorem audit command to run, even on a resumed build.
    audit = subprocess.run(['lake', 'env', 'lean', 'BBFM/AxiomAudit.lean'],
                           cwd=ROOT, env=env, capture_output=True, text=True)
    audit_text = audit.stdout + audit.stderr
    (report / 'axiom-audit.log').write_text(audit_text)
    match = re.search(r'BBFM_AXIOM_AUDIT: (\d+) theorems checked', audit_text)
    if audit.returncode or not match:
        print(audit_text)
        raise SystemExit(audit.returncode or 1)
    for path, expected in initial_hashes.items():
        if digest(ROOT / path) != expected:
            raise RuntimeError(f'Source changed during verification: {path}')
    for path, expected in config_hashes.items():
        if digest(ROOT / path) != expected:
            raise RuntimeError(f'Build configuration changed during verification: {path}')
    record = dict(complete=True, modules=len(files), theorems_audited=int(match[1]),
                  standard_axioms=['propext', 'Classical.choice', 'Quot.sound'],
                  fresh_project_build=args.clean,
                  existing_build_checked=args.existing_build,
                  completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  elapsed_seconds=round(time.monotonic() - start, 3),
                  sources=initial_hashes, configuration=config_hashes)
    success.write_text(json.dumps(record, indent=2) + '\n')
    print(f'VERIFIED: {len(files)} modules, {match[1]} theorems; {record["elapsed_seconds"]} seconds.', flush=True)
    print(f'Receipt: {success}', flush=True)


if __name__ == '__main__':
    main()
