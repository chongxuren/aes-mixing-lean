#!/usr/bin/env python3
"""Regenerate the finite Lean certificates, then verify their source identities.

Generation is deterministic integer arithmetic. Lean's kernel checks the proofs;
successful generation or matching file hashes is not a new proof check.
"""
import argparse
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import assembly
import rows

HERE = Path(__file__).resolve().parent
PREFIX = 'AES8/Estimates/Word/'


def row_paths(alpha):
    if alpha == 13:
        pairs = ['PaperSharpEntriesPairB%d' % b for b in range(1, 256)]
        name = 'PaperSharpEntriesRow13'
    else:
        pairs = ['PaperSharpEntriesPairA%03dB%03d' % (alpha, b) for b in range(1, 256)]
        name = 'PaperSharpEntriesRowA%03d' % alpha
    names = pairs + [name, name + 'Interface'] + [name + 'Block%02d' % b for b in range(16)]
    return [PREFIX + n + '.lean' for n in names]


def file_identity(path):
    digest = hashlib.sha256()
    size = 0
    with path.open('rb') as source:
        for data in iter(lambda: source.read(1024 * 1024), b''):
            digest.update(data)
            size += len(data)
    return size, digest.hexdigest()


def verify_group(root, paths, expected):
    digest = hashlib.sha256(b'aes8-source-group-v1\n')
    total = 0
    for name in sorted(paths):
        size, sha = file_identity(root / name)
        digest.update((json.dumps([name, size, sha], separators=(',', ':')) + '\n').encode('utf-8'))
        total += size
    actual = {'files': len(paths), 'bytes': total, 'sha256': digest.hexdigest()}
    if actual != expected:
        raise ValueError('Generated source identity differs: expected %s, received %s' % (expected, actual))
    return actual


def write_source(root, name, data):
    if not name.startswith(PREFIX) or not name.endswith('.lean') or '..' in Path(name).parts:
        raise ValueError('Unexpected generated path: ' + name)
    target = root / name
    if target.is_symlink() or any(p.is_symlink() for p in target.parents):
        raise ValueError('Refusing source symlink: ' + name)
    if target.exists():
        if target.read_bytes() != data:
            raise ValueError('Refusing to overwrite different source: ' + name)
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix='.aes8-source-', dir=str(target.parent))
    try:
        with os.fdopen(fd, 'wb') as output:
            output.write(data)
        # Hard linking installs without overwriting a file created concurrently.
        try:
            os.link(temporary, str(target))
        except FileExistsError:
            if target.read_bytes() != data:
                raise ValueError('Concurrent conflicting source: ' + name)
    finally:
        os.unlink(temporary)


def generate_row(task):
    alpha, project, executable, expected = task
    root = Path(project)
    paths = row_paths(alpha)
    if all((root / p).is_file() for p in paths):
        verify_group(root, paths, expected)
        return alpha, 'verified existing'
    with tempfile.TemporaryDirectory(prefix='aes8-row-%03d-' % alpha) as temporary:
        data = Path(temporary) / 'transforms.jsonl'
        subprocess.check_call([executable, str(alpha), str(data)])
        def write(name, contents):
            write_source(root, name, contents)
        if alpha == 13:
            rows.emit_pairs(alpha, data, write, legacy_names=True)
            assembly.emit_pilot_wrappers(write)
        else:
            rows.emit_row(alpha, data, write)
    verify_group(root, paths, expected)
    return alpha, 'generated and verified'


def selected_rows(value):
    try:
        result = sorted(set(int(part) for part in value.split(',')))
    except ValueError:
        raise argparse.ArgumentTypeError('Use comma-separated integers from 1 to 255.')
    if not result or any(a < 1 or a > 255 for a in result):
        raise argparse.ArgumentTypeError('Every row must lie between 1 and 255.')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1, help='Independent row processes (default: 1).')
    parser.add_argument('--rows', type=selected_rows, default=list(range(1, 256)),
                        help='Optional comma-separated subset for a partial generation.')
    parser.add_argument('--output', type=Path, default=HERE.parent, help='Project root (default: this checkout).')
    parser.add_argument('--cxx', default=os.environ.get('CXX', 'g++'), help='C++11 compiler with __int128 support.')
    parser.add_argument('--verify-only', action='store_true', help='Check sources without compiling or generating.')
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    root = args.output.resolve()
    expected = json.loads((HERE / 'expected.json').read_text(encoding='utf-8'))
    if expected['schema'] != 'aes8-source-generator/v1':
        raise ValueError('Unknown expected-source format')
    verify_group(root, expected['shared_paths'], expected['shared'])
    if args.verify_only:
        for alpha in args.rows:
            verify_group(root, row_paths(alpha), expected['rows'][str(alpha)])
        verify_group(root, expected['complete_paths'], expected['complete'])
    else:
        compiler = shutil.which(args.cxx)
        if compiler is None:
            raise ValueError('C++ compiler not found: ' + args.cxx)
        with tempfile.TemporaryDirectory(prefix='aes8-generator-') as temporary:
            executable = str(Path(temporary) / 'generate_transforms')
            subprocess.check_call([compiler, '-std=c++11', '-O2', str(HERE / 'generate_transforms.cpp'), '-o', executable])
            tasks = [(a, str(root), executable, expected['rows'][str(a)]) for a in args.rows]
            workers = min(args.jobs, len(tasks))
            with ProcessPoolExecutor(max_workers=workers) as pool:
                remaining = iter(tasks)
                pending = {pool.submit(generate_row, next(remaining)) for _ in range(workers)}
                try:
                    while pending:
                        done, pending = wait(pending, return_when=FIRST_COMPLETED)
                        for future in done:
                            alpha, status = future.result()
                            print('Row %03d: %s' % (alpha, status), flush=True)
                        for _ in done:
                            task = next(remaining, None)
                            if task is not None:
                                pending.add(pool.submit(generate_row, task))
                except BaseException:
                    # Do not start additional rows after a failure. Already-running
                    # rows finish safely before their temporary compiler is removed.
                    for future in pending:
                        future.cancel()
                    raise
            assembly.emit_complete(lambda name, data: write_source(root, name, data))
        verify_group(root, expected['complete_paths'], expected['complete'])
    if len(args.rows) == 255:
        print('All 69,913 certificate source identities verified. Run the documented Lean checks next.')
    else:
        print('Partial source check: %d/255 rows. Run without --rows before checking the full theorem.' % len(args.rows))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print('error: ' + str(error), file=sys.stderr)
        sys.exit(1)
