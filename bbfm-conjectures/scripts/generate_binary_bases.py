"""Generate data-only candidates for Lean's exact finite-base checker.

Python arithmetic discovers the lists. Acceptance depends on separately
compiling each generated Lean theorem; no Python output is a proof.
"""
from functools import lru_cache
from math import comb
from pathlib import Path
import hashlib
import json
import argparse

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.verification/generated-bases'


@lru_cache(None)
def numerator(n):
    if n == 0:
        return (1,)
    if n % 2:
        return numerator(n - 1)
    half = n // 2
    q = 2 * (half & -half)
    prev, small = numerator(n - 2), numerator(half)
    result = [0] * max(len(prev) + 2 * (q - 1), n + 2 * (len(small) - 1) + 1)
    for j in range(q):
        for i, a in enumerate(prev):
            result[i + 2 * j] += a
    for j, a in enumerate(small):
        for i in range(n + 1):
            result[2 * j + i] += a * comb(n, i)
    return tuple(result)


def residual(p):
    c = (len(p) - 1) // 2
    amplitude = sum(a * (-1) ** i for i, a in enumerate(p))
    r = []
    previous = 0
    for i, a in enumerate(p):
        previous = a - (amplitude * (-1) ** c if i == c else 0) - previous
        r.append(previous)
    assert r[-1] == 0
    return r[:-1]


def lean_list(xs):
    return '[' + ', '.join(map(str, xs)) + ']'


def generate(check=False):
    manifest = []
    if not check:
        OUT.mkdir(parents=True, exist_ok=True)
    for n in range(2, 97, 2):
        tag = f'{n:03d}'
        m, p = n // 2, numerator(n)
        c = (len(p) - 1) // 2
        assert p == p[::-1]
        assert all(p[k] <= p[k + 1] for k in range(c))
        assert sum(p) < 2 ** 256
        text = f'''import BBFM.Binary.Unimodality.ListShapeChecks

    open Polynomial BinaryResearch BinaryShape
    namespace BinaryCertificate.Bases
    set_option maxRecDepth 1000000
    set_option maxHeartbeats 0

    def p{tag} : List ℕ := {lean_list(p)}

    theorem numerator{tag} : listPoly p{tag} = numB {n} := by
      exact numB_eq_of_packed {m} (2 ^ 256) p{tag}
        (by decide +kernel) (by decide +kernel) (by decide +kernel)

    theorem shape{tag} : HasShape (numB {n}) (2 * center {n}) := by
      rw [← numerator{tag}]
      exact listPoly_shape p{tag} (2 * center {n})
        (by decide +kernel) (by decide +kernel) (by decide +kernel)

    '''
        if n >= 10:
            r = residual(p)
            assert all(a >= 0 for a in r)
            assert r == r[::-1]
            assert all(r[k] <= r[k + 1] for k in range((len(r) - 1) // 2))
            text += f'''def r{tag} : List ℕ := {lean_list(r)}

    theorem residual{tag} : listPoly r{tag} = BinaryResearch.residual {n} := by
      exact residual_eq_of_check {n} p{tag} r{tag} numerator{tag} (by decide +kernel)

    theorem residualShape{tag} : HasShape (BinaryResearch.residual {n}) (2 * center {n} - 1) := by
      rw [← residual{tag}]
      exact listPoly_shape r{tag} (2 * center {n} - 1)
        (by decide +kernel) (by decide +kernel) (by decide +kernel)

    '''
        if n >= 48:
            lo = c - (n + 2)
            assert lo >= 1
            assert all(p[k] - p[k - 1] >= 3 ** n for k in range(lo, c + 1))
            text += f'''theorem slopes{tag} (k : ℕ)
        (hklo : center {n} - ({n} + 2) ≤ k) (hkhi : k ≤ center {n}) :
        (3 : ℤ) ^ {n} ≤ (numB {n}).coeff k - (numB {n}).coeff (k - 1) := by
      rw [← numerator{tag}]
      exact_mod_cast listPoly_slope p{tag} (center {n} - ({n} + 2)) (center {n}) (3 ^ {n})
        (by decide +kernel) (by decide +kernel) k hklo hkhi

    '''
        text += f'end BinaryCertificate.Bases\n\n#print axioms BinaryCertificate.Bases.shape{tag}\n'
        if n >= 10:
            text += f'#print axioms BinaryCertificate.Bases.residualShape{tag}\n'
        if n >= 48:
            text += f'#print axioms BinaryCertificate.Bases.slopes{tag}\n'
        # Match the indentation normalization used for the accepted sources.
        text = ''.join(line[4:] if line.startswith('    ') else line
                       for line in text.splitlines(keepends=True))
        source = (ROOT / 'BBFM/Binary/Unimodality/Bases' if check else OUT) / f'N{tag}.lean'
        if check:
            if source.read_text() != text:
                raise SystemExit(f'Regenerated certificate differs: {source}')
        else:
            source.write_text(text)
        manifest.append({'n': n, 'module': f'BBFM.Binary.Unimodality.Bases.N{tag}', 'degree': 2 * c,
                         'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()})

    if check:
        print(f'All {len(manifest)} regenerated certificates match the checked-in Lean sources.')
    else:
        (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
        print(f'Generated {len(manifest)} candidate modules in {OUT}. Lean compilation is required for acceptance.')


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Compare regenerated certificates without modifying proof sources")
    generate(check=parser.parse_args().check)
