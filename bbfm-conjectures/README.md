# BBFM conjectures on subsum polynomials

Lean proofs of **revised BBFM Conjecture 6 for every `n ≥ 2`** and
**Conjecture 4 for every `n ≥ 2^(10^8)`**, building on the work of
Ballantine, Beck, Feigon and Maurischat and
[Axiom Math](https://arxiv.org/html/2605.21718v2).

## Results

| Conjecture | Result | Lean theorem |
| --- | --- | --- |
| Revised BBFM 6 | **Resolved:** binary-partition numerator unimodality for every `n ≥ 2`. | [`BBFM.revisedConjecture6`](BBFM/Results.lean) |
| BBFM 4 | Denominator log-concavity for every `n ≥ 2^(10^8)`, strict at internal coefficients. The full conjecture remains open. | [`BBFM.conjecture4_large_n`](BBFM/Results.lean) |
| Revised BBFM 7 | Binary-numerator log-concavity at both positions immediately beside the center for every `n ≥ 6`. The full conjecture remains open. | [`BBFM.binaryLogConcavityBesideCenter`](BBFM/Results.lean) |

The conjecture numbering follows the
[revised BBFM paper](https://arxiv.org/html/2605.10512v2).
Axiom's paper leaves binary unimodality and denominator log-concavity open.
Its `n = 4` counterexample refutes the original binary **log-concavity** claim;
it does not refute unimodality. This repository resolves the unimodality
question and proves the stated large-`n` range of the denominator conjecture.

See [BBFM/Results.lean](BBFM/Results.lean) for the precise statements and
[attribution](docs/ATTRIBUTION.md) for the mathematical sources and upstream code.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
python3 scripts/verify.py --clean
```

The project pins Lean **4.34.0-rc2** and Mathlib commit
`bbcd1968ee6950abe88b85dba6995da346c4b2a8`. The verification script requires
Python 3.10 or later, builds all modules, and checks theorem dependencies
against `propext`, `Classical.choice`, and `Quot.sound`. Output is written to
`.verification/`. You can also build directly with `lake build`.

```lean
import BBFM.Results

#check BBFM.revisedConjecture6
#check BBFM.conjecture4_large_n
#check BBFM.binaryLogConcavityBesideCenter
```

## Contents

- [`BBFM/Results.lean`](BBFM/Results.lean): public theorem statements.
- [`BBFM/Binary/`](BBFM/Binary/): binary numerator proofs.
- [`BBFM/Denominator/`](BBFM/Denominator/): denominator proofs.
- [`BBFM/AxiomAudit.lean`](BBFM/AxiomAudit.lean): theorem dependency audit.
- [`docs/ATTRIBUTION.md`](docs/ATTRIBUTION.md): sources, credits, and licensing.

## License

[MIT](LICENSE). Credited Axiom Math code retains its
[upstream MIT license](LICENSES/AxiomMath-MIT.txt).
