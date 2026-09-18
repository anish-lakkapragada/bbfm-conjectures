# Attribution

## Mathematical sources

Cristina Ballantine, George Beck, Brooke Feigon and Kathrin Maurischat,
[*Reciprocals of Subsum Polynomials*](https://arxiv.org/html/2605.10512v2),
formulated the conjectures and proved the structural denominator product formula.
The revised numbering distinguishes Conjecture 6 (binary unimodality for
`n ≥ 2`) from Conjecture 7 (binary log-concavity for `n ≥ 6`). Conjecture 4
concerns denominator log-concavity outside the exceptions `3, 5, 6, 7`.

Evan Chen, Ken Ono and Jujian Zhang,
[*Reciprocals of Partition Polynomials*](https://arxiv.org/html/2605.21718v2),
proved several BBFM conjectures. Their
[Table 1](https://arxiv.org/html/2605.21718v2#S1.T1) and
[§1.2.2](https://arxiv.org/html/2605.21718v2#S1.SS2.SSS2)
leave the unimodality question open: the `n = 4` counterexample disproves
log-concavity, while its coefficient sequence is unimodal. Table 1 also leaves
Conjecture 4 open. The results here resolve revised Conjecture 6 and establish
Conjecture 4 for the stated range `n ≥ 2^(10^8)`.

## Axiom Math code

This repository builds on
[AxiomMath/PartitionPolynomial](https://github.com/AxiomMath/PartitionPolynomial/tree/b2a9e8d75cc76e5c432f15f668c18826a9abab80),
pinned at commit `b2a9e8d75cc76e5c432f15f668c18826a9abab80`.

- [`BBFM/Binary/Source.lean`](../BBFM/Binary/Source.lean) contains the binary
  partition definitions from the upstream
  [Conjecture 5 solution](https://github.com/AxiomMath/PartitionPolynomial/blob/b2a9e8d75cc76e5c432f15f668c18826a9abab80/PartitionPolynomial/Conjecture5/solution.lean).
  In particular, `numB` is the literal finite sum over binary partitions.
- [`BBFM/Binary/Symmetry.lean`](../BBFM/Binary/Symmetry.lean) adapts the
  upstream weighted-multiplicity identity.
- [`BBFM/Denominator/Bridge/AxiomC2Roots.lean`](../BBFM/Denominator/Bridge/AxiomC2Roots.lean)
  contains the source definitions and proof excerpt through
  `rootMultiplicity_gCommon` from the upstream
  [Conjecture 2 solution](https://github.com/AxiomMath/PartitionPolynomial/blob/b2a9e8d75cc76e5c432f15f668c18826a9abab80/PartitionPolynomial/Conjecture2/solution.lean).

These definitions and lemmas are credited to Axiom Math. Its copyright notice
and MIT license are retained in
[`LICENSES/AxiomMath-MIT.txt`](../LICENSES/AxiomMath-MIT.txt).
