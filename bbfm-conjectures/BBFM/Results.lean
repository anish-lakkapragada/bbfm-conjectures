import BBFM.Binary.AllUnimodal
import BBFM.Binary.SourceCentralLCFinite
import BBFM.Denominator.MomentEventualSource
import BBFM.Denominator.MomentSourceInterior
import BBFM.Denominator.SourceFourEdges
import BBFM.Denominator.Bridge.FiniteTransfer

/-! Public statements for the BBFM results. The conjectures defined at the end
remain open; the preceding theorems specify the proved ranges explicitly. -/

open Polynomial

namespace BBFM

/-- Revised BBFM Conjecture 6: the actual binary numerator is unimodal for
every n >= 2, including the zero coefficient tail. -/
theorem revisedConjecture6 (n : ℕ) (hn : 2 ≤ n) :
    BinaryResearch.CoeffUnimodal (numB n) :=
  BinaryResearch.binary_numerator_unimodal n hn

/-- Two coefficient positions of revised Conjecture 7, for every n >= 6.
This is a partial result, with the two positions explicit. -/
theorem binaryLogConcavityBesideCenter (n : ℕ) (hn : 6 ≤ n) :
    (numB n).coeff (BinaryResearch.center n - 2) *
        (numB n).coeff (BinaryResearch.center n) ≤
      ((numB n).coeff (BinaryResearch.center n - 1)) ^ 2 ∧
    (numB n).coeff (BinaryResearch.center n) *
        (numB n).coeff (BinaryResearch.center n + 2) ≤
      ((numB n).coeff (BinaryResearch.center n + 1)) ^ 2 :=
  BinaryResearch.source_adjacent_to_center_logconcavity_all n hn

/-- BBFM Conjecture 4 above the explicit cutoff 2^(10^8).
The denominator is the actual monic common-gcd quotient over the rationals. -/
theorem conjecture4_large_n (n : ℕ) (hn : 2 ^ ((10 : ℕ) ^ 8) ≤ n) :
    DenominatorBridge.SourceDenLC n := by
  intro k hk
  exact BBFMMoment.source_den_logconcave_of_pow_le n k ((10 : ℕ) ^ 8) hk le_rfl hn

/-- The large-n denominator inequality is strict at every internal index. -/
theorem conjecture4_large_n_strict (n k : ℕ)
    (hn : 2 ^ ((10 : ℕ) ^ 8) ≤ n) (hk : 1 ≤ k)
    (hkd : k < (denReduced n).natDegree) :
    (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) <
      (denReduced n).coeff k ^ 2 :=
  BBFMMoment.source_den_strict_of_pow_le n k ((10 : ℕ) ^ 8) hk hkd le_rfl hn

/-- Complete source-denominator classification on 1 <= n <= 32. -/
theorem conjecture4_through_32 (n : ℕ) (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    DenominatorBridge.SourceDenLC n ↔ n ≠ 3 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 :=
  DenominatorBridge.source_denominator_classification_through_32 n hn hn32

/-- OPEN: full binary log-concavity for n >= 6, revised BBFM Conjecture 7. -/
def RevisedConjecture7 : Prop := BinaryResearch.CorrectedBinaryLogConcavity

/-- OPEN: denominator log-concavity at every positive n outside the four
exceptional sizes. -/
def Conjecture4 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≠ 3 → n ≠ 5 → n ≠ 6 → n ≠ 7 →
    DenominatorBridge.SourceDenLC n

end BBFM

#print axioms BBFM.revisedConjecture6
#print axioms BBFM.binaryLogConcavityBesideCenter
#print axioms BBFM.conjecture4_large_n
#print axioms BBFM.conjecture4_large_n_strict
#print axioms BBFM.conjecture4_through_32
