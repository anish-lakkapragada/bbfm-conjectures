import BBFM.Denominator.Bridge.EventualTransfer
import BBFM.Denominator.Bridge.Finite32

open Polynomial
noncomputable section
namespace DenominatorBridge

def SourceDenLC (n : ℕ) : Prop := ∀ k : ℕ, 1 ≤ k →
  (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) ≤
    (denReduced n).coeff k ^ 2

theorem source_DenLC_iff (n : ℕ) (hn : 1 ≤ n) : SourceDenLC n ↔ C4Search.DenLC n := by
  constructor
  · intro h k hk
    have hh := (source_logconcavity_iff_product n k hn).mp (h k hk)
    simpa only [productR_eq_den] using hh
  · intro h k hk
    apply (source_logconcavity_iff_product n k hn).mpr
    simpa only [productR_eq_den] using h k hk

/-- The finite classification now refers to the literal original rational
denominator, including all coefficient indices and their zero tails. -/
theorem source_denominator_classification_through_32 (n : ℕ)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    SourceDenLC n ↔ n ≠ 3 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 := by
  rw [source_DenLC_iff n hn]
  exact BBFMSeptember.denominator_classification_through_32 n hn32

end DenominatorBridge

#print axioms DenominatorBridge.source_denominator_classification_through_32
