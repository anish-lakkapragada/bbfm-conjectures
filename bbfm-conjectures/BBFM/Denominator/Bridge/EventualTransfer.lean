import BBFM.Denominator.Bridge.CoefficientAlignment
import BBFM.Denominator.Analytic.Eventual

open Polynomial
noncomputable section
namespace DenominatorBridge

lemma productR_eq_den (n : ℕ) : productR n = DenominatorResearch.den n := rfl

/-- The eventual product theorem for the monic gcd-defined denominator in Axiom Math's source. -/
theorem source_den_logconcave (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hlarge : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ Nat.log 2 n + 1) :
    (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) ≤
      (denReduced n).coeff k ^ 2 := by
  apply (source_logconcavity_iff_product n k hn).mpr
  rw [productR_eq_den]
  exact DenominatorResearch.den_logconcave n k (by omega) hk hlarge

theorem source_den_logconcave_of_pow_le (n k E : ℕ) (hk : 1 ≤ k)
    (hE : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ E) (hlarge : 2 ^ E ≤ n) :
    (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) ≤
      (denReduced n).coeff k ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) E) hlarge
  apply (source_logconcavity_iff_product n k (by omega)).mpr
  rw [productR_eq_den]
  exact DenominatorResearch.den_logconcave_of_pow_le n k E hk hE hlarge

/-- A single cutoff controls every coefficient of the source denominator. -/
theorem source_den_eventually_logconcave :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
      (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) ≤
        (denReduced n).coeff k ^ 2 := by
  refine ⟨2 ^ (100 * ((10 : ℕ) ^ 100) ^ 2), ?_⟩
  intro n hn k hk
  exact source_den_logconcave_of_pow_le n k _ hk le_rfl hn

end DenominatorBridge

#print axioms DenominatorBridge.source_den_logconcave
#print axioms DenominatorBridge.source_den_eventually_logconcave
