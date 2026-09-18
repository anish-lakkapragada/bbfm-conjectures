import BBFM.Denominator.Bridge.AxiomC2Roots

/-! New bridge work. All referenced gcd and partition definitions are the
unchanged definitions from Axiom's pinned C2 solution. -/

open Polynomial Finset
noncomputable section
namespace DenominatorBridge

theorem denReduced_ne_zero (n : ℕ) (hn : 1 ≤ n) : denReduced n ≠ 0 := by
  intro h
  have he := denStar_eq_denReduced_mul_gCommon n hn
  rw [h, zero_mul] at he
  exact denStar_ne_zero n he

theorem denReduced_map_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (denReduced n).map (algebraMap ℚ ℂ) ≠ 0 := by
  exact Polynomial.map_ne_zero (denReduced_ne_zero n hn)

/-- Exact multiplicity of each even-order root in the original reduced
denominator. This does not assert log-concavity. -/
theorem rootMultiplicity_denReduced {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    Polynomial.rootMultiplicity α ((denReduced n).map (algebraMap ℚ ℂ)) = n / s := by
  have hn : 1 ≤ n := hs.trans hsn
  have hM : n / s ≤ cC α n := by
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (n / i))
      (s_mem_badSet hs hsn hord.1 hord.2)
  have he := congrArg (Polynomial.map (algebraMap ℚ ℂ))
    (denStar_eq_denReduced_mul_gCommon n hn)
  rw [Polynomial.map_mul] at he
  have hne : (denReduced n).map (algebraMap ℚ ℂ) *
      (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := by
    exact mul_ne_zero (denReduced_map_ne_zero n hn) (gCommon_map_ne_zero n hn)
  have hm := congrArg (Polynomial.rootMultiplicity α) he
  rw [rootMultiplicity_denStar, Polynomial.rootMultiplicity_mul hne,
    rootMultiplicity_gCommon α s hs hord hsn] at hm
  omega

end DenominatorBridge

#print axioms DenominatorBridge.rootMultiplicity_denReduced
