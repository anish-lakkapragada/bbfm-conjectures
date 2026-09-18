import Mathlib

noncomputable section
namespace DenominatorResearch
open Real intervalIntegral

private def exponentialTailPrimitive (u : ℝ) : ℝ :=
  -100 * (u ^ 2 + 200 * u + 20000) * Real.exp (-u / 100)

private lemma exponentialTailPrimitive_deriv (u : ℝ) :
    HasDerivAt exponentialTailPrimitive (u ^ 2 * Real.exp (-u / 100)) u := by
  have hpoly := (((hasDerivAt_id u).pow 2).add ((hasDerivAt_id u).const_mul 200)).add_const 20000
  have hexp := (((hasDerivAt_id u).neg).div_const 100).exp
  convert! (hpoly.const_mul (-100)).mul hexp using 1 <;> simp only [exponentialTailPrimitive, id_eq, Pi.pow_apply, Pi.add_apply, Pi.neg_apply] <;> ring

/-- The finite exponential tail bound used after Gaussian comparison. -/
theorem integral_square_exponential_tail_le (A B : ℝ) :
    (∫ u in A..B, u ^ 2 * Real.exp (-u / 100)) ≤
      100 * (A ^ 2 + 200 * A + 20000) * Real.exp (-A / 100) := by
  have h := integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ Set.uIcc A B) => exponentialTailPrimitive_deriv u)
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-u / 100))).intervalIntegrable A B)
  rw [h]
  unfold exponentialTailPrimitive
  have hB : 0 ≤ B ^ 2 + 200 * B + 20000 := by nlinarith [sq_nonneg (B + 100)]
  have he := Real.exp_pos (-B / 100)
  nlinarith [mul_nonneg hB he.le]

private lemma numerical_exponential_tail :
    100 * ((100000000 : ℝ) ^ 2 + 200 * 100000000 + 20000) *
      Real.exp (-(100000000 : ℝ) / 100) < 1 / 100 := by
  have he := Real.pow_div_factorial_le_exp 1000000 (by norm_num : (0 : ℝ) ≤ 1000000) 5
  norm_num at he ⊢
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos _)).2
  nlinarith

/-- Uniform finite Gaussian tail bound with the explicit constants in the written proof.
The upper endpoint is arbitrary, so this does not rely on an assumed tail integral estimate. -/
theorem gaussian_second_moment_tail (B : ℝ) (hB : 100000000 ≤ B) :
    (∫ u in (100000000 : ℝ)..B, u ^ 2 * Real.exp (-u ^ 2 / 10000000000)) < 1 / 100 := by
  have hc := integral_mono_on (μ := MeasureTheory.volume) hB
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-u ^ 2 / 10000000000))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-u / 100))).intervalIntegrable _ _)
    (fun u (hu : u ∈ Set.Icc (100000000 : ℝ) B) => ?_)
  · exact (hc.trans (integral_square_exponential_tail_le 100000000 B)).trans_lt numerical_exponential_tail
  · apply mul_le_mul_of_nonneg_left _ (sq_nonneg u)
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ u * (u - 100000000) := mul_nonneg (by linarith [hu.1]) (by linarith [hu.1])
    nlinarith

/-- The unweighted Gaussian tail is bounded by the same second-moment tail. -/
theorem gaussian_zeroth_moment_tail (B : ℝ) (hB : 100000000 ≤ B) :
    (∫ u in (100000000 : ℝ)..B, Real.exp (-u ^ 2 / 10000000000)) < 1 / 100 := by
  have hc := integral_mono_on (μ := MeasureTheory.volume) hB
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-u ^ 2 / 10000000000))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-u ^ 2 / 10000000000))).intervalIntegrable _ _)
    (fun u (hu : u ∈ Set.Icc (100000000 : ℝ) B) => ?_)
  · exact hc.trans_lt (gaussian_second_moment_tail B hB)
  · have hs : 1 ≤ u ^ 2 := by nlinarith [hu.1]
    have hh := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-u ^ 2 / 10000000000)).le
    simpa only [one_mul] using hh

end DenominatorResearch
