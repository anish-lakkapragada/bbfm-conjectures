import BBFM.Denominator.Analytic.CharacteristicBridge

noncomputable section
namespace DenominatorResearch
open Finset Real intervalIntegral

lemma integral_integer_cosine (i k : ℕ) :
    (∫ θ in -Real.pi..Real.pi, Real.cos (((i : ℝ) - k) * θ)) =
      if i = k then 2 * Real.pi else 0 := by
  by_cases hik : i = k
  · subst i
    simp
    ring
  · rw [if_neg hik]
    have hc : (i : ℝ) - k ≠ 0 := by
      intro h
      apply hik
      exact_mod_cast sub_eq_zero.mp h
    rw [intervalIntegral.integral_comp_mul_left Real.cos hc, integral_cos]
    have hs : Real.sin (((i : ℝ) - k) * Real.pi) = 0 := by
      have h := Real.sin_int_mul_pi ((i : ℤ) - k)
      simpa only [Int.cast_sub, Int.cast_natCast] using h
    simp only [mul_neg, Real.sin_neg, hs, neg_zero, sub_zero, smul_zero]

/-- A finite real Fourier sum, centered at the requested coefficient. -/
def cosineSum (a : ℕ → ℝ) (d k : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ range (d + 1), a i * Real.cos (((i : ℝ) - k) * θ)

lemma continuous_cosineSum (a : ℕ → ℝ) (d k : ℕ) : Continuous (cosineSum a d k) := by
  unfold cosineSum
  fun_prop

/-- Elementary Fourier coefficient inversion, proved for an actual finite sum. -/
theorem cosineSum_integral (a : ℕ → ℝ) (d k : ℕ) (hk : k ≤ d) :
    (∫ θ in -Real.pi..Real.pi, cosineSum a d k θ) = 2 * Real.pi * a k := by
  unfold cosineSum
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_integer_cosine]
    simp [show k < d + 1 by omega, mul_comm]
  · intro i hi
    exact (by fun_prop : Continuous (fun θ : ℝ => a i * Real.cos (((i : ℝ) - k) * θ))).intervalIntegrable _ _

lemma cosine_neighbor_identity (i k : ℕ) (θ : ℝ) (hk : 1 ≤ k) :
    Real.cos (((i : ℝ) - (k - 1 : ℕ)) * θ) +
      Real.cos (((i : ℝ) - (k + 1 : ℕ)) * θ) =
        2 * Real.cos (((i : ℝ) - k) * θ) * Real.cos θ := by
  rw [Nat.cast_sub hk, Nat.cast_add, Nat.cast_one]
  rw [show ((i : ℝ) - ((k : ℝ) - 1)) * θ = ((i : ℝ) - k) * θ + θ by ring,
    show ((i : ℝ) - ((k : ℝ) + 1)) * θ = ((i : ℝ) - k) * θ - θ by ring]
  rw [Real.cos_add, Real.cos_sub]
  ring

lemma cosineSum_second_difference (a : ℕ → ℝ) (d k : ℕ) (θ : ℝ) (hk : 1 ≤ k) :
    cosineSum a d k θ * (1 - Real.cos θ) =
      cosineSum a d k θ - (cosineSum a d (k - 1) θ + cosineSum a d (k + 1) θ) / 2 := by
  have hs : cosineSum a d (k - 1) θ + cosineSum a d (k + 1) θ =
      2 * cosineSum a d k θ * Real.cos θ := by
    unfold cosineSum
    rw [← sum_add_distrib, mul_sum, sum_mul]
    apply sum_congr rfl
    intro i hi
    have h := cosine_neighbor_identity i k θ hk
    linear_combination a i * h
  nlinarith

/-- Exact identity behind the direct discrete Fourier proof of log-concavity. -/
theorem cosineSum_second_difference_integral (a : ℕ → ℝ) (d k : ℕ)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ d) :
    (∫ θ in -Real.pi..Real.pi, cosineSum a d k θ * (1 - Real.cos θ)) =
      2 * Real.pi * (a k - (a (k - 1) + a (k + 1)) / 2) := by
  simp_rw [cosineSum_second_difference a d k _ hk]
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_div, intervalIntegral.integral_add]
    · rw [cosineSum_integral a d k (by omega),
        cosineSum_integral a d (k - 1) (by omega),
        cosineSum_integral a d (k + 1) hkd]
      ring
    · exact (continuous_cosineSum a d (k - 1)).intervalIntegrable _ _
    · exact (continuous_cosineSum a d (k + 1)).intervalIntegrable _ _
  · exact (continuous_cosineSum a d k).intervalIntegrable _ _
  · exact (((continuous_cosineSum a d (k - 1)).add
      (continuous_cosineSum a d (k + 1))).div_const 2).intervalIntegrable _ _

/-- A reduction lemma, not a proof of the required integral positivity.
Its explicit analytic hypothesis is recorded in the final input audit. -/
theorem turan_of_positive_fourier_second_difference (a : ℕ → ℝ) (d k : ℕ)
    (ha : ∀ i, 0 ≤ a i) (hk : 1 ≤ k) (hkd : k + 1 ≤ d)
    (hI : 0 < ∫ θ in -Real.pi..Real.pi, cosineSum a d k θ * (1 - Real.cos θ)) :
    a (k - 1) * a (k + 1) < a k ^ 2 := by
  rw [cosineSum_second_difference_integral a d k hk hkd] at hI
  have hp : 0 < 2 * Real.pi := by positivity
  have hmiddle := (mul_pos_iff_of_pos_left hp).mp hI
  have hA := ha (k - 1)
  have hB := ha k
  have hC := ha (k + 1)
  have hsum : a (k - 1) + a (k + 1) < 2 * a k := by linarith
  have hsquare := (sq_lt_sq₀ (show 0 ≤ a (k - 1) + a (k + 1) by positivity)
    (show 0 ≤ 2 * a k by positivity)).mpr hsum
  nlinarith [sq_nonneg (a (k - 1) - a (k + 1))]

end DenominatorResearch
