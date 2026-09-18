import BBFM.Denominator.Analytic.Moments

noncomputable section
namespace DenominatorResearch
open Finset Real

lemma hasSum_cube_mul_geometric (r : ℝ) (hr : ‖r‖ < 1) :
    HasSum (fun i : ℕ => (i : ℝ) ^ 3 * r ^ i)
      (r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4) := by
  have h := hasSum_pow_mul_geometric_of_norm_lt_one 3 hr
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond] at h
  have hd : 1 - r ≠ 0 := by
    have := lt_of_le_of_lt (le_abs_self r) (show |r| < 1 by simpa only [Real.norm_eq_abs] using hr)
    linarith
  convert! h using 1
  field_simp
  <;> ring

/-- The explicit third-moment constant used in the small-radius Taylor estimate. -/
theorem small_radius_moment_three (m : ℕ → ℕ) (n t : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    weightedMoment m n 3 r ≤ 52 * (t : ℝ) * r := by
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  have h := weightedMoment_le_of_hasSum m n 3 t (by decide) r _ hr hm
    (hasSum_cube_mul_geometric r hrnorm)
  have hden : 0 < (1 - r) ^ 4 := pow_pos (by linarith) _
  have hfrac : r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 ≤ 52 * r := by
    apply (div_le_iff₀ hden).2
    have hsq : r ^ 2 ≤ 1 / 4 := by nlinarith [mul_nonneg hr (show 0 ≤ 1 / 2 - r by linarith)]
    have hnum : 1 + 4 * r + r ^ 2 ≤ 13 / 4 := by linarith
    have hfourth : (1 / 16 : ℝ) ≤ (1 - r) ^ 4 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (show (1 / 2 : ℝ) ≤ 1 - r by linarith) 4
      norm_num at hh
      exact hh
    have hh1 := mul_le_mul_of_nonneg_left hnum hr
    have hh2 := mul_le_mul_of_nonneg_left hfourth (show 0 ≤ 52 * r by positivity)
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hfrac (show 0 ≤ (t : ℝ) by positivity)
  nlinarith

theorem den_small_radius_third_moment (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    weightedMoment (fun i => Nat.log 2 (n / i) + 1) n 3 r ≤
      52 * ((Nat.log 2 n + 1 : ℕ) : ℝ) * r := by
  apply small_radius_moment_three _ _ _ _ hr hrhalf
  intro i _ _
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1

end DenominatorResearch
