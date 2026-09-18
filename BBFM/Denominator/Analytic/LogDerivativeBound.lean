import BBFM.Denominator.Analytic.HigherMoment
import BBFM.Denominator.Analytic.CharacteristicBridge

noncomputable section
namespace DenominatorResearch
open Finset Complex

/-- Algebraic expression for the third logarithmic derivative of 1+z.
The derivative identity itself is part of the written argument. -/
def thirdLogRatio (z : ℂ) : ℂ := z * (1 - z) / (1 + z) ^ 3

lemma thirdLogRatio_norm_bound (z : ℂ) (hz : ‖z‖ ≤ 1) (hd : 1 / 2 ≤ ‖1 + z‖) :
    ‖thirdLogRatio z‖ ≤ 16 * ‖z‖ := by
  have hd0 : 0 < ‖1 + z‖ := by linarith
  have hden : (1 / 8 : ℝ) ≤ ‖1 + z‖ ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hd 3
    norm_num at h
    exact h
  have hnum : ‖z * (1 - z)‖ ≤ 2 * ‖z‖ := by
    rw [norm_mul]
    have hs := norm_sub_le (1 : ℂ) z
    simp only [norm_one] at hs
    have hh := mul_le_mul_of_nonneg_left hs (norm_nonneg z)
    have hh2 := mul_le_mul_of_nonneg_left hz (norm_nonneg z)
    nlinarith
  unfold thirdLogRatio
  rw [norm_div, norm_pow]
  apply (div_le_iff₀ (pow_pos hd0 3)).2
  have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ 16 * ‖z‖ by positivity)
  nlinarith

lemma thirdLogRatio_norm_bound_small (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖thirdLogRatio z‖ ≤ 16 * ‖z‖ := by
  apply thirdLogRatio_norm_bound z (by linarith)
  have h := norm_sub_norm_le (1 : ℂ) (-z)
  simp only [norm_one, norm_neg, sub_neg_eq_add] at h
  linarith

def factorPhase (r θ : ℝ) (i : ℕ) : ℂ :=
  (r : ℂ) ^ i * Complex.exp ((i : ℂ) * (θ : ℂ) * Complex.I)

lemma factorPhase_norm (r θ : ℝ) (i : ℕ) (hr : 0 ≤ r) :
    ‖factorPhase r θ i‖ = r ^ i := by
  unfold factorPhase
  rw [norm_mul, norm_pow, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Real.norm_eq_abs, abs_of_nonneg hr]

/-- The complete finite expression whose norm controls the third derivative.
No derivative or Taylor assertion is smuggled into this definition. -/
def thirdLogSum (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ) : ℂ :=
  ∑ i ∈ range n, (m (i + 1) : ℂ) * (Complex.I * (i + 1 : ℕ)) ^ 3 *
    thirdLogRatio (factorPhase r θ (i + 1))

/-- Uniform pointwise third-derivative expression bound at small radii. -/
theorem thirdLogSum_small_radius_bound (m : ℕ → ℕ) (n t : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    ‖thirdLogSum m n r θ‖ ≤ 832 * (t : ℝ) * r := by
  have hs : ‖thirdLogSum m n r θ‖ ≤ 16 * weightedMoment m n 3 r := by
    unfold thirdLogSum weightedMoment
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hp : r ^ (i + 1) ≤ 1 / 2 := by
      apply le_trans _ hrhalf
      exact pow_le_of_le_one hr (by linarith) (by omega)
    have hratio := thirdLogRatio_norm_bound_small (factorPhase r θ (i + 1))
      (by rw [factorPhase_norm r θ (i + 1) hr]; exact hp)
    rw [factorPhase_norm r θ (i + 1) hr] at hratio
    simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_natCast]
    have hh := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ (m (i + 1) : ℝ) * ((i + 1 : ℕ) : ℝ) ^ 3 by positivity)
    push_cast at hh ⊢
    nlinarith
  have hmoment := small_radius_moment_three m n t r hr hrhalf hm
  nlinarith

theorem den_thirdLogSum_small_radius_bound (n : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    ‖thirdLogSum (fun i => Nat.log 2 (n / i) + 1) n r θ‖ ≤
      832 * ((Nat.log 2 n + 1 : ℕ) : ℝ) * r := by
  apply thirdLogSum_small_radius_bound _ _ _ _ _ hr hrhalf
  intro i _ _
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1

end DenominatorResearch
