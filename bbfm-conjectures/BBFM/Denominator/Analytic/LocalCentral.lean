import BBFM.Denominator.Analytic.GaussianTail

noncomputable section
namespace DenominatorResearch
open Real Complex

lemma small_complex_error_cos (z : ℂ) (hz : ‖z‖ ≤ 1 / 10) :
    (3 / 4 : ℝ) ≤ Real.cos z.im := by
  have hi := (Complex.abs_im_le_norm z).trans hz
  have hisq : z.im ^ 2 ≤ 1 / 100 := by
    have hh := pow_le_pow_left₀ (abs_nonneg z.im) hi 2
    rw [sq_abs] at hh
    norm_num at hh
    exact hh
  have hc := Real.one_sub_sq_div_two_le_cos (x := z.im)
  linarith

/-- A small complex logarithmic remainder forces a positive central real part. -/
theorem local_exponential_real_pos (s : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 10) :
    0 < (Complex.exp (-(s : ℂ) + z)).re := by
  rw [Complex.exp_re]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add]
  have hc := small_complex_error_cos z hz
  exact mul_pos (Real.exp_pos _) (by linarith)

/-- Quantitative lower bound at one standard deviation.
The input s will be V*theta^2/2 in the application. -/
theorem local_exponential_real_lower (s : ℝ) (z : ℂ)
    (hs : s ≤ 1 / 2) (hz : ‖z‖ ≤ 1 / 10) :
    (1 / 4 : ℝ) ≤ (Complex.exp (-(s : ℂ) + z)).re := by
  have hr := (Complex.abs_re_le_norm z).trans hz
  have hrlo : -(1 / 10 : ℝ) ≤ z.re := (abs_le.mp hr).1
  have hexp : (1 / 3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (lt_div_iff₀ (Real.exp_pos 1)).2
    nlinarith [Real.exp_one_lt_three]
  have hexp' : (1 / 3 : ℝ) ≤ Real.exp (-s + z.re) :=
    hexp.le.trans (Real.exp_le_exp.mpr (by linarith))
  have hc := small_complex_error_cos z hz
  rw [Complex.exp_re]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add]
  have hh := mul_le_mul hexp' hc (by norm_num : (0 : ℝ) ≤ 3 / 4) (Real.exp_pos _).le
  norm_num at hh
  exact hh

end DenominatorResearch
