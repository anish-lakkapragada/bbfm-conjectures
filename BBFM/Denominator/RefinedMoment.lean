import BBFM.Denominator.Analytic.FourierCore

noncomputable section
namespace BBFMRefined
open Real Complex intervalIntegral

private def p8 (u : ℝ) : ℝ :=
  u^8 + 8*u^7 + 56*u^6 + 336*u^5 + 1680*u^4 + 6720*u^3 +
    20160*u^2 + 40320*u + 40320

private lemma p8_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ p8 u := by
  unfold p8
  positivity

private lemma primitive_deriv (u : ℝ) :
    HasDerivAt (fun u : ℝ => -p8 u * Real.exp (-u))
      (u^8 * Real.exp (-u)) u := by
  have h0 := ((hasDerivAt_id u).pow 8).add (((hasDerivAt_id u).pow 7).const_mul 8)
  have h1 := h0.add (((hasDerivAt_id u).pow 6).const_mul 56)
  have h2 := h1.add (((hasDerivAt_id u).pow 5).const_mul 336)
  have h3 := h2.add (((hasDerivAt_id u).pow 4).const_mul 1680)
  have h4 := h3.add (((hasDerivAt_id u).pow 3).const_mul 6720)
  have h5 := h4.add (((hasDerivAt_id u).pow 2).const_mul 20160)
  have hp := (h5.add ((hasDerivAt_id u).const_mul 40320)).add_const 40320
  have he := ((hasDerivAt_id u).neg).exp
  convert! hp.neg.mul he using 1 <;>
    simp only [p8, id_eq, Pi.pow_apply, Pi.add_apply, Pi.neg_apply] <;> ring

lemma eighth_exponential_moment (B : ℝ) (hB : 0 ≤ B) :
    (∫ u in (0 : ℝ)..B, u^8 * Real.exp (-u)) ≤ 40320 := by
  have h := integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ Set.uIcc 0 B) => primitive_deriv u)
    ((by fun_prop : Continuous (fun u : ℝ => u^8 * Real.exp (-u))).intervalIntegrable 0 B)
  rw [h]
  have hp := mul_nonneg (p8_nonneg B hB) (Real.exp_pos (-B)).le
  norm_num [p8] at *
  nlinarith

/-- A deliberately loose but elementary Gaussian eighth-moment bound. -/
theorem gaussian_eighth_moment (B : ℝ) (hB : 0 ≤ B) :
    (∫ u in (0 : ℝ)..B, u^8 * Real.exp (-u^2 / 4)) ≤ 1000000 := by
  have hc := integral_mono_on (μ := MeasureTheory.volume) hB
    ((by fun_prop : Continuous (fun u : ℝ => u^8 * Real.exp (-u^2 / 4))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u : ℝ => 3 * (u^8 * Real.exp (-u)))).intervalIntegrable _ _)
    (fun u (_ : u ∈ Set.Icc (0 : ℝ) B) => ?_)
  · rw [integral_const_mul] at hc
    linarith [eighth_exponential_moment B hB]
  · have he : Real.exp (-u^2 / 4) ≤ 3 * Real.exp (-u) := by
      calc
        _ ≤ Real.exp (1 + -u) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (u-2)])
        _ = Real.exp 1 * Real.exp (-u) := Real.exp_add _ _
        _ ≤ 3 * Real.exp (-u) := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le
    have hu8 : 0 ≤ u^8 := by positivity
    have hm := mul_le_mul_of_nonneg_left he hu8
    nlinarith only [hm]

theorem scaled_gaussian_eighth_moment (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    (∫ θ in (0 : ℝ)..c, θ^8 * Real.exp (-(θ/a)^2/4)) ≤ 1000000 * a^9 := by
  have hm := gaussian_eighth_moment (c/a) (div_nonneg hc ha.le)
  have hs := integral_comp_div (fun u : ℝ => u^8 * Real.exp (-u^2/4))
    (a := (0 : ℝ)) (b := c) ha.ne'
  simp only [smul_eq_mul, zero_div] at hs
  have heq : (fun θ : ℝ => θ^8 * Real.exp (-(θ/a)^2/4)) =
      fun θ : ℝ => a^8 * ((θ/a)^8 * Real.exp (-(θ/a)^2/4)) := by
    funext θ
    field_simp
    <;> ring
  rw [heq, integral_const_mul, hs]
  have hh := mul_le_mul_of_nonneg_left hm (pow_pos ha 9).le
  nlinarith

/-- A cubic logarithmic error can have either sign; its negative contribution
is controlled by its squared imaginary part and a Gaussian envelope. -/
theorem local_exponential_real_lower_error (s M θ : ℝ) (R : ℂ)
    (hM : 0 ≤ M) (hθ : 0 ≤ θ) (hR : ‖R‖ ≤ M * θ^3)
    (hrel : ‖R‖ ≤ s/2) :
    -(M^2 * θ^6 * Real.exp (-s/2)) ≤
      (Complex.exp (-(s : ℂ) + R)).re := by
  have hi := Complex.abs_im_le_norm R
  have hr := Complex.abs_re_le_norm R
  have hi2 : R.im^2 ≤ M^2 * θ^6 := by
    have h := pow_le_pow_left₀ (abs_nonneg R.im) (hi.trans hR) 2
    rw [sq_abs] at h
    nlinarith
  have hc : -(M^2 * θ^6) ≤ Real.cos R.im := by
    have h := Real.one_sub_sq_div_two_le_cos (x := R.im)
    nlinarith [sq_nonneg R.im, mul_nonneg (sq_nonneg M) (pow_nonneg hθ 6)]
  have he : Real.exp (-s + R.re) ≤ Real.exp (-s/2) := by
    apply Real.exp_le_exp.mpr
    have h := (abs_le.mp (hr.trans hrel)).2
    linarith
  have hp := mul_le_mul_of_nonneg_left hc (Real.exp_pos (-s+R.re)).le
  have hq := mul_le_mul_of_nonneg_right he
    (mul_nonneg (sq_nonneg M) (pow_nonneg hθ 6))
  rw [Complex.exp_re]
  simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    Complex.add_im, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_add]
  nlinarith

#print axioms gaussian_eighth_moment
#print axioms local_exponential_real_lower_error
end BBFMRefined
