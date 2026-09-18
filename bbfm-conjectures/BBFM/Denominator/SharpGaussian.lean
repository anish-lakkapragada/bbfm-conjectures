import BBFM.Denominator.RefinedMoment

noncomputable section
namespace BBFMRelative
open Real Complex intervalIntegral
set_option maxHeartbeats 0

private def p7 (u : ℝ) : ℝ := 2*u^7+28*u^5+280*u^3+1680*u

private lemma p7_nonneg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ p7 u := by
  unfold p7
  positivity

private lemma primitive_deriv (u : ℝ) :
    HasDerivAt (fun u : ℝ => -p7 u*Real.exp (-u^2/4))
      ((u^8-1680)*Real.exp (-u^2/4)) u := by
  have hp := ((((hasDerivAt_id u).pow 7).const_mul 2).add
    (((hasDerivAt_id u).pow 5).const_mul 28)).add
    (((hasDerivAt_id u).pow 3).const_mul 280)
  have hp' := hp.add ((hasDerivAt_id u).const_mul 1680)
  have he := (((hasDerivAt_id u).pow 2).neg.div_const 4).exp
  convert! hp'.neg.mul he using 1 <;>
    simp only [p7,id_eq,Pi.pow_apply,Pi.add_apply,Pi.neg_apply] <;> ring

lemma gaussian_zeroth_moment (B : ℝ) (hB : 0 ≤ B) :
    (∫ u in (0 : ℝ)..B, Real.exp (-u^2/4)) ≤ 3 := by
  have hh := integral_mono_on (μ := MeasureTheory.volume) hB
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-u^2/4))).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun u : ℝ => 3*Real.exp (-u))).intervalIntegrable _ _)
    (fun u (_ : u ∈ Set.Icc (0 : ℝ) B) => ?_)
  · have hi : (∫ u in (0 : ℝ)..B, Real.exp (-u)) = 1-Real.exp (-B) := by
      have hf := integral_eq_sub_of_hasDerivAt
        (fun u (_ : u ∈ Set.uIcc 0 B) =>
          by convert (((hasDerivAt_id u).neg).exp).neg using 1 <;> simp)
        ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-u))).intervalIntegrable 0 B)
      simpa using hf
    rw [integral_const_mul,hi] at hh
    nlinarith [Real.exp_pos (-B)]
  · calc
      Real.exp (-u^2/4) ≤ Real.exp (1 + -u) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (u-2)])
      _ = Real.exp 1*Real.exp (-u) := Real.exp_add _ _
      _ ≤ 3*Real.exp (-u) :=
        mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos _).le

/-- Integration by parts gives the eighth Gaussian moment with no numerical
integration oracle. The exact recurrence factor is1680. -/
theorem gaussian_eighth_moment (B : ℝ) (hB : 0 ≤ B) :
    (∫ u in (0 : ℝ)..B, u^8*Real.exp (-u^2/4)) ≤ 6000 := by
  have hf := integral_eq_sub_of_hasDerivAt
    (fun u (_ : u ∈ Set.uIcc 0 B) => primitive_deriv u)
    ((by fun_prop : Continuous (fun u : ℝ => (u^8-1680)*Real.exp (-u^2/4))).intervalIntegrable 0 B)
  have heq : (fun u : ℝ => (u^8-1680)*Real.exp (-u^2/4)) =
      fun u => u^8*Real.exp (-u^2/4) - 1680*Real.exp (-u^2/4) := by
    funext u
    ring
  rw [heq,integral_sub
    ((by fun_prop : Continuous (fun u : ℝ => u^8*Real.exp (-u^2/4))).intervalIntegrable 0 B)
    ((by fun_prop : Continuous (fun u : ℝ => 1680*Real.exp (-u^2/4))).intervalIntegrable 0 B),
    integral_const_mul] at hf
  have hn := mul_nonneg (p7_nonneg B hB) (Real.exp_pos (-B^2/4)).le
  have hz := gaussian_zeroth_moment B hB
  norm_num [p7] at hf hn
  nlinarith only [hf,hn,hz]

theorem scaled_gaussian_eighth_moment (a c : ℝ) (ha : 0 < a) (hc : 0 ≤ c) :
    (∫ θ in (0 : ℝ)..c, θ^8*Real.exp (-(θ/a)^2/4)) ≤ 6000*a^9 := by
  have hm := gaussian_eighth_moment (c/a) (div_nonneg hc ha.le)
  have hs := integral_comp_div (fun u : ℝ => u^8*Real.exp (-u^2/4))
    (a := (0 : ℝ)) (b := c) ha.ne'
  simp only [smul_eq_mul,zero_div] at hs
  have heq : (fun θ : ℝ => θ^8*Real.exp (-(θ/a)^2/4)) =
      fun θ => a^8*((θ/a)^8*Real.exp (-(θ/a)^2/4)) := by
    funext θ
    field_simp
    <;> ring
  rw [heq,integral_const_mul,hs]
  have hh := mul_le_mul_of_nonneg_left hm (pow_pos ha 9).le
  nlinarith only [hh]

#print axioms gaussian_eighth_moment
end BBFMRelative
