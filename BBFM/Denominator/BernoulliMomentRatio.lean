import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! New rational logarithm envelope and infinite geometric moment comparison.
This is a supporting inequality, not a denominator coefficient theorem. -/
noncomputable section
namespace BBFMMoment
open Real Finset
set_option maxHeartbeats 0

def logEnvelope (r : ℝ) : ℝ := (1-r)*(r^2+10*r+1)/(6*r*(1+r))

lemma logEnvelope_add_log_hasDerivAt (r : ℝ) (hr : 0<r) :
    HasDerivAt (fun t : ℝ => logEnvelope t+Real.log t)
      (-(1-r)^4/(6*r^2*(1+r)^2)) r := by
  have hx := hasDerivAt_id r
  have hn := (hx.const_sub 1).mul (((hx.pow 2).add (hx.const_mul 10)).add_const 1)
  have hd := (hx.const_mul 6).mul (hx.const_add 1)
  have hh := (hn.div hd (by change 6*r*(1+r) ≠ 0; positivity)).add
    (Real.hasDerivAt_log hr.ne')
  unfold logEnvelope
  convert! hh using 1 <;>
    simp only [id_eq,Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.pow_apply]
  have hp : 1+r ≠ 0 := by positivity
  field_simp [hr.ne',hp]
  <;> ring

theorem neg_log_le_envelope (r : ℝ) (hr : 0<r) (hr1 : r≤1) :
    -Real.log r ≤ logEnvelope r := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc r 1) :=
    logEnvelope_add_log_hasDerivAt x (lt_of_lt_of_le hr hx.1)
  have hm : AntitoneOn (fun t : ℝ => logEnvelope t+Real.log t) (Set.Icc r 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc r 1)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (by positivity)
    · positivity
  have hh := hm ⟨le_rfl,hr1⟩ ⟨hr1,le_rfl⟩ hr1
  dsimp only at hh
  have hz : logEnvelope 1+Real.log 1=0 := by norm_num [logEnvelope]
  rw [hz] at hh
  linarith

lemma geometric_cube_sum (r : ℝ) (hr : 0≤r) (hr1 : r<1) :
    (∑' i : ℕ, (i : ℝ)^3*r^i)=r*(1+4*r+r^2)/(1-r)^4 := by
  rw [tsum_pow_mul_geometric_of_norm_lt_one 3 (by simpa [Real.norm_eq_abs,abs_of_nonneg hr])]
  norm_num [sum_range_succ,Nat.stirlingSecond]
  field_simp [show 1-r ≠ 0 by linarith]
  <;> ring

theorem infinite_moment_comparison (r : ℝ) (hr : 1/2≤r) (hr1 : r<1) :
    (-Real.log r)*(∑' i : ℕ, (i : ℝ)^3*r^i) ≤
      4*((∑' i : ℕ, (i : ℝ)^2*r^i)-2*(∑' i : ℕ, (i : ℝ)^2*(r^2)^i)) := by
  have hr0 : 0<r := by linarith
  have hr2 : r^2<1 := by nlinarith
  rw [geometric_cube_sum r hr0.le hr1,
    tsum_sq_mul_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs,abs_of_pos hr0] using hr1),
    tsum_sq_mul_geometric_of_norm_lt_one (r := r^2) (by simpa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] using hr2)]
  have he := neg_log_le_envelope r hr0 hr1.le
  have hp := mul_le_mul_of_nonneg_right he
    (show 0≤r*(1+4*r+r^2)/(1-r)^4 by positivity)
  have hid : 4*(r*(1+r)/(1-r)^3-2*(r^2*(1+r^2)/(1-r^2)^3))-
      logEnvelope r*(r*(1+4*r+r^2)/(1-r)^4) =
      (1-r)*(-r^2+4*r-1)/(6*(1+r)^3) := by
    unfold logEnvelope
    have h1 : 1-r≠0 := by linarith
    have h2 : 1-r^2≠0 := by linarith
    have h3 : 1+r≠0 := by positivity
    field_simp [h1,h2,h3,hr0.ne']
    <;> ring
  have hpoly : 0≤-r^2+4*r-1 := by
    nlinarith [mul_nonneg (show 0≤r-1/2 by linarith) (show 0≤1-r by linarith)]
  have hnon : 0≤(1-r)*(-r^2+4*r-1)/(6*(1+r)^3) := by positivity
  linarith

#print axioms neg_log_le_envelope
#print axioms infinite_moment_comparison
end BBFMMoment
