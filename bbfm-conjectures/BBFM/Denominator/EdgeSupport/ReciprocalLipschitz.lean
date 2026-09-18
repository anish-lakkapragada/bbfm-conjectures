import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace DenominatorEdgeSupport

/-- Adjacent normalized ratios vary slowly when their denominators stay near
a common large multiplicity and move by at most sixteen. -/
theorem reciprocal_ratio_step (r j u v : ℝ) (hj : 1 ≤ j) (hr : 1000*j ≤ r)
    (hu : r-j ≤ u) (hv : r-j ≤ v) (hv' : v ≤ r+8*j) (hd : |u-v| ≤ 16) :
    |j/u-(j-1)/v| ≤ 2/r ∧ (0 ≤ j/u ∧ j/u ≤ 1/16) := by
  have hj0 : 0 ≤ j := by linarith
  have hr0 : 0 < r := by linarith
  have hrj : 0 < r-j := by linarith
  have hu0 : 0 < u := lt_of_lt_of_le hrj hu
  have hv0 : 0 < v := lt_of_lt_of_le hrj hv
  have huv0 : 0 < u*v := mul_pos hu0 hv0
  have hd1 := (abs_le.mp hd).1
  have hd2 := (abs_le.mp hd).2
  have hj1 : 0 ≤ j-1 := by linarith
  have hdl := mul_le_mul_of_nonneg_left hd1 hj1
  have hdu := mul_le_mul_of_nonneg_left hd2 hj1
  have hnum : |j*v-(j-1)*u| ≤ r+24*j := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hden : (r-j)^2 ≤ u*v := by
    simpa only [pow_two] using mul_le_mul hu hv (le_of_lt hrj) (le_of_lt hu0)
  have hscale : (r+24*j)*r ≤ 2*(r-j)^2 := by
    have hr28 : 0 ≤ r-28*j := by linarith
    nlinarith [mul_nonneg hr28 (le_of_lt hr0), sq_nonneg j]
  constructor
  · rw [div_sub_div _ _ (ne_of_gt hu0) (ne_of_gt hv0), abs_div,
      abs_of_pos huv0]
    apply (div_le_div_iff₀ huv0 hr0).mpr
    rw [mul_comm u (j-1)]
    have hb := mul_le_mul_of_nonneg_right hnum (le_of_lt hr0)
    nlinarith
  · constructor
    · positivity
    · apply (div_le_iff₀ hu0).mpr
      nlinarith

/-- Natural-index presentation of the same estimate, convenient for the
coefficient-ratio induction. The upper bound on u is unnecessary. -/
theorem reciprocal_ratio_step_of_bound (r u v : ℝ) (j K : ℕ)
    (hj : 1 ≤ j) (hjK : j ≤ K) (hr : 1000*(K : ℝ) ≤ r)
    (hu : r-j ≤ u) (hv : r-j ≤ v) (hv' : v ≤ r+8*j) (hd : |u-v| ≤ 16) :
    |(j : ℝ)/u-((j : ℝ)-1)/v| ≤ 2/r ∧
      (0 ≤ (j : ℝ)/u ∧ (j : ℝ)/u ≤ 1/16) := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjK' : (j : ℝ) ≤ K := by exact_mod_cast hjK
  exact reciprocal_ratio_step r j u v hj' (by linarith) hu hv hv' hd

#print axioms reciprocal_ratio_step
#print axioms reciprocal_ratio_step_of_bound
end DenominatorEdgeSupport
