import BBFM.Denominator.BernoulliMomentRatio
import BBFM.Denominator.MonotoneWeightTransfer
import BBFM.Denominator.VarianceMoment
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Finite-prefix and decreasing-profile transfer of the new Bernoulli
third-moment estimate. All infinite sums below are proved summable. -/
noncomputable section
namespace BBFMMoment
open Real Finset DenominatorResearch BBFMRelative
set_option maxHeartbeats 0

def varianceTerm (r : ℝ) (i : ℕ) : ℝ := (i : ℝ)^2*r^i/(1+r^i)^2

lemma varianceTerm_bounds (r : ℝ) (hr : 0 ≤ r) (i : ℕ) :
    0 ≤ varianceTerm r i ∧ varianceTerm r i ≤ (i : ℝ)^2*r^i := by
  have hp : 0 ≤ r^i := pow_nonneg hr _
  have hd : 1 ≤ (1+r^i)^2 := by nlinarith
  constructor
  · unfold varianceTerm; positivity
  · unfold varianceTerm
    apply (div_le_iff₀ (by positivity : 0 < (1+r^i)^2)).mpr
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ (i : ℝ)^2*r^i by positivity)
    nlinarith only [hh]

lemma varianceTerm_lower (r : ℝ) (hr : 0 ≤ r) (i : ℕ) :
    (i : ℝ)^2*r^i-2*((i : ℝ)^2*(r^2)^i) ≤ varianceTerm r i := by
  have hp : 0 ≤ r^i := pow_nonneg hr _
  have hbase : r^i-2*(r^i)^2 ≤ r^i/(1+r^i)^2 := by
    apply (le_div_iff₀ (by positivity : 0 < (1+r^i)^2)).mpr
    nlinarith [pow_nonneg hp 3,pow_nonneg hp 4]
  have hh := mul_le_mul_of_nonneg_left hbase (sq_nonneg (i : ℝ))
  unfold varianceTerm
  have he : (r^2)^i=(r^i)^2 := by rw [← pow_mul,Nat.mul_comm,pow_mul]
  rw [he]
  rw [← mul_div_assoc] at hh
  nlinarith only [hh]

lemma varianceTerm_summable (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (varianceTerm r) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := r) (by simpa [Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
  exact Summable.of_nonneg_of_le (fun i => (varianceTerm_bounds r hr i).1)
    (fun i => (varianceTerm_bounds r hr i).2) hs

lemma infinite_third_le_variance (r L : ℝ) (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hL : L=1/(-Real.log r)) :
    (∑' i : ℕ, (i : ℝ)^3*r^i) ≤ 4*L*(∑' i : ℕ, varianceTerm r i) := by
  have hr0 : 0 < r := by linarith
  have hlog : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr1)
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := r) (by simpa [Real.norm_eq_abs,abs_of_pos hr0] using hr1)
  have hr2 : r^2 < 1 := by nlinarith
  have hs22 := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := r^2) (by simpa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] using hr2)
  have hv := Summable.tsum_le_tsum (varianceTerm_lower r hr0.le)
    (hs2.sub (hs22.mul_left 2)) (varianceTerm_summable r hr0.le hr1)
  rw [hs2.tsum_sub (hs22.mul_left 2),tsum_mul_left] at hv
  have hi := infinite_moment_comparison r hr hr1
  have hh := mul_le_mul_of_nonneg_left (show
    (-Real.log r)*(∑' i : ℕ, (i : ℝ)^3*r^i) ≤
      4*(∑' i : ℕ, varianceTerm r i) by linarith) (le_of_lt (one_div_pos.mpr hlog))
  rw [hL]
  calc
    (∑' i : ℕ, (i : ℝ)^3*r^i) =
        (1/(-Real.log r))*((-Real.log r)*(∑' i : ℕ, (i : ℝ)^3*r^i)) := by
          have hn : Real.log r ≠ 0 := ne_of_lt (Real.log_neg hr0 hr1)
          field_simp [hn]
    _ ≤ (1/(-Real.log r))*(4*(∑' i : ℕ, varianceTerm r i)) := hh
    _ = _ := by ring

lemma scaled_bernoulli_bound (x : ℝ) (hx : 0 ≤ x) (hx4 : x ≤ 4) :
    x*(1+Real.exp (-x))^2 ≤ 9/2 := by
  have he1 : Real.exp (-1) ≤ (3/8 : ℝ) := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 1)).mpr
    linarith [Real.exp_one_gt_d9]
  have hexp : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hb (j : ℕ) (hj : (j : ℝ) ≤ x) : Real.exp (-x) ≤ (3/8 : ℝ)^j := by
    have hh := pow_le_pow_left₀ (Real.exp_pos (-1)).le he1 j
    rw [← Real.exp_nat_mul] at hh
    calc
      Real.exp (-x) ≤ Real.exp ((j : ℝ)*(-1)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := hh
  by_cases h1 : x ≤ 1
  · have he : Real.exp (-x) ≤ 1 := by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hx)
    have hs : (1+Real.exp (-x))^2 ≤ 4 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hx]
  by_cases h2 : x ≤ 2
  · have he := hb 1 (by norm_num; linarith)
    norm_num at he
    have hs : (1+Real.exp (-x))^2 ≤ (11/8 : ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hx]
  by_cases h3 : x ≤ 3
  · have he := hb 2 (by norm_num; linarith)
    norm_num at he
    have hs : (1+Real.exp (-x))^2 ≤ (73/64 : ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hx]
  · have he := hb 3 (by norm_num; linarith)
    norm_num at he
    have hs : (1+Real.exp (-x))^2 ≤ (539/512 : ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hs hx]

#print axioms infinite_third_le_variance
#print axioms scaled_bernoulli_bound
end BBFMMoment
