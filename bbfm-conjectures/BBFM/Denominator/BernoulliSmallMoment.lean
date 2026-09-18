import BBFM.Denominator.BernoulliFiniteMoment

/-! A matching third raw-moment bound6V for every decreasing profile at
radius at most one half. Source draft, not accepted before compilation. -/
noncomputable section
namespace BBFMMoment
open Real Finset DenominatorResearch BBFMRelative
set_option maxHeartbeats 0

lemma infinite_third_le_six_variance (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    (∑' i : ℕ, (i : ℝ)^3*r^i) ≤ 6*(∑' i : ℕ, varianceTerm r i) := by
  have hr1 : r < 1 := by linarith
  have hr2 : r^2 < 1 := by nlinarith
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := r) (by simpa [Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
  have hs22 := summable_pow_mul_geometric_of_norm_lt_one 2
    (r := r^2) (by simpa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] using hr2)
  have hv := Summable.tsum_le_tsum (varianceTerm_lower r hr)
    (hs2.sub (hs22.mul_left 2)) (varianceTerm_summable r hr hr1)
  rw [hs2.tsum_sub (hs22.mul_left 2),tsum_mul_left] at hv
  have hi : (∑' i : ℕ, (i : ℝ)^3*r^i) ≤
      6*((∑' i : ℕ, (i : ℝ)^2*r^i)-2*(∑' i : ℕ, (i : ℝ)^2*(r^2)^i)) := by
    rw [geometric_cube_sum r hr hr1,
      tsum_sq_mul_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs,abs_of_nonneg hr] using hr1),
      tsum_sq_mul_geometric_of_norm_lt_one (r := r^2) (by simpa [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg r)] using hr2)]
    have hP : 0 ≤ 5-r+8*r^2-40*r^3-13*r^4-7*r^5 := by
      have h2 : r^2 ≤ 1/4 := by nlinarith
      have h3 : r^3 ≤ r^2/2 := by nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1/2-r by linarith)]
      have h4 : r^4 ≤ r^2/4 := by nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1/4-r^2 by linarith)]
      have h3' : r^3 ≤ 1/8 := by nlinarith
      have h5 : r^5 ≤ r^2/8 := by nlinarith [mul_nonneg (sq_nonneg r) (show 0 ≤ 1/8-r^3 by linarith)]
      nlinarith
    have hid : 6*(r*(1+r)/(1-r)^3-2*(r^2*(1+r^2)/(1-r^2)^3))-
        r*(1+4*r+r^2)/(1-r)^4 =
        r*(5-r+8*r^2-40*r^3-13*r^4-7*r^5)/((1-r)^4*(1+r)^3) := by
      have h1 : 1-r ≠ 0 := by linarith
      have h2 : 1-r^2 ≠ 0 := by linarith
      have h3 : 1+r ≠ 0 := by positivity
      field_simp [h1,h2,h3]
      <;> ring
    have hn : 0 ≤ r*(5-r+8*r^2-40*r^3-13*r^4-7*r^5)/((1-r)^4*(1+r)^3) := by positivity
    linarith
  linarith

lemma finite_third_le_six_variance (q : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    (∑ i ∈ range q, (i : ℝ)^3*r^i) ≤ 6*(∑ i ∈ range q, varianceTerm r i) := by
  by_cases hq : q ≤ 6
  · rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hi5 : i ≤ 5 := by have := mem_range.mp hi; omega
    have hc : (i : ℝ)*(1+(1/2 : ℝ)^i)^2 ≤ 6 := by interval_cases i <;> norm_num
    have hp := pow_le_pow_left₀ hr hrhalf i
    have hs : (1+r^i)^2 ≤ (1+(1/2 : ℝ)^i)^2 := by
      nlinarith [pow_nonneg hr i,pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) i]
    have hpoint : (i : ℝ)*(1+r^i)^2 ≤ 6 := by
      have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ (i : ℝ) by positivity)
      linarith
    unfold varianceTerm
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < (1+r^i)^2)).mpr
    have hh := mul_le_mul_of_nonneg_right hpoint (show 0 ≤ (i : ℝ)^2*r^i by positivity)
    nlinarith only [hh]
  · have hr1 : r < 1 := by linarith
    have hs3 := summable_pow_mul_geometric_of_norm_lt_one 3
      (r := r) (by simpa [Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
    have hsV := varianceTerm_summable r hr hr1
    let F : ℕ → ℝ := fun i => (i : ℝ)^3*r^i-6*varianceTerm r i
    have hsF : Summable F := hs3.sub (hsV.mul_left 6)
    have htail : ∀ i, i ∉ range q → 0 ≤ F i := by
      intro i hi
      have hiq : q ≤ i := by simpa only [mem_range,not_lt] using hi
      have hi6 : (6 : ℝ) ≤ i := by exact_mod_cast (show 6 ≤ i by omega)
      have hb := mul_le_mul_of_nonneg_left (varianceTerm_bounds r hr i).2 (by norm_num : (0 : ℝ) ≤ 6)
      have hh := mul_le_mul_of_nonneg_right hi6 (show 0 ≤ (i : ℝ)^2*r^i by positivity)
      dsimp [F]
      nlinarith only [hb,hh]
    have hp := hsF.sum_le_tsum (range q) htail
    have htotal : (∑' i : ℕ, F i) ≤ 0 := by
      dsimp [F]
      rw [hs3.tsum_sub (hsV.mul_left 6),tsum_mul_left]
      exact sub_nonpos.mpr (infinite_third_le_six_variance r hr hrhalf)
    have hh := hp.trans htotal
    simpa only [F,sum_sub_distrib,← mul_sum,sub_nonpos] using hh

theorem third_moment_sharp_small (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    weightedMoment m n 3 r ≤ 6*tiltedVariance m n r := by
  let a : ℕ → ℝ := fun i => ((i+1 : ℕ) : ℝ)^3*r^(i+1)
  let b : ℕ → ℝ := fun i => 6*varianceTerm r (i+1)
  have hp (q : ℕ) : (∑ i ∈ range q, a i) ≤ ∑ i ∈ range q, b i := by
    have hh := finite_third_le_six_variance (q+1) r hr hrhalf
    rw [sum_range_succ',sum_range_succ'] at hh
    simpa [a,b,varianceTerm,mul_sum] using hh
  have hh := weighted_prefix_le (fun i => (m (i+1) : ℝ)) a b n
    (by positivity) (fun i hi => by
      exact_mod_cast hm (i+1) (by omega) (by omega)) (fun q _ => hp q)
  calc
    weightedMoment m n 3 r = ∑ i ∈ range n, (m (i+1) : ℝ)*a i := by
      simp [weightedMoment,a,mul_assoc]
    _ ≤ ∑ i ∈ range n, (m (i+1) : ℝ)*b i := hh
    _ = 6*tiltedVariance m n r := by
      unfold tiltedVariance
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      dsimp [b,varianceTerm]
      push_cast
      ring

#print axioms finite_third_le_six_variance
#print axioms third_moment_sharp_small
end BBFMMoment
