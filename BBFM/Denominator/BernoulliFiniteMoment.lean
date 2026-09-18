import BBFM.Denominator.BernoulliPrefixMoment

/-! Finite prefix control, then Abel transfer to a decreasing profile.
This source is a new draft until its compiler receipt succeeds. -/
noncomputable section
namespace BBFMMoment
open Real Finset DenominatorResearch BBFMRelative
set_option maxHeartbeats 0

theorem finite_third_le_variance (q : ℕ) (r L : ℝ)
    (hr : 1/2 ≤ r) (hr1 : r < 1) (hL : L=1/(-Real.log r)) :
    (∑ i ∈ range q, (i : ℝ)^3*r^i) ≤
      (9/2 : ℝ)*L*(∑ i ∈ range q, varianceTerm r i) := by
  have hr0 : 0 < r := by linarith
  have ht : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr1)
  have hL0 : 0 < L := by rw [hL]; positivity
  have hLt : L*(-Real.log r)=1 := by
    rw [hL]
    have hn : Real.log r ≠ 0 := ne_of_lt (Real.log_neg hr0 hr1)
    field_simp [hn]
  by_cases hq : (q : ℝ) ≤ 4*L
  · rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hiq : (i : ℝ) ≤ q := by exact_mod_cast (mem_range.mp hi).le
    have hx : 0 ≤ (i : ℝ)*(-Real.log r) := by positivity
    have hx4 : (i : ℝ)*(-Real.log r) ≤ 4 := by
      have hh := mul_le_mul_of_nonneg_right (hiq.trans hq) ht.le
      nlinarith only [hh,hLt]
    have hphase : Real.exp (-((i : ℝ)*(-Real.log r)))=r^i := by
      have he : -((i : ℝ)*(-Real.log r))=(i : ℝ)*Real.log r := by ring
      rw [he,Real.exp_nat_mul,Real.exp_log hr0]
    have hb := scaled_bernoulli_bound ((i : ℝ)*(-Real.log r)) hx hx4
    rw [hphase] at hb
    have hc := mul_le_mul_of_nonneg_left hb hL0.le
    have hpoint : (i : ℝ)*(1+r^i)^2 ≤ (9/2 : ℝ)*L := by
      calc
        (i : ℝ)*(1+r^i)^2 = (L*(-Real.log r))*((i : ℝ)*(1+r^i)^2) := by rw [hLt]; ring
        _ = L*((i : ℝ)*(-Real.log r)*(1+r^i)^2) := by ring
        _ ≤ L*(9/2 : ℝ) := hc
        _ = _ := by ring
    unfold varianceTerm
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : 0 < (1+r^i)^2)).mpr
    have hh := mul_le_mul_of_nonneg_right hpoint (show 0 ≤ (i : ℝ)^2*r^i by positivity)
    nlinarith only [hh]
  · have hs3 := summable_pow_mul_geometric_of_norm_lt_one 3
      (r := r) (by simpa [Real.norm_eq_abs,abs_of_pos hr0] using hr1)
    have hsV := varianceTerm_summable r hr0.le hr1
    let F : ℕ → ℝ := fun i => (i : ℝ)^3*r^i-4*L*varianceTerm r i
    have hsF : Summable F := hs3.sub (hsV.mul_left (4*L))
    have htail : ∀ i, i ∉ range q → 0 ≤ F i := by
      intro i hi
      have hiq : (q : ℝ) ≤ i := by
        have hin : q ≤ i := by simpa only [mem_range,not_lt] using hi
        exact_mod_cast hin
      have hiL : 4*L ≤ i := by linarith
      have hb := mul_le_mul_of_nonneg_left (varianceTerm_bounds r hr0.le i).2
        (show 0 ≤ 4*L by positivity)
      have hh := mul_le_mul_of_nonneg_right hiL (show 0 ≤ (i : ℝ)^2*r^i by positivity)
      dsimp [F]
      nlinarith only [hb,hh]
    have hp := hsF.sum_le_tsum (range q) htail
    have htotal : (∑' i : ℕ, F i) ≤ 0 := by
      dsimp [F]
      rw [hs3.tsum_sub (hsV.mul_left (4*L)),tsum_mul_left]
      exact sub_nonpos.mpr (infinite_third_le_variance r L hr hr1 hL)
    have hsum : (∑ i ∈ range q, (i : ℝ)^3*r^i) ≤
        4*L*(∑ i ∈ range q, varianceTerm r i) := by
      have hh := hp.trans htotal
      simpa only [F,sum_sub_distrib,← mul_sum,sub_nonpos] using hh
    have hV : 0 ≤ ∑ i ∈ range q, varianceTerm r i :=
      sum_nonneg fun i _ => (varianceTerm_bounds r hr0.le i).1
    nlinarith [mul_nonneg hL0.le hV]

theorem decreasing_third_le_variance (m : ℕ → ℕ) (n : ℕ) (r L : ℝ)
    (hr : 1/2 ≤ r) (hr1 : r < 1) (hL : L=1/(-Real.log r))
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    weightedMoment m n 3 r ≤ (9/2 : ℝ)*L*tiltedVariance m n r := by
  let a : ℕ → ℝ := fun i => ((i+1 : ℕ) : ℝ)^3*r^(i+1)
  let b : ℕ → ℝ := fun i => (9/2 : ℝ)*L*varianceTerm r (i+1)
  have hp (q : ℕ) : (∑ i ∈ range q, a i) ≤ ∑ i ∈ range q, b i := by
    have hh := finite_third_le_variance (q+1) r L hr hr1 hL
    rw [sum_range_succ',sum_range_succ'] at hh
    simpa [a,b,varianceTerm,mul_sum] using hh
  have hh := weighted_prefix_le (fun i => (m (i+1) : ℝ)) a b n
    (by positivity) (fun i hi => by
      exact_mod_cast hm (i+1) (by omega) (by omega)) (fun q _ => hp q)
  calc
    weightedMoment m n 3 r = ∑ i ∈ range n, (m (i+1) : ℝ)*a i := by
      simp [weightedMoment,a,mul_assoc]
    _ ≤ ∑ i ∈ range n, (m (i+1) : ℝ)*b i := hh
    _ = (9/2 : ℝ)*L*tiltedVariance m n r := by
      unfold tiltedVariance
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      dsimp [b,varianceTerm]
      push_cast
      ring

theorem saturated_third_le_variance (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    weightedMoment m n 3 r ≤ 4*(n : ℝ)*tiltedVariance m n r := by
  unfold weightedMoment tiltedVariance
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hin : (i : ℝ)+1 ≤ n := by exact_mod_cast (mem_range.mp hi)
  have hp0 : 0 ≤ r^(i+1) := pow_nonneg hr _
  have hp1 : r^(i+1) ≤ 1 := pow_le_one₀ hr hr1
  have hd : (1+r^(i+1))^2 ≤ 4 := by nlinarith
  have hprod : ((i : ℝ)+1)*(1+r^(i+1))^2 ≤ 4*n := by
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ (i : ℝ)+1 by positivity)
    nlinarith only [hh,hin]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < (1+r^(i+1))^2)).mpr
  have hh := mul_le_mul_of_nonneg_right hprod
    (show 0 ≤ (m (i+1) : ℝ)*((i : ℝ)+1)^2*r^(i+1) by positivity)
  nlinarith only [hh]

theorem third_moment_sharp_scale (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hn : 0 < n) (hr : 1/2 < r) (hr1 : r ≤ 1)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    weightedMoment m n 3 r ≤ (9/2 : ℝ)*effectiveScale n r*tiltedVariance m n r := by
  by_cases heq : effectiveScale n r=(n : ℝ)
  · rw [heq]
    have hh := saturated_third_le_variance m n r (by linarith) hr1
    have hv : 0 ≤ tiltedVariance m n r := by unfold tiltedVariance; positivity
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) hv]
  · obtain ⟨hrlt,hscale⟩ := effectiveScale_unsaturated n r hr hr1 heq
    exact decreasing_third_le_variance m n r (effectiveScale n r) hr.le hrlt hscale hm

#print axioms finite_third_le_variance
#print axioms decreasing_third_le_variance
#print axioms third_moment_sharp_scale
end BBFMMoment
