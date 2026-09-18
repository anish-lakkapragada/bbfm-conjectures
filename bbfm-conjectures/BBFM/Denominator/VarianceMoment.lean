import BBFM.Denominator.Analytic.LargeRadiusTaylor

/-! Variance-relative moment estimates for the denominator effective scale. -/

noncomputable section
namespace BBFMRelative
open Finset Polynomial Real DenominatorResearch
set_option maxHeartbeats 0

/-- Summation by parts controls a third moment by a second moment for every
decreasing multiplicity profile; no bound on its largest weight is needed. -/
theorem geometric_third_moment (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    (1-r)*weightedMoment m n 3 r ≤ 3*weightedMoment m n 2 r := by
  let T : ℕ → ℝ := fun N => ∑ i ∈ range N, (m (i+1) : ℝ) * (i : ℝ)^3 * r^(i+1)
  have hT : T n ≤ T (n+1) := by
    dsimp [T]
    rw [sum_range_succ]
    have hh : 0 ≤ (m (n+1) : ℝ) * (n : ℝ)^3 * r^(n+1) := by positivity
    linarith
  have hshift : T (n+1) = r * ∑ i ∈ range n,
      (m (i+2) : ℝ) * ((i : ℝ)+1)^3 * r^(i+1) := by
    dsimp [T]
    rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_pow (by decide : 3 ≠ 0), mul_zero, zero_mul, add_zero]
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    simp only [Nat.cast_add, Nat.cast_one, pow_succ, Nat.add_assoc]
    ring
  have hmono : T (n+1) ≤ r * weightedMoment m n 3 r := by
    rw [hshift]
    apply mul_le_mul_of_nonneg_left _ hr
    unfold weightedMoment
    apply sum_le_sum
    intro i hi
    have hh : (m (i+2) : ℝ) ≤ m (i+1) := by
      exact_mod_cast hm (i+1) (by omega) (by have := mem_range.mp hi; omega)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (by positivity)) (pow_nonneg hr _)
  have hpoly : weightedMoment m n 3 r - T n ≤ 3 * weightedMoment m n 2 r := by
    unfold weightedMoment
    dsimp [T]
    rw [← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro i hi
    have hi0 : 0 ≤ (i : ℝ) := by positivity
    have hbase : ((i : ℝ)+1)^3 - (i : ℝ)^3 ≤ 3*((i : ℝ)+1)^2 := by
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hbase
      (show 0 ≤ (m (i+1) : ℝ)*r^(i+1) by positivity)
    nlinarith only [hh]
  nlinarith only [hT, hmono, hpoly]

theorem third_moment_of_max_weight (m : ℕ → ℕ) (n : ℕ) (r L : ℝ)
    (hr : 0 ≤ r) (hn : (n : ℝ) ≤ L) :
    weightedMoment m n 3 r ≤ L * weightedMoment m n 2 r := by
  unfold weightedMoment
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hiL : (i : ℝ)+1 ≤ L := by
    have hh : (i : ℝ)+1 ≤ n := by exact_mod_cast mem_range.mp hi
    exact hh.trans hn
  have hh := mul_le_mul_of_nonneg_right hiL
    (show 0 ≤ (m (i+1) : ℝ)*((i : ℝ)+1)^2*r^(i+1) by positivity)
  nlinarith only [hh]

theorem second_moment_le_four_variance (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrone : r ≤ 1) :
    weightedMoment m n 2 r ≤ 4 * tiltedVariance m n r := by
  unfold weightedMoment tiltedVariance
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hp0 : 0 ≤ r^(i+1) := pow_nonneg hr _
  have hp1 : r^(i+1) ≤ 1 := pow_le_one₀ hr hrone
  have hd : 0 < (1+r^(i+1))^2 := by positivity
  have hs : (1+r^(i+1))^2 ≤ 4 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ (m (i+1) : ℝ)*((i : ℝ)+1)^2*r^(i+1) by positivity)
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  nlinarith only [hh]

/-- The actual exponential scale differs from the geometric scale by at
most a factor two. -/
lemma geometric_scale_le_twice (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1/2 < r) (hrone : r ≤ 1)
    (hne : effectiveScale n r ≠ (n : ℝ)) :
    1 ≤ 2 * effectiveScale n r * (1-r) := by
  obtain ⟨hrlt, hscale⟩ := effectiveScale_unsaturated n r hr hrone hne
  have hr0 : 0 < r := by linarith
  have hg : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hrlt)
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at hlog
  have hlog' : -Real.log r ≤ 2*(1-r) := by
    have hh := (mul_le_mul_of_nonneg_right hlog hr0.le)
    have hir : r⁻¹*r = 1 := inv_mul_cancel₀ hr0.ne'
    have hg0 : 0 ≤ -Real.log r := hg.le
    nlinarith [mul_inv_cancel₀ hr0.ne']
  rw [hscale]
  have hh := mul_le_mul_of_nonneg_right hlog' (show 0 ≤ 1/(-Real.log r) by positivity)
  have hrec : (-Real.log r)*(1/(-Real.log r)) = 1 := by rw [mul_one_div,div_self hg.ne']
  nlinarith only [hh,hrec]

theorem third_moment_le_scale_variance (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hn : 0 < n) (hr : 1/2 < r) (hrone : r ≤ 1)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    weightedMoment m n 3 r ≤ 24 * effectiveScale n r * tiltedVariance m n r := by
  let L := effectiveScale n r
  have hL : 0 ≤ L := by
    have hh := (effectiveScale_bounds n r hn hr hrone).1
    dsimp [L]
    linarith
  have hr0 : 0 ≤ r := by linarith
  have hM2 : 0 ≤ weightedMoment m n 2 r := by
    unfold weightedMoment
    exact sum_nonneg fun i hi => by positivity
  have hM3 : 0 ≤ weightedMoment m n 3 r := by
    unfold weightedMoment
    exact sum_nonneg fun i hi => by positivity
  have hfirst : weightedMoment m n 3 r ≤ 6*L*weightedMoment m n 2 r := by
    by_cases heq : L = (n : ℝ)
    · have hh := third_moment_of_max_weight m n r L hr0 (by linarith)
      have hz := mul_nonneg hL hM2
      nlinarith only [hh,hz]
    · have hg := geometric_scale_le_twice n r hn hr hrone heq
      have hs := geometric_third_moment m n r hr0 hm
      have hp := mul_le_mul_of_nonneg_right hg hM3
      have hq := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*L by positivity)
      change 1 ≤ 2*L*(1-r) at hg
      nlinarith only [hp,hq]
  have hsecond := second_moment_le_four_variance m n r hr0 hrone
  have hh := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 6*L by positivity)
  change _ ≤ 24*L*_
  nlinarith only [hfirst,hh]

theorem third_moment_le_variance_small (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    weightedMoment m n 3 r ≤ 24 * tiltedVariance m n r := by
  have hM3 : 0 ≤ weightedMoment m n 3 r := by
    unfold weightedMoment
    exact sum_nonneg fun i hi => by positivity
  have hs := geometric_third_moment m n r hr hm
  have hsecond := second_moment_le_four_variance m n r hr (by linarith)
  have hh := mul_le_mul_of_nonneg_right (show (1/2 : ℝ) ≤ 1-r by linarith) hM3
  nlinarith only [hs,hsecond,hh]

#print axioms geometric_third_moment
#print axioms third_moment_le_scale_variance
#print axioms third_moment_le_variance_small
end BBFMRelative
