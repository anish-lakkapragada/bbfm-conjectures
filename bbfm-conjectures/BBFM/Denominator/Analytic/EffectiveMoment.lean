import BBFM.Denominator.Analytic.EffectiveScale
import BBFM.Denominator.Analytic.GlobalMoment
import BBFM.Denominator.Analytic.HigherMoment

noncomputable section
namespace DenominatorResearch
open Finset Real

lemma effectiveScale_unsaturated (n : ℕ) (r : ℝ) (hr : 1 / 2 < r)
    (hrone : r ≤ 1) (hne : effectiveScale n r ≠ (n : ℝ)) :
    r < 1 ∧ effectiveScale n r = 1 / (-Real.log r) := by
  have hrne : r ≠ 1 := by
    intro h
    subst r
    simp [effectiveScale] at hne
  refine ⟨lt_of_le_of_ne hrone hrne, ?_⟩
  simp only [effectiveScale, if_neg hrne] at hne ⊢
  exact min_eq_right (le_of_not_ge (fun h => hne (min_eq_left h)))

lemma effectiveScale_geometric_gap (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) (hne : effectiveScale n r ≠ (n : ℝ)) :
    1 / (1 - r) ≤ 2 * effectiveScale n r := by
  obtain ⟨hrlt, hrec⟩ := effectiveScale_unsaturated n r hr hrone hne
  have hr0 : 0 < r := by linarith
  have hh : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hrlt)
  have hL := (effectiveScale_bounds n r hn hr hrone).1
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
  rw [Real.log_inv] at hlog
  have hmul := mul_le_mul_of_nonneg_right hlog hr0.le
  simp only [sub_mul, inv_mul_cancel₀ hr0.ne', one_mul] at hmul
  have hscale : (-Real.log r) * effectiveScale n r = 1 := by
    rw [hrec, mul_one_div, div_self hh.ne']
  have hbound := mul_le_mul_of_nonneg_right hmul (show 0 ≤ effectiveScale n r by linarith)
  have hg : 1 ≤ 2 * effectiveScale n r * (1 - r) := by
    have heq : (-Real.log r * r) * effectiveScale n r = r := by
      calc
        _ = ((-Real.log r) * effectiveScale n r) * r := by ring
        _ = r := by rw [hscale, one_mul]
    rw [heq] at hbound
    nlinarith
  exact (div_le_iff₀ (sub_pos.mpr hrlt)).2 hg

/-- Sum the global profile m_i <= M + L/i against a positive moment. -/
lemma den_moment_le_profile_sums (n s : ℕ) (r L A B : ℝ)
    (hr : 0 ≤ r) (hL : 0 < L) (hLn : L ≤ n)
    (hA : HasSum (fun i : ℕ => (i : ℝ) ^ (s + 1) * r ^ i) A)
    (hB : HasSum (fun i : ℕ => (i : ℝ) ^ s * r ^ i) B) :
    weightedMoment (fun i => Nat.log 2 (n / i) + 1) n (s + 1) r ≤
      (1 + Real.logb 2 ((n : ℝ) / L)) * A + L * B := by
  let M := 1 + Real.logb 2 ((n : ℝ) / L)
  have hM : 0 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ) / L := (le_div_iff₀ hL).2 (by simpa using hLn)
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  have hf := hA.mul_left M |>.add (hB.mul_left L)
  have hfinite : (∑ i ∈ range (n + 1),
      (M * (i : ℝ) ^ (s + 1) * r ^ i + L * (i : ℝ) ^ s * r ^ i)) ≤ M * A + L * B := by
    have hh := hf.summable.sum_le_tsum (range (n + 1))
      (fun i _ => show 0 ≤ M * ((i : ℝ) ^ (s + 1) * r ^ i) + L * ((i : ℝ) ^ s * r ^ i) by positivity)
    rw [hf.tsum_eq] at hh
    simpa only [mul_assoc] using hh
  rw [sum_range_succ'] at hfinite
  simp only [Nat.cast_zero] at hfinite
  have hzero : 0 ≤ M * (0 : ℝ) ^ (s + 1) * r ^ 0 + L * (0 : ℝ) ^ s * r ^ 0 := by positivity
  have hs : (∑ i ∈ range n,
      (M * ((i + 1 : ℕ) : ℝ) ^ (s + 1) * r ^ (i + 1) +
       L * ((i + 1 : ℕ) : ℝ) ^ s * r ^ (i + 1))) ≤ M * A + L * B := by
    exact le_trans (le_add_of_nonneg_right hzero) hfinite
  apply le_trans _ hs
  unfold weightedMoment
  apply sum_le_sum
  intro i hi
  have hi0 : (0 : ℝ) < i + 1 := by positivity
  have hp := den_profile_upper_near n (i + 1) L (by omega)
    (by have := mem_range.mp hi; omega) hL
  change _ ≤ M + L / ((i + 1 : ℕ) : ℝ) at hp
  have hm := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ ((i + 1 : ℕ) : ℝ) ^ (s + 1) * r ^ (i + 1) by positivity)
  have heq : (M + L / ((i + 1 : ℕ) : ℝ)) *
      (((i + 1 : ℕ) : ℝ) ^ (s + 1) * r ^ (i + 1)) =
      M * ((i + 1 : ℕ) : ℝ) ^ (s + 1) * r ^ (i + 1) +
      L * ((i + 1 : ℕ) : ℝ) ^ s * r ^ (i + 1) := by
    rw [pow_succ]
    field_simp
  rw [heq] at hm
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hm

lemma geometric_moments_effective (r L : ℝ) (hr : 0 ≤ r) (hrlt : r < 1)
    (hL : 0 ≤ L) (hgap : 1 / (1 - r) ≤ 2 * L) :
    r / (1 - r) ^ 2 ≤ 4 * L ^ 2 ∧
    r * (1 + r) / (1 - r) ^ 3 ≤ 16 * L ^ 3 ∧
    r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 ≤ 96 * L ^ 4 := by
  have hd : 0 < 1 - r := by linarith
  have hpow (s : ℕ) : (1 / (1 - r)) ^ s ≤ (2 * L) ^ s :=
    pow_le_pow_left₀ (by positivity) hgap s
  have h1 : r ≤ 1 := hrlt.le
  have h2 : r * (1 + r) ≤ 2 := by nlinarith
  have h3 : r * (1 + 4 * r + r ^ 2) ≤ 6 := by
    have hs : r ^ 2 ≤ 1 := pow_le_one₀ hr h1
    have hh := mul_le_mul_of_nonneg_left (show 1 + 4 * r + r ^ 2 ≤ 6 by linarith) hr
    nlinarith
  constructor
  · calc
      _ = r * (1 / (1 - r)) ^ 2 := by rw [div_pow]; ring
      _ ≤ 1 * (2 * L) ^ 2 := mul_le_mul h1 (hpow 2) (by positivity) (by norm_num)
      _ = _ := by ring
  constructor
  · calc
      _ = (r * (1 + r)) * (1 / (1 - r)) ^ 3 := by rw [div_pow]; ring
      _ ≤ 2 * (2 * L) ^ 3 := mul_le_mul h2 (hpow 3) (by positivity) (by norm_num)
      _ = _ := by ring
  · calc
      _ = (r * (1 + 4 * r + r ^ 2)) * (1 / (1 - r)) ^ 4 := by rw [div_pow]; ring
      _ ≤ 6 * (2 * L) ^ 4 := mul_le_mul h3 (hpow 4) (by positivity) (by norm_num)
      _ = _ := by ring

/-- Concrete large-radius moments, including both saturated and unsaturated scales. -/
theorem den_large_radius_moments (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) :
    let L := effectiveScale n r
    let M := 1 + Real.logb 2 ((n : ℝ) / L)
    weightedMoment (fun i => Nat.log 2 (n / i) + 1) n 2 r ≤ 20 * M * L ^ 3 ∧
    weightedMoment (fun i => Nat.log 2 (n / i) + 1) n 3 r ≤ 112 * M * L ^ 4 := by
  dsimp only
  let L := effectiveScale n r
  let M := 1 + Real.logb 2 ((n : ℝ) / L)
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨hL, hLn, _⟩ := effectiveScale_bounds n r hn hr hrone
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hM : 1 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ) / L := (le_div_iff₀ hL0).2 (by simpa using hLn)
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  change _ ≤ 20 * M * L ^ 3 ∧ _ ≤ 112 * M * L ^ 4
  by_cases heq : L = (n : ℝ)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hMeq : M = 1 := by simp [M, heq, div_self hn0.ne']
    rw [heq, hMeq]
    have htwo := den_global_moment_bound n 1 r hr0 hrone
    have hthree := den_global_moment_bound n 2 r hr0 hrone
    norm_num at htwo hthree
    constructor <;> nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 3,
      pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 4]
  · have hunsat := effectiveScale_unsaturated n r hr hrone heq
    have hgap := effectiveScale_geometric_gap n r hn hr hrone heq
    have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hunsat.1
    have hgeom := geometric_moments_effective r L hr0 hunsat.1 hL0.le hgap
    have htwo := den_moment_le_profile_sums n 1 r L _ _ hr0 hL0 hLn
      (hasSum_sq_mul_geometric_of_norm_lt_one hnorm)
      (by simpa only [pow_one] using hasSum_coe_mul_geometric_of_norm_lt_one hnorm)
    have hthree := den_moment_le_profile_sums n 2 r L _ _ hr0 hL0 hLn
      (hasSum_cube_mul_geometric r hnorm)
      (hasSum_sq_mul_geometric_of_norm_lt_one hnorm)
    change _ ≤ M * _ + L * _ at htwo hthree
    have hM0 : 0 ≤ M := by linarith
    have ha := mul_le_mul_of_nonneg_left hgeom.1 hL0.le
    have hb := mul_le_mul_of_nonneg_left hgeom.2.1 hM0
    have hc := mul_le_mul_of_nonneg_left hgeom.2.1 hL0.le
    have hd := mul_le_mul_of_nonneg_left hgeom.2.2 hM0
    have he := mul_le_mul_of_nonneg_right hM (pow_nonneg hL0.le 3)
    have hf := mul_le_mul_of_nonneg_right hM (pow_nonneg hL0.le 4)
    constructor <;> nlinarith

end DenominatorResearch
