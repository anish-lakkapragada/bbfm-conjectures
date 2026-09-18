import BBFM.Denominator.Analytic.Parameters

noncomputable section
namespace DenominatorResearch
open Real

lemma logb_two_le_self (x : ℝ) (hx : 0 < x) : Real.logb 2 x ≤ x := by
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 2 by positivity)
  rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  unfold Real.logb
  apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).2
  have hh := mul_le_mul_of_nonneg_left hl2 hx.le
  linarith

/-- Uniform lower multiplicity throughout a radius-adapted initial block. -/
theorem den_profile_lower (n i : ℕ) (L : ℝ) (hi : 1 ≤ i) (hin : i ≤ n)
    (hL : 1 ≤ L) (hiL : (i : ℝ) ≤ L) :
    (1 + Real.logb 2 ((n : ℝ) / L)) / 2 ≤ ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL0 : 0 < L := by linarith
  have hrat : (n : ℝ) / L ≤ (n : ℝ) / i := by
    apply (div_le_div_iff₀ hL0 hi0).2
    exact mul_le_mul_of_nonneg_left hiL hn0.le
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < (n : ℝ) / L) hrat
  have hm := (multiplicity_real_bounds n i hi hin).1
  have hone : (1 : ℝ) ≤ ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.le_add_left 1 (Nat.log 2 (n / i)))
  linarith

/-- Upper profile estimate; the slightly stronger coefficient one also implies the written two. -/
theorem den_profile_upper_near (n i : ℕ) (L : ℝ) (hi : 1 ≤ i) (hin : i ≤ n)
    (hL : 0 < L) :
    ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 ((n : ℝ) / L) + L / i := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (multiplicity_real_bounds n i hi hin).2
  have heq : (n : ℝ) / i = ((n : ℝ) / L) * (L / i) := by field_simp
  rw [heq, Real.logb_mul (by positivity : (n : ℝ) / L ≠ 0) (by positivity : L / i ≠ 0)] at h
  have hl := logb_two_le_self (L / i) (by positivity)
  linarith

/-- Beyond the effective block, every multiplicity is bounded by the profile height. -/
theorem den_profile_upper_far (n i : ℕ) (L : ℝ) (hi : 1 ≤ i) (hin : i ≤ n)
    (hL : 0 < L) (hLi : L ≤ i) :
    ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 ((n : ℝ) / L) := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrat : (n : ℝ) / i ≤ (n : ℝ) / L := by
    apply (div_le_div_iff₀ hi0 hL).2
    exact mul_le_mul_of_nonneg_left hLi hn0.le
  have hl := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < (n : ℝ) / i) hrat
  have hm := (multiplicity_real_bounds n i hi hin).2
  linarith

/-- The effective large-radius size always covers half the unit multiplicity. -/
theorem effective_size_covers_unit (n : ℕ) (L : ℝ) (hn : 0 < n)
    (hL : 1 ≤ L) (hLn : L ≤ n) :
    ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 2 * ((1 + Real.logb 2 ((n : ℝ) / L)) * L) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL0 : 0 < L := by linarith
  let M := 1 + Real.logb 2 ((n : ℝ) / L)
  have hrat : (1 : ℝ) ≤ (n : ℝ) / L := by
    apply (le_div_iff₀ hL0).2
    simpa only [one_mul] using hLn
  have hM : 1 ≤ M := by
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  have heq : Real.logb 2 (n : ℝ) = M - 1 + Real.logb 2 L := by
    dsimp [M]
    rw [Real.logb_div hn0.ne' hL0.ne']
    ring
  have hl := logb_two_le_self L hL0
  have hprod := mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hL)
  have hML : 1 ≤ M * L := by nlinarith
  have ht := (multiplicity_real_bounds n 1 (by decide) (by omega)).2
  simp only [Nat.div_one, Nat.cast_one, div_one] at ht
  change ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 2 * (M * L)
  nlinarith

end DenominatorResearch
