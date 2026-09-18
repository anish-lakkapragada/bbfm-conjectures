import BBFM.Denominator.Analytic.BlockVariance
import BBFM.Denominator.Analytic.LogProfile

noncomputable section
namespace DenominatorResearch
open Real

lemma floor_ge_half (L : ℝ) (hL : 1 ≤ L) : L / 2 ≤ (⌊L⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊L⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff L).2 hL
  by_cases hh : L ≤ 2
  · linarith
  · have hf := Nat.lt_floor_add_one L
    linarith

/-- The logarithmic radius condition supplies the required nonnegligible block probabilities. -/
theorem radius_floor_pow_lower (r L : ℝ) (hr : 0 < r) (hrone : r ≤ 1)
    (hL : 0 ≤ L) (hscale : (-Real.log r) * L ≤ 1) :
    (1 / 3 : ℝ) ≤ r ^ ⌊L⌋₊ := by
  have hlog : 0 ≤ -Real.log r := neg_nonneg.mpr (Real.log_nonpos hr.le hrone)
  have hq := mul_le_mul_of_nonneg_left (Nat.floor_le hL) hlog
  have he : (1 / 3 : ℝ) < Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (lt_div_iff₀ (Real.exp_pos 1)).2
    nlinarith [Real.exp_one_lt_three]
  calc
    (1 / 3 : ℝ) ≤ Real.exp (-1) := he.le
    _ ≤ Real.exp ((⌊L⌋₊ : ℝ) * Real.log r) := Real.exp_le_exp.mpr (by nlinarith)
    _ = r ^ ⌊L⌋₊ := by rw [Real.exp_nat_mul, Real.exp_log hr]

/-- Uniform variance lower bound for the actual effective block, including nonintegral L.
This improves the written proof's 1000 denominator to 576 and removes its small-L split. -/
theorem den_effective_variance_lower (n : ℕ) (r L : ℝ) (hL : 1 ≤ L) (hLn : L ≤ n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hrq : 1 / 3 ≤ r ^ ⌊L⌋₊) :
    (1 + Real.logb 2 ((n : ℝ) / L)) * L ^ 3 ≤
      576 * tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r := by
  have hL0 : 0 ≤ L := by linarith
  have hqL := Nat.floor_le hL0
  have hqn : ⌊L⌋₊ ≤ n := by exact_mod_cast hqL.trans hLn
  have hq1 : 1 ≤ ⌊L⌋₊ := (Nat.one_le_floor_iff L).2 hL
  have hM := den_profile_lower n ⌊L⌋₊ L hq1 hqn hL hqL
  have hv := den_variance_block_lower n ⌊L⌋₊ r hqn hr hrone hrq
  have hq := floor_ge_half L hL
  have hqcube := pow_le_pow_left₀ (show 0 ≤ L / 2 by positivity) hq 3
  have hM0 : 0 ≤ 1 + Real.logb 2 ((n : ℝ) / L) := by
    have hnratio : (1 : ℝ) ≤ (n : ℝ) / L := by
      apply (le_div_iff₀ (by linarith : 0 < L)).2
      simpa only [one_mul] using hLn
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hnratio
    linarith
  have hm0 : 0 ≤ ((Nat.log 2 (n / ⌊L⌋₊) + 1 : ℕ) : ℝ) := by positivity
  have hh := mul_le_mul hM hqcube (by positivity : (0 : ℝ) ≤ (L / 2) ^ 3) hm0
  nlinarith

end DenominatorResearch
