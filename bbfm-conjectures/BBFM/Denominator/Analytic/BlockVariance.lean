import BBFM.Denominator.Analytic.FourierDecay
import BBFM.Denominator.Analytic.Moments

noncomputable section
namespace DenominatorResearch
open Finset Real

/-- A full consecutive block gives a cubic lower variance bound for the true denominator. -/
theorem den_variance_block_lower (n q : ℕ) (r : ℝ) (hq : q ≤ n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hrq : 1 / 3 ≤ r ^ q) :
    ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * (q : ℝ) ^ 3 ≤
      36 * tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r := by
  let m := fun i => Nat.log 2 (n / i) + 1
  have hblock : (m q : ℝ) / 12 * (∑ i ∈ range q, ((i : ℝ) + 1) ^ 2) ≤
      ∑ i ∈ range q, (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 * r ^ (i + 1) /
        (1 + r ^ (i + 1)) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hiq : i + 1 ≤ q := by have := mem_range.mp hi; omega
    have hri : 1 / 3 ≤ r ^ (i + 1) := hrq.trans (pow_le_pow_of_le_one hr hrone hiq)
    have hri1 : r ^ (i + 1) ≤ 1 := pow_le_one₀ hr hrone
    have hden : 0 < (1 + r ^ (i + 1)) ^ 2 := sq_pos_of_pos (by positivity)
    have hvar : 1 / 12 ≤ r ^ (i + 1) / (1 + r ^ (i + 1)) ^ 2 := by
      apply (le_div_iff₀ hden).2
      have hs : (1 + r ^ (i + 1)) ^ 2 ≤ 4 := by nlinarith [pow_nonneg hr (i + 1)]
      nlinarith
    have hm : (m q : ℝ) ≤ m (i + 1) := by exact_mod_cast den_multiplicity_antitone n (i + 1) q (by omega) hiq
    have h1 := mul_le_mul_of_nonneg_left hvar
      (show 0 ≤ (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_right hm (show 0 ≤ ((i : ℝ) + 1) ^ 2 / 12 by positivity)
    calc
      (m q : ℝ) / 12 * ((i : ℝ) + 1) ^ 2 = (m q : ℝ) * (((i : ℝ) + 1) ^ 2 / 12) := by ring
      _ ≤ (m (i + 1) : ℝ) * (((i : ℝ) + 1) ^ 2 / 12) := h2
      _ = (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 * (1 / 12) := by ring
      _ ≤ (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 * (r ^ (i + 1) / (1 + r ^ (i + 1)) ^ 2) := h1
      _ = _ := by ring
  have hsum : (∑ i ∈ range q, (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 * r ^ (i + 1) /
        (1 + r ^ (i + 1)) ^ 2) ≤ tiltedVariance m n r := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono hq)
    intro i hi _
    positivity
  have hs := mul_le_mul_of_nonneg_left (sum_successor_sq_lower q)
    (show 0 ≤ (m q : ℝ) by positivity)
  change (m q : ℝ) * (q : ℝ) ^ 3 ≤ 36 * tiltedVariance m n r
  nlinarith

end DenominatorResearch
