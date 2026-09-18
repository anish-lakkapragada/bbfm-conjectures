import BBFM.Denominator.Analytic.Basic

noncomputable section
namespace DenominatorResearch
open Finset

/-- Unnormalized tilted moments of the weighted factor list. -/
def weightedMoment (m : ℕ → ℕ) (n s : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ range n, (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ s * r ^ (i + 1)

def tiltedMean (m : ℕ → ℕ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ range n, (m (i + 1) : ℝ) * ((i : ℝ) + 1) * r ^ (i + 1) / (1 + r ^ (i + 1))

def tiltedVariance (m : ℕ → ℕ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ range n, (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 * r ^ (i + 1) / (1 + r ^ (i + 1)) ^ 2

lemma weightedMoment_le_of_hasSum (m : ℕ → ℕ) (n s t : ℕ) (hs : 0 < s) (r C : ℝ)
    (hr : 0 ≤ r) (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t)
    (hS : HasSum (fun i : ℕ => (i : ℝ) ^ s * r ^ i) C) :
    weightedMoment m n s r ≤ (t : ℝ) * C := by
  have hfinite : (∑ i ∈ range (n + 1), (i : ℝ) ^ s * r ^ i) ≤ C := by
    rw [← hS.tsum_eq]
    exact hS.summable.sum_le_tsum _ (fun i _ => by positivity)
  rw [sum_range_succ'] at hfinite
  simp only [Nat.cast_zero, zero_pow (Nat.ne_of_gt hs), mul_zero, zero_mul, add_zero,
    Nat.cast_add, Nat.cast_one] at hfinite
  have h1 : weightedMoment m n s r ≤
      (t : ℝ) * ∑ i ∈ range n, ((i : ℝ) + 1) ^ s * r ^ (i + 1) := by
    unfold weightedMoment
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have him : (m (i + 1) : ℝ) ≤ t := by
      exact_mod_cast hm (i + 1) (by omega) (by have := mem_range.mp hi; omega)
    have hh := mul_le_mul_of_nonneg_right him (by positivity : 0 ≤ ((i : ℝ) + 1) ^ s * r ^ (i + 1))
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left hfinite (by positivity))

lemma small_radius_moment_one (m : ℕ → ℕ) (n t : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    weightedMoment m n 1 r ≤ 4 * (t : ℝ) * r := by
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  have h := weightedMoment_le_of_hasSum m n 1 t (by decide) r _ hr hm
    (by simpa only [pow_one] using hasSum_coe_mul_geometric_of_norm_lt_one hrnorm)
  have hden : 0 < (1 - r) ^ 2 := sq_pos_of_pos (by linarith)
  have hfrac : r / (1 - r) ^ 2 ≤ 4 * r := by
    apply (div_le_iff₀ hden).2
    have hsq : 1 / 4 ≤ (1 - r) ^ 2 := by nlinarith [sq_nonneg (r - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 4 * r)]
  have hh := mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ (t : ℝ))
  nlinarith

lemma small_radius_moment_two (m : ℕ → ℕ) (n t : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    weightedMoment m n 2 r ≤ 16 * (t : ℝ) * r := by
  have hrnorm : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr]; linarith
  have h := weightedMoment_le_of_hasSum m n 2 t (by decide) r _ hr hm
    (hasSum_sq_mul_geometric_of_norm_lt_one hrnorm)
  have hden : 0 < (1 - r) ^ 3 := pow_pos (by linarith) _
  have hfrac : r * (1 + r) / (1 - r) ^ 3 ≤ 16 * r := by
    apply (div_le_iff₀ hden).2
    have hcube : (1 / 8 : ℝ) ≤ (1 - r) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : (1 / 2 : ℝ) ≤ 1 - r) 3
      norm_num at this
      exact this
    have hh := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ 16 * r)
    nlinarith [mul_nonneg hr (show 0 ≤ 1 - r by linarith)]
  have hh := mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ (t : ℝ))
  nlinarith

lemma tiltedMean_le_moment (m : ℕ → ℕ) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    tiltedMean m n r ≤ weightedMoment m n 1 r := by
  unfold tiltedMean weightedMoment
  apply sum_le_sum
  intro i hi
  simp only [pow_one]
  exact div_le_self (by positivity) (by linarith [pow_nonneg hr (i + 1)])

lemma tiltedVariance_le_moment (m : ℕ → ℕ) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    tiltedVariance m n r ≤ weightedMoment m n 2 r := by
  unfold tiltedVariance weightedMoment
  apply sum_le_sum
  intro i hi
  apply div_le_self (by positivity)
  nlinarith [pow_nonneg hr (i + 1)]

theorem small_radius_mean_le (m : ℕ → ℕ) (n t : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    tiltedMean m n r ≤ 4 * (t : ℝ) * r :=
  (tiltedMean_le_moment m n r hr).trans (small_radius_moment_one m n t r hr hrhalf hm)

theorem small_radius_variance_le (m : ℕ → ℕ) (n t : ℕ) (r : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    tiltedVariance m n r ≤ 16 * (t : ℝ) * r :=
  (tiltedVariance_le_moment m n r hr).trans (small_radius_moment_two m n t r hr hrhalf hm)

/-- The unit-weight factor gives a variance lower bound uniformly up to radius one. -/
theorem tiltedVariance_unit_lower (m : ℕ → ℕ) (n : ℕ) (r : ℝ)
    (hn : 0 < n) (hr : 0 ≤ r) (hrone : r ≤ 1) :
    (m 1 : ℝ) * r / 4 ≤ tiltedVariance m n r := by
  have hsum := Finset.single_le_sum (s := range n)
    (f := fun i : ℕ => (m (i + 1) : ℝ) * ((i : ℝ) + 1) ^ 2 * r ^ (i + 1) /
      (1 + r ^ (i + 1)) ^ 2)
    (fun i _ => by positivity) (show 0 ∈ range n by simpa using hn)
  simp only [Nat.zero_add, Nat.cast_zero, zero_add, one_pow, mul_one, pow_one] at hsum
  apply le_trans _ hsum
  have hd : 0 < (1 + r) ^ 2 := sq_pos_of_pos (by linarith)
  apply (le_div_iff₀ hd).2
  have hsq : (1 + r) ^ 2 ≤ 4 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (m 1 : ℝ) * r by positivity)
  nlinarith

/-- All three small-radius parameter estimates for the concrete BBFM multiplicities. -/
theorem den_small_radius_parameters (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    let m := fun i => Nat.log 2 (n / i) + 1
    let N := ((Nat.log 2 n + 1 : ℕ) : ℝ) * r
    tiltedMean m n r ≤ 4 * N ∧ N / 4 ≤ tiltedVariance m n r ∧
      tiltedVariance m n r ≤ 16 * N := by
  dsimp only
  have hm : ∀ i, 1 ≤ i → i ≤ n → Nat.log 2 (n / i) + 1 ≤ Nat.log 2 n + 1 := by
    intro i _ _
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1
  constructor
  · have h := small_radius_mean_le (fun i => Nat.log 2 (n / i) + 1) n
      (Nat.log 2 n + 1) r hr hrhalf hm
    nlinarith
  constructor
  · simpa only [Nat.div_one] using tiltedVariance_unit_lower
      (fun i => Nat.log 2 (n / i) + 1) n r hn hr (by linarith)
  · have h := small_radius_variance_le (fun i => Nat.log 2 (n / i) + 1) n
      (Nat.log 2 n + 1) r hr hrhalf hm
    nlinarith

end DenominatorResearch
