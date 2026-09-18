import BBFM.Binary.LowCoefficients
import Mathlib.Data.Real.Basic

/- The generic monotone-weight inequality below is reused from the prior private c6_search audit. -/
namespace BinaryMoments
open Finset

/-- Zeroth weighted moment on `0,...,m`. -/
def mass (m : ℕ) (w : ℕ → ℝ) : ℝ := ∑ j ∈ range (m + 1), w j
/-- First weighted moment. -/
def moment₁ (m : ℕ) (w : ℕ → ℝ) : ℝ := ∑ j ∈ range (m + 1), (j : ℝ) * w j
/-- Second weighted moment. -/
def moment₂ (m : ℕ) (w : ℕ → ℝ) : ℝ := ∑ j ∈ range (m + 1), (j : ℝ)^2 * w j

lemma reflect_sum (m : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ range (m + 1), f (m - j)) = ∑ j ∈ range (m + 1), f j := by
  exact sum_range_reflect f (m + 1)

lemma mean_ge_half (m : ℕ) (w : ℕ → ℝ) (hw : Monotone w) :
    (m : ℝ) * mass m w ≤ 2 * moment₁ m w := by
  have hterm : ∀ j ∈ range (m + 1),
      0 ≤ ((2 : ℝ) * j - m) * (w j - w (m - j)) := by
    intro j hj
    have hjm : j ≤ m := by simpa using (mem_range.mp hj)
    by_cases h : m - j ≤ j
    · apply mul_nonneg
      · have : m ≤ 2 * j := by omega
        exact_mod_cast (show (0 : ℤ) ≤ 2 * (j : ℤ) - m by omega)
      · exact sub_nonneg.mpr (hw h)
    · apply mul_nonneg_of_nonpos_of_nonpos
      · have : 2 * j ≤ m := by omega
        exact_mod_cast (show 2 * (j : ℤ) - m ≤ 0 by omega)
      · exact sub_nonpos.mpr (hw (by omega))
  have hs := sum_nonneg hterm
  have hr : (∑ j ∈ range (m + 1), ((2 : ℝ) * j - m) * w (m - j)) =
      - ∑ j ∈ range (m + 1), ((2 : ℝ) * j - m) * w j := by
    calc
      _ = ∑ j ∈ range (m + 1), ((2 : ℝ) * (m - j : ℕ) - m) * w j := by
        rw [← reflect_sum m (fun j => ((2 : ℝ) * (m - j : ℕ) - m) * w j)]
        apply sum_congr rfl
        intro j hj
        have hjm : j ≤ m := Nat.le_of_lt_succ (mem_range.mp hj)
        rw [Nat.sub_sub_self hjm]
      _ = - ∑ j ∈ range (m + 1), ((2 : ℝ) * j - m) * w j := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro j hj
        rw [Nat.cast_sub (Nat.le_of_lt_succ (mem_range.mp hj))]
        ring
  have he : (∑ j ∈ range (m + 1), ((2 : ℝ) * j - m) * w j) =
      2 * moment₁ m w - (m : ℝ) * mass m w := by
    simp only [mass, moment₁, sub_mul, mul_assoc, sum_sub_distrib, mul_sum]
  simp only [mul_sub, sum_sub_distrib] at hs
  rw [hr, he] at hs
  linarith

lemma second_le_first (m : ℕ) (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j) :
    moment₂ m w ≤ (m : ℝ) * moment₁ m w := by
  unfold moment₂ moment₁
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  have hjm : (j : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (mem_range.mp hj)
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  nlinarith [mul_nonneg (hw j) (show 0 ≤ (j : ℝ) * (m - j) by positivity)]

/-- A nonnegative increasing sequence has coefficient moments satisfying the first Turan inequality. -/
theorem first_turan (m : ℕ) (w : ℕ → ℝ)
    (hw0 : ∀ j, 0 ≤ w j) (hw : Monotone w) :
    mass m w * (2 * moment₂ m w) ≤ (2 * moment₁ m w)^2 := by
  have hB : 0 ≤ mass m w := sum_nonneg fun j _ => hw0 j
  have hS : 0 ≤ moment₁ m w := sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hw0 j)
  have h1 := mean_ge_half m w hw
  have h2 := second_le_first m w hw0
  have h3 := mul_le_mul_of_nonneg_left h2 hB
  have h4 := mul_le_mul_of_nonneg_right h1 hS
  nlinarith

#print axioms first_turan
end BinaryMoments

open Polynomial Finset
namespace BinaryResearch

lemma b_even_sum (m : ℕ) : b (2 * m) = ∑ j ∈ range (m + 1), b j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, b_even, sum_range_succ, ih]

lemma coeff_one_moment (m : ℕ) :
    (numB (2 * m)).coeff 1 = 2 * ∑ j ∈ range (m + 1), (j : ℤ) * b j := by
  induction m with
  | zero => norm_num [numB_zero, coeff_one]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, coeff_one_even, sum_range_succ, ih]
    push_cast
    ring

lemma first_balance_even (m : ℕ) :
    (2 * m : ℤ) * b (2 * m) =
      (numB (2 * m)).coeff 1 + ∑ j ∈ range (2 * m), b j := by
  induction m with
  | zero => norm_num [numB_zero, coeff_one]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, b_even, coeff_one_even,
      sum_range_succ, sum_range_succ, b_odd]
    push_cast
    nlinarith [ih]

/-- Exact marked-one balance, derived from the checked source recurrence. -/
lemma first_balance (n : ℕ) :
    (n : ℤ) * b n = (numB n).coeff 1 + ∑ j ∈ range n, b j := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn]
    simpa using first_balance_even (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, b_odd, numB_odd, sum_range_succ]
    have h := first_balance_even (n / 2)
    push_cast at h ⊢
    nlinarith [h]

lemma coeff_two_even_simplified (m : ℕ) :
    (numB (2 * m + 2)).coeff 2 =
      (numB (2 * m)).coeff 2 + 2 * (m + 1 : ℤ)^2 * b (m + 1) := by
  rw [coeff_two_even]
  have hbalance := first_balance (m + 1)
  rw [← b_even_sum] at hbalance
  have hchoose : ((2 * m + 2).choose 2 : ℤ) = (m + 1 : ℤ) * (2 * m + 1) := by
    have h := Nat.choose_two_right (2 * m + 2)
    have he : (2 * m + 2).choose 2 = (m + 1) * (2 * m + 1) := by
      rw [h, show 2 * m + 2 - 1 = 2 * m + 1 by omega]
      rw [show (2 * m + 2) * (2 * m + 1) = 2 * ((m + 1) * (2 * m + 1)) by ring]
      omega
    exact_mod_cast he
  rw [hchoose]
  push_cast at hbalance
  nlinarith [hbalance]

lemma coeff_two_moment (m : ℕ) :
    (numB (2 * m)).coeff 2 = 2 * ∑ j ∈ range (m + 1), (j : ℤ)^2 * b j := by
  induction m with
  | zero => norm_num [numB_zero, coeff_one]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, coeff_two_even_simplified,
      sum_range_succ, ih]
    push_cast
    ring

/-- Unconditional first internal log-concavity inequality for the exact public numerator.
This is a single edge, not the full all-index conjecture. -/
theorem numB_first_edge_even (m : ℕ) :
    (numB (2 * m)).coeff 0 * (numB (2 * m)).coeff 2 ≤ (numB (2 * m)).coeff 1 ^ 2 := by
  rw [numB_coeff_zero, b_even_sum, coeff_one_moment, coeff_two_moment]
  have h := BinaryMoments.first_turan m (fun j => (b j : ℝ))
    (fun j => by exact_mod_cast b_nonneg j)
    (by intro i j hij; dsimp; exact_mod_cast b_mono hij)
  dsimp [BinaryMoments.mass, BinaryMoments.moment₁, BinaryMoments.moment₂] at h
  exact_mod_cast h

/-- The first edge holds for every n, by the exact odd/even equality. -/
theorem numB_first_edge (n : ℕ) :
    (numB n).coeff 0 * (numB n).coeff 2 ≤ (numB n).coeff 1 ^ 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn]
    exact numB_first_edge_even _
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, numB_odd]
    exact numB_first_edge_even _

#print axioms coeff_one_moment
#print axioms coeff_two_moment
#print axioms numB_first_edge
end BinaryResearch
