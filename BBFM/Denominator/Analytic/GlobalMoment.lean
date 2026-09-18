import BBFM.Denominator.Analytic.LogProfile
import BBFM.Denominator.Analytic.Moments

noncomputable section
namespace DenominatorResearch
open Finset Real

/-- A global size bound for every positive unnormalized moment of the actual profile.
In particular it gives the large-radius upper bounds when the effective scale equals n. -/
theorem den_global_moment_bound (n s : ℕ) (r : ℝ) (hr : 0 ≤ r) (hrone : r ≤ 1) :
    weightedMoment (fun i => Nat.log 2 (n / i) + 1) n (s + 1) r ≤
      2 * (n : ℝ) ^ (s + 2) := by
  by_cases hn : n = 0
  · subst n
    simp [weightedMoment]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  have hterm : ∀ i ∈ range n,
      ((Nat.log 2 (n / (i + 1)) + 1 : ℕ) : ℝ) * ((i : ℝ) + 1) ^ (s + 1) *
        r ^ (i + 1) ≤ 2 * (n : ℝ) ^ (s + 1) := by
    intro i hi
    have hiN : i + 1 ≤ n := by have := mem_range.mp hi; omega
    have hiR : (i : ℝ) + 1 ≤ n := by exact_mod_cast hiN
    have hi0 : 0 < (i : ℝ) + 1 := by positivity
    have hm := den_profile_upper_near n (i + 1) (n : ℝ) (by omega) hiN hn0
    simp only [div_self hn0.ne', Real.logb_one, add_zero, Nat.cast_add, Nat.cast_one] at hm
    have hmi : ((Nat.log 2 (n / (i + 1)) + 1 : ℕ) : ℝ) * ((i : ℝ) + 1) ≤ 2 * n := by
      have hh := mul_le_mul_of_nonneg_right hm hi0.le
      have heq : (1 + (n : ℝ) / ((i : ℝ) + 1)) * ((i : ℝ) + 1) = (i : ℝ) + 1 + n := by
        field_simp
      rw [heq] at hh
      push_cast
      linarith
    have hpow := pow_le_pow_left₀ hi0.le hiR s
    have hprod := mul_le_mul hmi hpow (by positivity : 0 ≤ ((i : ℝ) + 1) ^ s)
      (by positivity : (0 : ℝ) ≤ 2 * n)
    have hrpow : r ^ (i + 1) ≤ 1 := pow_le_one₀ hr hrone
    calc
      _ ≤ ((Nat.log 2 (n / (i + 1)) + 1 : ℕ) : ℝ) * ((i : ℝ) + 1) ^ (s + 1) :=
        mul_le_of_le_one_right (by positivity) hrpow
      _ ≤ 2 * (n : ℝ) ^ (s + 1) := by
        rw [pow_succ, pow_succ]
        nlinarith
  unfold weightedMoment
  calc
    _ ≤ ∑ i ∈ range n, 2 * (n : ℝ) ^ (s + 1) := sum_le_sum hterm
    _ = 2 * (n : ℝ) ^ (s + 2) := by simp only [sum_const, card_range, nsmul_eq_mul]; ring

end DenominatorResearch
