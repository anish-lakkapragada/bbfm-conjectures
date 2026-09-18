import BBFM.Binary.Jump
import BBFM.Binary.LowCoefficients
import BBFM.Binary.Symmetry
import Mathlib.Algebra.Polynomial.Div

open Polynomial Finset
namespace BinaryResearch

noncomputable def amplitude (n : ℕ) : ℤ := (numB n).eval (-1)

lemma jump_eval_neg_one (m : ℕ) : (jump m).eval (-1) = jumpLength m := by
  rw [jump_geometric]
  simp [eval_finsetSum, pow_mul]

lemma amplitude_odd (m : ℕ) : amplitude (2 * m + 1) = amplitude (2 * m) := by
  unfold amplitude
  rw [numB_odd]

lemma amplitude_even (m : ℕ) :
    amplitude (2 * m + 2) = (jumpLength m : ℤ) * amplitude (2 * m) := by
  unfold amplitude
  rw [numB_even_recurrence]
  simp [jump_eval_neg_one]

lemma amplitude_even_formula (m : ℕ) :
    amplitude (2 * m) = (2 : ℤ) ^ (m + padicValNat 2 m.factorial) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction m with
  | zero => norm_num [amplitude, numB_zero]
  | succ m ih =>
    have hf : padicValNat 2 (m + 1).factorial =
        padicValNat 2 (m + 1) + padicValNat 2 m.factorial := by
      rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero _)]
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, amplitude_even, ih, hf]
    unfold jumpLength
    push_cast
    rw [← pow_add]
    congr 1
    omega

lemma amplitude_even_bound (m : ℕ) : 0 < amplitude (2 * m) ∧ amplitude (2 * m) ≤ 2 ^ (2 * m) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [amplitude_even_formula]
  constructor
  · positivity
  · apply pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2)
    have h := padicValNat_factorial_le (p := 2) m
    omega

/-- Exact source evaluation, with the uniform exponential bound needed for residual correction. -/
theorem amplitude_bounds (n : ℕ) : 0 < amplitude n ∧ amplitude n ≤ 2 ^ n := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · have hn : n = 2 * (n / 2) := by omega
    rw [hn]
    exact amplitude_even_bound _
  · have hn : n = 2 * (n / 2) + 1 := by omega
    rw [hn, amplitude_odd]
    have h := amplitude_even_bound (n / 2)
    exact ⟨h.1, h.2.trans (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega))⟩

/-- Residual after subtracting the central value responsible for the nonzero evaluation at -1. -/
noncomputable def residual (n : ℕ) : ℤ[X] :=
  (numB n - C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n) /ₘ (X - C (-1))

/-- Exact polynomial division, without any divisibility assumption. -/
theorem residual_identity (n : ℕ) :
    (1 + X) * residual n = numB n - C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n := by
  have he : (1 + (X : ℤ[X])) = X - C (-1) := by simp; ring
  rw [he]
  unfold residual
  apply mul_divByMonic_eq_iff_isRoot.mpr
  unfold IsRoot
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  have hsign : ((-1 : ℤ) ^ center n) * (-1) ^ center n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  change amplitude n - ((-1 : ℤ) ^ center n * amplitude n) * (-1) ^ center n = 0
  rw [show ((-1 : ℤ) ^ center n * amplitude n) * (-1) ^ center n =
    amplitude n * ((-1 : ℤ) ^ center n * (-1) ^ center n) by ring, hsign]
  ring

#print axioms amplitude_even_formula
#print axioms amplitude_bounds
#print axioms residual_identity
end BinaryResearch
