import BBFM.Binary.ResidualShape

open Polynomial Finset
namespace BinaryResearch

/-- Finite correction introduced when dividing the even recurrence by `1+X`. -/
noncomputable def correction (m : ℕ) : ℤ[X] :=
  (jump m + C (jumpLength m : ℤ) * X ^ (jumpLength m - 1)) /ₘ (X - C (-1))

lemma jumpLength_two_le (m : ℕ) : 2 ≤ jumpLength m := by
  have hp := jumpLength_pos m
  obtain ⟨r, hr⟩ := jumpLength_even m
  omega

lemma correction_identity (m : ℕ) :
    (1 + X) * correction m = jump m + C (jumpLength m : ℤ) * X ^ (jumpLength m - 1) := by
  have hq : (-1 : ℤ) ^ jumpLength m = 1 := (jumpLength_even m).neg_one_pow
  have hp : (-1 : ℤ) ^ (jumpLength m - 1) = -1 := by
    rw [show jumpLength m = (jumpLength m - 1) + 1 by have := jumpLength_pos m; omega,
      pow_add, pow_one] at hq
    nlinarith [hq]
  have he : (1 + (X : ℤ[X])) = X - C (-1) := by simp; ring
  rw [he]
  unfold correction
  apply mul_divByMonic_eq_iff_isRoot.mpr
  unfold IsRoot
  rw [eval_add, eval_mul, eval_C, eval_pow, eval_X, jump_eval_neg_one, hp]
  ring

/-- The exact residual recurrence, with all source normalizations and centers proved. -/
theorem residual_recurrence (m : ℕ) :
    residual (2 * m + 2) =
      jump m * residual (2 * m) +
      (1 + X) ^ (2 * m + 1) * (numB (m + 1)).comp (X ^ 2) +
      C ((-1 : ℤ) ^ center (2 * m) * amplitude (2 * m)) *
        X ^ center (2 * m) * correction m := by
  apply mul_left_cancel₀ one_add_X_ne_zero
  rw [residual_identity]
  have hc : center (2 * m + 2) = center (2 * m) + (jumpLength m - 1) := by
    have h := center_step m
    have hq := jumpLength_pos m
    omega
  have he : (1 + X) *
      (jump m * residual (2 * m) +
        (1 + X) ^ (2 * m + 1) * (numB (m + 1)).comp (X ^ 2) +
        C ((-1 : ℤ) ^ center (2 * m) * amplitude (2 * m)) * X ^ center (2 * m) * correction m) =
      jump m * ((1 + X) * residual (2 * m)) +
        (1 + X) ^ (2 * m + 2) * (numB (m + 1)).comp (X ^ 2) +
        C ((-1 : ℤ) ^ center (2 * m) * amplitude (2 * m)) * X ^ center (2 * m) *
          ((1 + X) * correction m) := by
    rw [show 2 * m + 2 = (2 * m + 1) + 1 by omega, pow_succ]
    ring
  rw [he, residual_identity, correction_identity, numB_even_recurrence,
    amplitude_even, center_sign_step, hc, pow_add]
  simp only [map_mul, map_neg]
  ring

#print axioms correction_identity
#print axioms residual_recurrence
end BinaryResearch
