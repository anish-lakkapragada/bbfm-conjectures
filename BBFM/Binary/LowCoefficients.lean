import BBFM.Binary.Recurrence
import Mathlib.Algebra.Polynomial.Expand

/- Generic low-coefficient lemmas copied from the prior private c6_structure audit.
   New source-level consequences begin after this namespace. -/
open Polynomial Finset
namespace BinarySummandCoefficients

noncomputable def product (e : ℕ → ℕ) (L : ℕ) : ℤ[X] :=
  ∏ j ∈ range L, (1 + X ^ (2 ^ j)) ^ e j

lemma coeff_mul_high_factor (P : ℤ[X]) (s r k : ℕ) (hk : k < s) :
    (P * (1 + X ^ s) ^ r).coeff k = P.coeff k := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, ← mul_assoc, mul_add, mul_one, coeff_add, coeff_mul_X_pow']
    simp only [ite_eq_right (Nat.not_le.mpr hk), add_zero]
    exact ih

lemma truncate (e : ℕ → ℕ) (L k : ℕ) (hL : 2 ≤ L) (hk : k ≤ 3) :
    (product e L).coeff k = (product e 2).coeff k := by
  induction L, hL using Nat.le_induction with
  | base => rfl
  | succ L hL ih =>
    rw [product, prod_range_succ]
    rw [coeff_mul_high_factor]
    · exact ih
    · have hp : 2 ^ 2 ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hL
      omega

lemma coeff_one_add_X_pow_pow (s r k : ℕ) (hs : 0 < s) :
    ((1 + (X : ℤ[X]) ^ s) ^ r).coeff k =
      if s ∣ k then (r.choose (k / s) : ℤ) else 0 := by
  have h := coeff_expand hs ((1 + (X : ℤ[X])) ^ r) k
  simpa [map_pow, map_add, coeff_one_add_X_pow] using h

lemma product_two_coeff_one (e : ℕ → ℕ) :
    (product e 2).coeff 1 = (e 0 : ℤ) := by
  norm_num [product, prod_range_succ, coeff_mul, Nat.antidiagonal_succ,
    coeff_one_add_X_pow_pow, coeff_one_add_X_pow]

lemma product_two_coeff_two (e : ℕ → ℕ) :
    (product e 2).coeff 2 = ((e 0).choose 2 : ℤ) + e 1 := by
  norm_num [product, prod_range_succ, coeff_mul, Nat.antidiagonal_succ,
    coeff_one_add_X_pow_pow, coeff_one_add_X_pow]
  ring

lemma product_two_coeff_three (e : ℕ → ℕ) :
    (product e 2).coeff 3 = ((e 0).choose 3 : ℤ) + (e 0 : ℤ) * e 1 := by
  norm_num [product, prod_range_succ, coeff_mul, Nat.antidiagonal_succ,
    coeff_one_add_X_pow_pow, coeff_one_add_X_pow]
  ring

end BinarySummandCoefficients

namespace BinaryResearch

lemma jump_coeff_zero (m : ℕ) : (jump m).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  unfold jump
  rw [eval_prod]
  apply Finset.prod_eq_one
  intro j hj
  rw [eval_pow, eval_add, eval_one, eval_pow, eval_X]
  simp

lemma jump_coeff_one (m : ℕ) : (jump m).coeff 1 = 0 := by
  change (BinarySummandCoefficients.product _ (2 * m + 3)).coeff 1 = 0
  rw [BinarySummandCoefficients.truncate _ _ _ (by omega) (by omega),
    BinarySummandCoefficients.product_two_coeff_one]
  simp

lemma jump_coeff_two (m : ℕ) : (jump m).coeff 2 = 1 := by
  change (BinarySummandCoefficients.product _ (2 * m + 3)).coeff 2 = 1
  rw [BinarySummandCoefficients.truncate _ _ _ (by omega) (by omega),
    BinarySummandCoefficients.product_two_coeff_two]
  norm_num

lemma comp_square_coeff (P : ℤ[X]) (k : ℕ) :
    (P.comp (X ^ 2)).coeff k = if 2 ∣ k then P.coeff (k / 2) else 0 := by
  exact coeff_expand (by omega : 0 < 2) P k

lemma numB_zero : numB 0 = 1 := by
  have hb : binaryPartitions 0 = {(default : Nat.Partition 0)} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => by simp at hi⟩,
        fun p _ => Subsingleton.elim p _⟩
  simp [numB, hb, hBPartition]

/-- Counts are represented in the same coefficient ring as the source numerator. -/
noncomputable def b (n : ℕ) : ℤ := Fintype.card (Part n)

lemma b_nonneg (n : ℕ) : 0 ≤ b n := by unfold b; positivity
lemma b_mono : Monotone b := by
  apply monotone_nat_of_le_succ
  intro n
  unfold b
  exact_mod_cast Fintype.card_le_of_injective (@appendOne n) (appendOne_injective n)

lemma hBPartition_coeff_zero (n : ℕ) (p : Nat.Partition n) :
    (hBPartition n p).coeff 0 = 1 := by
  simp [hBPartition, coeff_zero_eq_eval_zero, eval_prod]

lemma numB_coeff_zero (n : ℕ) : (numB n).coeff 0 = b n := by
  classical
  rw [numerator_eq_sum, finsetSum_coeff]
  simp [hBPartition_coeff_zero, b]

lemma b_zero : b 0 = 1 := by rw [← numB_coeff_zero, numB_zero]; simp
lemma b_odd (m : ℕ) : b (2 * m + 1) = b (2 * m) := by
  rw [← numB_coeff_zero, numB_odd, numB_coeff_zero]

lemma b_even (m : ℕ) : b (2 * m + 2) = b (2 * m) + b (m + 1) := by
  rw [← numB_coeff_zero, numB_even_recurrence]
  norm_num [coeff_mul, Nat.antidiagonal_succ, coeff_one_add_X_pow,
    jump_coeff_zero, comp_square_coeff, numB_coeff_zero]

lemma coeff_one_even (m : ℕ) :
    (numB (2 * m + 2)).coeff 1 =
      (numB (2 * m)).coeff 1 + (2 * m + 2 : ℤ) * b (m + 1) := by
  rw [numB_even_recurrence]
  norm_num [coeff_mul, Nat.antidiagonal_succ, coeff_one_add_X_pow,
    jump_coeff_zero, jump_coeff_one, comp_square_coeff, numB_coeff_zero]

lemma coeff_two_even (m : ℕ) :
    (numB (2 * m + 2)).coeff 2 =
      (numB (2 * m)).coeff 2 + b (2 * m) +
        ((2 * m + 2).choose 2 : ℤ) * b (m + 1) + (numB (m + 1)).coeff 1 := by
  rw [numB_even_recurrence]
  norm_num [coeff_mul, Nat.antidiagonal_succ, coeff_one_add_X_pow,
    jump_coeff_zero, jump_coeff_one, jump_coeff_two, comp_square_coeff, numB_coeff_zero]
  ring

#print axioms b_even
#print axioms coeff_one_even
#print axioms coeff_two_even
end BinaryResearch
