import BBFM.Binary.GeometricLC
import Mathlib.Algebra.BigOperators.Intervals

open Polynomial Finset
namespace BinaryResearch

/-- The exact product of all source jumps between two even indices. -/
noncomputable def tailFactor (m j : ℕ) : ℤ[X] := ∏ i ∈ Ico j m, jump i

/-- A block groups source partitions according to their number of ones. -/
noncomputable def sourceBlock (m j : ℕ) : ℤ[X] :=
  tailFactor m j * (1 + X) ^ (2 * j) * (numB j).comp (X ^ 2)

lemma tailFactor_self (m : ℕ) : tailFactor m m = 1 := by simp [tailFactor]

lemma tailFactor_step (m j : ℕ) (hj : j < m) :
    tailFactor m j = jump j * tailFactor m (j + 1) := by
  exact prod_eq_prod_Ico_succ_bot hj jump

/-- Every partial sum of unrolled blocks is itself an exact source numerator
times a dyadic product. This introduces no surrogate recurrence. -/
theorem sourceBlock_prefix (m j : ℕ) (hj : j ≤ m) :
    (∑ i ∈ range (j + 1), sourceBlock m i) = tailFactor m j * numB (2 * j) := by
  induction j with
  | zero => simp [sourceBlock, numB_zero]
  | succ j ih =>
    rw [sum_range_succ, ih (by omega), sourceBlock, tailFactor_step m j (by omega)]
    have hr := numB_even_recurrence j
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, hr]
    ring

/-- Fully unrolled exact recurrence with all blocks centered at the source center. -/
theorem numB_unrolled (m : ℕ) : numB (2 * m) = ∑ j ∈ range (m + 1), sourceBlock m j := by
  rw [sourceBlock_prefix m m le_rfl, tailFactor_self, one_mul]

lemma coeff_mul_nonneg (P Q : ℤ[X]) (hP : ∀ k, 0 ≤ P.coeff k)
    (hQ : ∀ k, 0 ≤ Q.coeff k) (k : ℕ) : 0 ≤ (P * Q).coeff k := by
  rw [coeff_mul]
  apply sum_nonneg
  intro x hx
  exact mul_nonneg (hP _) (hQ _)

lemma tailFactor_nonneg (m j k : ℕ) : 0 ≤ (tailFactor m j).coeff k := by
  unfold tailFactor
  have hp : ∀ k, 0 ≤ (∏ i ∈ Ico j m, jump i).coeff k := by
    apply Finset.prod_induction _ (fun P : ℤ[X] => ∀ k, 0 ≤ P.coeff k)
    · intro P Q hP hQ
      exact coeff_mul_nonneg P Q hP hQ
    · intro k
      simp only [coeff_one]
      split_ifs <;> norm_num
    · intro i hi k
      exact (jump_coeff_bounded i k).1
  exact hp k

lemma sourceBlock_nonneg (m j k : ℕ) : 0 ≤ (sourceBlock m j).coeff k := by
  unfold sourceBlock
  apply coeff_mul_nonneg
  · apply coeff_mul_nonneg
    · exact tailFactor_nonneg m j
    · intro l
      rw [coeff_one_add_X_pow]
      positivity
  · intro l
    rw [comp_square_coeff]
    split_ifs
    · exact numB_nonneg _ _
    · rfl

#print axioms sourceBlock_prefix
#print axioms numB_unrolled
end BinaryResearch
