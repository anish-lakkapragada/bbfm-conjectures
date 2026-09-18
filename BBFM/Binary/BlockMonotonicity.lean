import BBFM.Binary.Blocks

open Polynomial Finset
namespace BinaryResearch

lemma jump_even_index (m : ℕ) : jump (2 * m) = 1 + X ^ 2 := by
  rw [jump_geometric, jumpLength_of_even (2 * m) (even_two_mul m)]
  norm_num [sum_range_succ]

lemma jump_odd_index (m : ℕ) :
    jump (2 * m + 1) = (1 + X ^ 2) * (jump m).comp (X ^ 2) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv : padicValNat 2 (2 * m + 1 + 1) = padicValNat 2 (m + 1) + 1 := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      padicValNat.mul (by decide) (by omega), padicValNat_self]
    omega
  rw [jump_carry_product, hv, prod_range_succ', jump_carry_product]
  simp only [Nat.zero_add, pow_one, Polynomial.prod_comp, add_comp, one_comp, pow_comp, X_comp]
  rw [mul_comm]
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [← pow_mul]
  congr 2
  rw [pow_succ']

lemma nonneg_comp_X_pow (P : ℤ[X]) (d : ℕ) (hd : 0 < d)
    (hP : ∀ k, 0 ≤ P.coeff k) (k : ℕ) : 0 ≤ (P.comp (X ^ d)).coeff k := by
  have he : (P.comp (X ^ d)).coeff k = if d ∣ k then P.coeff (k / d) else 0 :=
    Polynomial.coeff_expand hd P k
  rw [he]
  split_ifs
  · exact hP _
  · rfl

lemma binomial_coeff_nonneg (r k : ℕ) : 0 ≤ ((1 + X : ℤ[X]) ^ r).coeff k := by
  rw [coeff_one_add_X_pow]
  positivity

lemma two_X_coeff_nonneg (k : ℕ) : 0 ≤ ((2 : ℤ[X]) * X).coeff k := by
  rw [show (2 : ℤ[X]) * X = C (2 : ℤ) * X ^ 1 by simp, coeff_C_mul, coeff_X_pow]
  split_ifs <;> norm_num

noncomputable def blockAdvance (j : ℕ) : ℤ[X] :=
  (1 + X) ^ 2 * (numB (j + 1)).comp (X ^ 2) - jump j * (numB j).comp (X ^ 2)

lemma blockAdvance_even (m : ℕ) :
    blockAdvance (2 * m) = 2 * X * (numB (2 * m)).comp (X ^ 2) := by
  rw [blockAdvance, numB_odd, jump_even_index]
  ring

lemma blockAdvance_odd (m : ℕ) :
    blockAdvance (2 * m + 1) =
      2 * X * (jump m).comp (X ^ 2) * (numB (2 * m)).comp (X ^ 2) +
        (1 + X) ^ 2 * (1 + X ^ 2) ^ (2 * m + 2) * (numB (m + 1)).comp (X ^ 4) := by
  rw [blockAdvance, show 2 * m + 1 + 1 = 2 * m + 2 by omega,
    numB_even_recurrence, jump_odd_index, numB_odd]
  simp only [add_comp, mul_comp, pow_comp, one_comp, X_comp, comp_assoc, ← pow_mul]
  norm_num
  ring

/-- The exact neighboring-block increment is nonnegative at every coefficient. -/
theorem blockAdvance_nonneg (j k : ℕ) : 0 ≤ (blockAdvance j).coeff k := by
  rcases Nat.even_or_odd' j with ⟨m, hm | hm⟩
  · rw [hm, blockAdvance_even]
    exact coeff_mul_nonneg _ _ two_X_coeff_nonneg
      (nonneg_comp_X_pow _ 2 (by decide) (numB_nonneg _)) k
  · rw [hm, blockAdvance_odd, coeff_add]
    apply add_nonneg
    · apply coeff_mul_nonneg
      · exact coeff_mul_nonneg _ _ two_X_coeff_nonneg
          (nonneg_comp_X_pow _ 2 (by decide) (fun i => (jump_coeff_bounded m i).1))
      · exact nonneg_comp_X_pow _ 2 (by decide) (numB_nonneg _)
    · apply coeff_mul_nonneg
      · apply coeff_mul_nonneg
        · exact binomial_coeff_nonneg 2
        · have h := nonneg_comp_X_pow ((1 + X : ℤ[X]) ^ (2 * m + 2)) 2 (by decide)
            (binomial_coeff_nonneg _) 
          simpa only [pow_comp, add_comp, one_comp, X_comp] using h
      · exact nonneg_comp_X_pow _ 4 (by decide) (numB_nonneg _)

/-- Unrolled source blocks increase coefficient by coefficient. This positive
structure is exact, though it does not by itself imply log-concavity of their sum. -/
theorem sourceBlock_mono (m j : ℕ) (hj : j < m) (k : ℕ) :
    (sourceBlock m j).coeff k ≤ (sourceBlock m (j + 1)).coeff k := by
  have he : sourceBlock m (j + 1) - sourceBlock m j =
      tailFactor m (j + 1) * (1 + X) ^ (2 * j) * blockAdvance j := by
    rw [sourceBlock, sourceBlock, tailFactor_step m j hj, blockAdvance,
      show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
    ring
  have hp := coeff_mul_nonneg _ _
    (coeff_mul_nonneg _ _ (tailFactor_nonneg m (j + 1)) (binomial_coeff_nonneg (2 * j)))
    (blockAdvance_nonneg j) k
  rw [← he, coeff_sub] at hp
  omega

#print axioms sourceBlock_mono
end BinaryResearch
