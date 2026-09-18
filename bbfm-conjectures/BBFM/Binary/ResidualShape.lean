import BBFM.Binary.Center

open Polynomial Finset
namespace BinaryResearch

lemma numB_natDegree_le (n : ℕ) : (numB n).natDegree ≤ 2 * center n :=
  natDegree_le_iff_coeff_eq_zero.mpr (numB_support n)

lemma residual_degree_le (n : ℕ) : (residual n).natDegree ≤ 2 * center n - 1 := by
  unfold residual
  rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  apply Nat.sub_le_sub_right
  apply (natDegree_sub_le _ _).trans
  apply max_le
  · exact numB_natDegree_le n
  · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma numB_reflect (n : ℕ) : (numB n).reflect (2 * center n) = numB n := by
  ext k
  rw [coeff_reflect]
  by_cases hk : k ≤ 2 * center n
  · rw [revAt_le hk]
    exact (numB_symmetry n k hk).symm
  · rw [revAt_eq_self_of_lt (by omega)]

lemma central_remainder_reflect (n : ℕ) :
    (numB n - C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n).reflect (2 * center n) =
      numB n - C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n := by
  rw [reflect_sub, numB_reflect, reflect_C_mul_X_pow, revAt_le (by omega)]
  rw [show 2 * center n - center n = center n by omega]

/-- The residual has the odd-degree reflection required by the geometric closure lemma. -/
lemma residual_reflect (n : ℕ) (hc : 0 < center n) :
    (residual n).reflect (2 * center n - 1) = residual n := by
  have hD : 1 + (2 * center n - 1) = 2 * center n := by omega
  have hd : (1 + (X : ℤ[X])).natDegree ≤ 1 := by
    rw [add_comm, ← C_1, natDegree_X_add_C]
  have hm := reflect_mul (1 + (X : ℤ[X])) (residual n) hd (residual_degree_le n)
  rw [hD] at hm
  have hf : (1 + (X : ℤ[X])).reflect 1 = 1 + X := by
    rw [reflect_add, reflect_one, reflect_one_X]
    simp [add_comm]
  rw [hf] at hm
  apply mul_left_cancel₀ one_add_X_ne_zero
  calc
    (1 + X) * (residual n).reflect (2 * center n - 1) =
        ((1 + X) * residual n).reflect (2 * center n) := hm.symm
    _ = (numB n - C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n).reflect (2 * center n) := by
      rw [residual_identity]
    _ = numB n - C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n := central_remainder_reflect n
    _ = (1 + X) * residual n := (residual_identity n).symm

lemma residual_support (n k : ℕ) (hk : 2 * center n - 1 < k) : (residual n).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((residual_degree_le n).trans_lt hk)

lemma residual_symmetry (n k : ℕ) (hc : 0 < center n) (hk : k ≤ 2 * center n - 1) :
    (residual n).coeff k = (residual n).coeff (2 * center n - 1 - k) := by
  have h := congrArg (fun P : ℤ[X] => P.coeff k) (residual_reflect n hc)
  rw [coeff_reflect, revAt_le hk] at h
  exact h.symm

lemma residual_coeff_zero (n : ℕ) (hc : 0 < center n) : (residual n).coeff 0 = b n := by
  have h := congrArg (fun P : ℤ[X] => P.coeff 0) (residual_identity n)
  norm_num [coeff_mul, coeff_C_mul, coeff_X_pow, numB_coeff_zero, ne_of_gt hc, Ne.symm (ne_of_gt hc)] at h
  exact h

lemma center_sign_step (m : ℕ) :
    (-1 : ℤ) ^ center (2 * m + 2) = -((-1 : ℤ) ^ center (2 * m)) := by
  have h := congrArg (fun j : ℕ => (-1 : ℤ) ^ j) (center_step m)
  have hq : (-1 : ℤ) ^ jumpLength m = 1 := (jumpLength_even m).neg_one_pow
  rw [pow_add, pow_one, pow_add, hq] at h
  nlinarith [h]

#print axioms residual_degree_le
#print axioms residual_symmetry
#print axioms residual_coeff_zero
#print axioms center_sign_step
end BinaryResearch
