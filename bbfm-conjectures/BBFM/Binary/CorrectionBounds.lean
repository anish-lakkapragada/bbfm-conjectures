import BBFM.Binary.ResidualRecurrence

open Polynomial Finset
namespace BinaryResearch

lemma jump_coeff_bounded (m k : ℕ) : 0 ≤ (jump m).coeff k ∧ (jump m).coeff k ≤ 1 := by
  rw [jump_geometric, finsetSum_coeff]
  by_cases he : ∃ r ∈ range (jumpLength m), 2 * r = k
  · obtain ⟨r, hr, hk⟩ := he
    have hv : (∑ j ∈ range (jumpLength m), ((X : ℤ[X]) ^ (2 * j)).coeff k) = 1 := by
      rw [sum_eq_single r]
      · simp [hk]
      · intro j hj hjr
        have hn : 2 * j ≠ k := by omega
        simp [coeff_X_pow, Ne.symm hn]
      · exact fun h => (h hr).elim
    rw [hv]
    omega
  · have hv : (∑ j ∈ range (jumpLength m), ((X : ℤ[X]) ^ (2 * j)).coeff k) = 0 := by
      apply sum_eq_zero
      intro j hj
      have hn : 2 * j ≠ k := fun h => he ⟨j, hj, h⟩
      simp [coeff_X_pow, Ne.symm hn]
    rw [hv]
    omega

lemma jump_reverse (m : ℕ) : (jump m).reverse = jump m := by
  rw [jump_carry_product]
  apply Finset.prod_induction _ (fun P : ℤ[X] => P.reverse = P)
  · intro P Q hP hQ
    rw [reverse_mul_of_domain, hP, hQ]
  · simpa only [map_one] using (reverse_C (1 : ℤ))
  · intro j hj
    exact reverse_one_add_X_pow _ (by positivity)

lemma jump_natDegree (m : ℕ) : (jump m).natDegree = 2 * jumpLength m - 2 := by
  have h := jump_degree m
  have hq := jumpLength_two_le m
  omega

lemma correction_degree_le (m : ℕ) : (correction m).natDegree ≤ 2 * jumpLength m - 3 := by
  unfold correction
  rw [natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  have hq := jumpLength_two_le m
  have hb : (jump m + C (jumpLength m : ℤ) * X ^ (jumpLength m - 1)).natDegree ≤
      2 * jumpLength m - 2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · rw [jump_natDegree]
    · exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  omega

lemma correction_reflect (m : ℕ) :
    (correction m).reflect (2 * jumpLength m - 3) = correction m := by
  have hq := jumpLength_two_le m
  have hj : (jump m).reflect (2 * jumpLength m - 2) = jump m := by
    have h := jump_reverse m
    rw [reverse, jump_natDegree] at h
    exact h
  have hnum : (jump m + C (jumpLength m : ℤ) * X ^ (jumpLength m - 1)).reflect
      (2 * jumpLength m - 2) = jump m + C (jumpLength m : ℤ) * X ^ (jumpLength m - 1) := by
    rw [reflect_add, hj, reflect_C_mul_X_pow, revAt_le (by omega)]
    rw [show 2 * jumpLength m - 2 - (jumpLength m - 1) = jumpLength m - 1 by omega]
  have hd : (1 + (X : ℤ[X])).natDegree ≤ 1 := by
    rw [add_comm, ← C_1, natDegree_X_add_C]
  have hm := reflect_mul (1 + (X : ℤ[X])) (correction m) hd (correction_degree_le m)
  rw [show 1 + (2 * jumpLength m - 3) = 2 * jumpLength m - 2 by omega] at hm
  have hf : (1 + (X : ℤ[X])).reflect 1 = 1 + X := by
    rw [reflect_add, reflect_one, reflect_one_X]
    simp [add_comm]
  rw [hf] at hm
  apply mul_left_cancel₀ one_add_X_ne_zero
  calc
    (1 + X) * (correction m).reflect (2 * jumpLength m - 3) =
        ((1 + X) * correction m).reflect (2 * jumpLength m - 2) := hm.symm
    _ = _ := by rw [correction_identity, hnum]

lemma correction_symmetry (m k : ℕ) (hk : k ≤ 2 * jumpLength m - 3) :
    (correction m).coeff k = (correction m).coeff (2 * jumpLength m - 3 - k) := by
  have h := congrArg (fun P : ℤ[X] => P.coeff k) (correction_reflect m)
  rw [coeff_reflect, revAt_le hk] at h
  exact h.symm

lemma correction_coeff_zero (m : ℕ) : (correction m).coeff 0 = 1 := by
  have hq := jumpLength_two_le m
  have h := congrArg (fun P : ℤ[X] => P.coeff 0) (correction_identity m)
  have hn : 0 ≠ jumpLength m - 1 := by omega
  norm_num [coeff_mul, coeff_C_mul, coeff_X_pow, hn, jump_coeff_zero] at h
  exact h

lemma correction_coeff_step (m k : ℕ) (hk : k + 1 < jumpLength m - 1) :
    (correction m).coeff (k + 1) + (correction m).coeff k = (jump m).coeff (k + 1) := by
  have h := congrArg (fun P : ℤ[X] => P.coeff (k + 1)) (correction_identity m)
  rw [add_mul, one_mul, coeff_add, coeff_X_mul, coeff_add] at h
  have hn : k + 1 ≠ jumpLength m - 1 := by omega
  simpa [coeff_C_mul, coeff_X_pow, hn] using h

lemma correction_low_bounds (m k : ℕ) (hk : k < jumpLength m - 1) :
    -((k : ℤ) + 1) ≤ (correction m).coeff k ∧ (correction m).coeff k ≤ (k : ℤ) + 1 := by
  induction k with
  | zero => rw [correction_coeff_zero]; norm_num
  | succ k ih =>
    have hb := ih (by omega)
    have hs := correction_coeff_step m k hk
    have hj := jump_coeff_bounded m (k + 1)
    push_cast
    omega

/-- Coarse global coefficient bound; enough for exponential domination. -/
theorem correction_coeff_bounds (m k : ℕ) :
    -(jumpLength m : ℤ) ≤ (correction m).coeff k ∧ (correction m).coeff k ≤ jumpLength m := by
  have hq := jumpLength_two_le m
  by_cases hs : k ≤ 2 * jumpLength m - 3
  · by_cases hk : k < jumpLength m - 1
    · have h := correction_low_bounds m k hk
      omega
    · rw [correction_symmetry m k hs]
      have hr : 2 * jumpLength m - 3 - k < jumpLength m - 1 := by omega
      have h := correction_low_bounds m _ hr
      omega
  · have hz : (correction m).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt ((correction_degree_le m).trans_lt (by omega))
    rw [hz]
    omega

/-- The correction can change any one first difference by at most twice its geometric length. -/
theorem correction_difference_bounds (m k : ℕ) :
    -(2 * jumpLength m : ℤ) ≤ (correction m).coeff k - (correction m).coeff (k - 1) ∧
      (correction m).coeff k - (correction m).coeff (k - 1) ≤ (2 * jumpLength m : ℤ) := by
  have h := correction_coeff_bounds m k
  have hp := correction_coeff_bounds m (k - 1)
  omega

#print axioms correction_degree_le
#print axioms correction_coeff_bounds
#print axioms correction_difference_bounds
end BinaryResearch
