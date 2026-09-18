import BBFM.Binary.Residual

open Polynomial Finset
namespace BinaryResearch

/-- The canonical all-ones binary partition; reused construction from the previous private audit. -/
def allOnes (n : ℕ) : Part n :=
  ⟨{ parts := Multiset.replicate n 1
     parts_pos := by
       intro i hi
       have : i = 1 := (Multiset.mem_replicate.mp hi).2
       omega
     parts_sum := by simp }, by
    intro i hi
    have : i = 1 := (Multiset.mem_replicate.mp hi).2
    subst i
    exact ⟨0, by simp⟩⟩

lemma hBPartition_ne_zero (n : ℕ) (p : Nat.Partition n) : hBPartition n p ≠ 0 := by
  intro h
  have hc := hBPartition_coeff_zero n p
  rw [h] at hc
  norm_num at hc

lemma one_add_X_ne_zero : (1 + (X : ℤ[X])) ≠ 0 := by
  intro h
  have hc := congrArg (fun P : ℤ[X] => P.coeff 0) h
  norm_num at hc

lemma center_odd (m : ℕ) : center (2 * m + 1) = center (2 * m) := by
  have h := congrArg natDegree (summand_appendOne m (allOnes (2 * m)))
  rw [hBPartition_natDegree, hBPartition_natDegree] at h
  omega

lemma center_double (m : ℕ) : center (2 * m) = m + 2 * center m := by
  have h := congrArg natDegree (summand_doublePart (allOnes m))
  have hs : ((hBPartition m (allOnes m).val).comp (X ^ 2)) ≠ 0 := by
    intro hz
    have hc := congrArg (fun P : ℤ[X] => P.coeff 0) hz
    rw [comp_square_coeff] at hc
    norm_num [hBPartition_coeff_zero] at hc
  rw [hBPartition_natDegree, natDegree_mul (pow_ne_zero _ one_add_X_ne_zero) hs,
    natDegree_pow, natDegree_comp, hBPartition_natDegree, natDegree_X_pow] at h
  have h1 : (1 + (X : ℤ[X])).natDegree = 1 := by
    rw [add_comm, ← C_1, natDegree_X_add_C]
  rw [h1] at h
  omega

lemma sum_binary_degrees (t : ℕ) :
    (∑ j ∈ range t, 2 ^ (j + 1)) + 2 = 2 * 2 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ, pow_succ]
    omega

lemma jump_degree (m : ℕ) : (jump m).natDegree + 2 = 2 * jumpLength m := by
  rw [jump_carry_product, natDegree_prod_of_monic]
  · have hd (j : ℕ) : (1 + (X : ℤ[X]) ^ (2 ^ (j + 1))).natDegree = 2 ^ (j + 1) := by
      rw [add_comm, ← C_1, natDegree_X_pow_add_C]
    simp_rw [hd]
    exact sum_binary_degrees _
  · intro j hj
    simpa [add_comm] using (monic_X_pow_add_C (1 : ℤ) (by positivity : 2 ^ (j + 1) ≠ 0))

/-- Center alignment of the geometric and binomial summands, proved from actual summand degrees. -/
lemma center_step (m : ℕ) : center (2 * m + 2) + 1 = center (2 * m) + jumpLength m := by
  have h := congrArg natDegree (summand_appendTwo m (allOnes (2 * m)))
  have hj : jump m ≠ 0 := by
    intro hz
    have hc := jump_coeff_zero m
    rw [hz] at hc
    norm_num at hc
  rw [hBPartition_natDegree, natDegree_mul hj (hBPartition_ne_zero _ _), hBPartition_natDegree] at h
  have hd := jump_degree m
  omega

/-- Large-source central windows lie strictly inside the degree range. -/
lemma center_window (n : ℕ) (hn : 48 ≤ n) : n + 2 < center n := by
  have hsum : (∑ j ∈ range 3, 2 ^ j * (n / 2 ^ (j + 1))) ≤ center n := by
    unfold center
    exact sum_le_sum_of_subset (range_mono (by omega))
  norm_num [sum_range_succ] at hsum
  omega

#print axioms center_double
#print axioms center_step
#print axioms center_window
end BinaryResearch
