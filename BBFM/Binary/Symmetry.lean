import BBFM.Binary.Recurrence
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators

open Polynomial Finset
namespace BinaryResearch

/-- Half the common degree of the source summands. -/
def center (n : ℕ) : ℕ := ∑ j ∈ range n, 2 ^ j * (n / 2 ^ (j + 1))

/-- Adapted from the pinned public C5 weighted multiplicity identity. -/
lemma binary_weight_sum (n : ℕ) (p : Part n) :
    ∑ j ∈ range (n + 1), p.val.parts.count (2 ^ j) * 2 ^ j = n := by
  have hs : p.val.parts.toFinset ⊆ (range (n + 1)).image (fun j => 2 ^ j) := by
    intro i hi
    have himem := Multiset.mem_toFinset.mp hi
    obtain ⟨j, rfl⟩ := p.property i himem
    refine mem_image.mpr ⟨j, mem_range.mpr ?_, rfl⟩
    have hpow := p.val.le_of_mem_parts himem
    have hlt := j.lt_two_pow_self
    omega
  have hinj : Set.InjOn (fun j : ℕ => 2 ^ j) (range (n + 1) : Set ℕ) :=
    fun _ _ _ _ h => Nat.pow_right_injective (le_refl 2) h
  have h := Finset.sum_multiset_count_of_subset p.val.parts _ hs
  rw [Finset.sum_image hinj] at h
  simp only [smul_eq_mul] at h
  simpa [p.val.parts_sum] using h.symm

lemma capacity_sum (n : ℕ) :
    ∑ j ∈ range (n + 1), (n / 2 ^ j) * 2 ^ j = n + 2 * center n := by
  rw [sum_range_succ']
  simp only [pow_zero, Nat.div_one, mul_one]
  unfold center
  rw [Finset.mul_sum]
  have he : (∑ j ∈ range n, (n / 2 ^ (j + 1)) * 2 ^ (j + 1)) =
      ∑ j ∈ range n, 2 * (2 ^ j * (n / 2 ^ (j + 1))) := by
    apply sum_congr rfl
    intro j hj
    rw [pow_succ']
    ring
  rw [he]
  omega

lemma hBPartition_natDegree (n : ℕ) (p : Part n) :
    (hBPartition n p.val).natDegree = 2 * center n := by
  unfold hBPartition
  rw [natDegree_prod_of_monic]
  · simp only [natDegree_pow]
    have hd (j : ℕ) : (1 + (X : ℤ[X]) ^ (2 ^ j)).natDegree = 2 ^ j := by
      rw [add_comm, ← C_1, natDegree_X_pow_add_C]
    simp_rw [hd]
    have he : (∑ j ∈ range (n + 1), (n / 2 ^ j - p.val.parts.count (2 ^ j)) * 2 ^ j) =
        (∑ j ∈ range (n + 1), (n / 2 ^ j) * 2 ^ j) -
        ∑ j ∈ range (n + 1), p.val.parts.count (2 ^ j) * 2 ^ j := by
      simp_rw [Nat.sub_mul]
      exact Finset.sum_tsub_distrib (range (n + 1)) (fun j hj => Nat.mul_le_mul_right _ (multiplicity_bound n p.val j))
    rw [he, capacity_sum, binary_weight_sum]
    omega
  · intro j hj
    apply Monic.pow
    simpa [add_comm] using (monic_X_pow_add_C (1 : ℤ) (by positivity : 2 ^ j ≠ 0))

lemma reverse_one_add_X_pow (s : ℕ) (_hs : 0 < s) :
    (1 + (X : ℤ[X]) ^ s).reverse = 1 + X ^ s := by
  have hd : (1 + (X : ℤ[X]) ^ s).natDegree = s := by
    rw [add_comm, ← C_1, natDegree_X_pow_add_C]
  rw [reverse, hd, reflect_add, reflect_one, reflect_monomial, revAt_le (le_refl s)]
  simp [add_comm]

lemma reverse_power_of_fixed (P : ℤ[X]) (hP : P.reverse = P) (r : ℕ) :
    (P ^ r).reverse = P ^ r := by
  induction r with
  | zero => simpa only [pow_zero, map_one] using (reverse_C (1 : ℤ))
  | succ r ih => rw [pow_succ, reverse_mul_of_domain, ih, hP]

lemma hBPartition_reverse (n : ℕ) (p : Nat.Partition n) :
    (hBPartition n p).reverse = hBPartition n p := by
  unfold hBPartition
  apply Finset.prod_induction _ (fun P : ℤ[X] => P.reverse = P)
  · intro P Q hP hQ
    rw [reverse_mul_of_domain, hP, hQ]
  · simpa only [map_one] using (reverse_C (1 : ℤ))
  · intro j hj
    exact reverse_power_of_fixed _ (reverse_one_add_X_pow _ (by positivity)) _

/-- Full source symmetry, with the explicit degree bound used by the shape invariant. -/
theorem numB_symmetry (n k : ℕ) (hk : k ≤ 2 * center n) :
    (numB n).coeff k = (numB n).coeff (2 * center n - k) := by
  rw [numerator_eq_sum, finsetSum_coeff, finsetSum_coeff]
  apply sum_congr rfl
  intro p hp
  have h := congrArg (fun P : ℤ[X] => P.coeff k) (hBPartition_reverse n p.val)
  rw [coeff_reverse, hBPartition_natDegree n p, revAt_le hk] at h
  exact h.symm

theorem numB_support (n k : ℕ) (hk : 2 * center n < k) : (numB n).coeff k = 0 := by
  rw [numerator_eq_sum, finsetSum_coeff]
  apply sum_eq_zero
  intro p hp
  exact coeff_eq_zero_of_natDegree_lt (by rw [hBPartition_natDegree n p]; exact hk)

lemma nonneg_coeff_mul (P Q : ℤ[X]) (hP : ∀ k, 0 ≤ P.coeff k) (hQ : ∀ k, 0 ≤ Q.coeff k)
    (k : ℕ) : 0 ≤ (P * Q).coeff k := by
  rw [coeff_mul]
  exact sum_nonneg fun x hx => mul_nonneg (hP x.1) (hQ x.2)

lemma nonneg_coeff_pow (P : ℤ[X]) (hP : ∀ k, 0 ≤ P.coeff k) (r k : ℕ) :
    0 ≤ (P ^ r).coeff k := by
  induction r generalizing k with
  | zero => simp only [pow_zero, coeff_one]; split_ifs <;> omega
  | succ r ih =>
    rw [pow_succ]
    exact nonneg_coeff_mul _ _ ih hP k

lemma hBPartition_nonneg (n : ℕ) (p : Nat.Partition n) :
    ∀ k, 0 ≤ (hBPartition n p).coeff k := by
  unfold hBPartition
  apply Finset.prod_induction _ (fun P : ℤ[X] => ∀ k, 0 ≤ P.coeff k)
  · exact fun P Q hP hQ k => nonneg_coeff_mul P Q hP hQ k
  · intro k; simp only [coeff_one]; split_ifs <;> omega
  · intro j hj k
    apply nonneg_coeff_pow
    intro k
    simp only [coeff_add, coeff_one, coeff_X_pow]
    split_ifs <;> omega

theorem numB_nonneg (n k : ℕ) : 0 ≤ (numB n).coeff k := by
  rw [numerator_eq_sum, finsetSum_coeff]
  exact sum_nonneg fun p hp => hBPartition_nonneg n p.val k

#print axioms numB_symmetry
#print axioms numB_support
#print axioms numB_nonneg
end BinaryResearch
