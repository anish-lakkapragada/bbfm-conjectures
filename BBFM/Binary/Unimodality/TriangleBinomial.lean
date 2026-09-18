import BBFM.Binary.Unimodality.PolynomialClosure
import Mathlib.Data.Nat.Choose.Sum

open Finset Polynomial
namespace BinaryShape

noncomputable def uniform (L : ℕ) : ℤ[X] := ∑ i ∈ range L, X ^ i

lemma coeff_mul_uniform_sum (P : ℤ[X]) (L k : ℕ) :
    (P * uniform L).coeff k =
      ∑ j ∈ range L, if j ≤ k then P.coeff (k - j) else 0 := by
  simp only [uniform, Finset.mul_sum, finsetSum_coeff, Polynomial.coeff_mul_X_pow']

lemma coeff_mul_uniform_low (P : ℤ[X]) (L k : ℕ) (hk : k < L) :
    (P * uniform L).coeff k = ∑ i ∈ range (k + 1), P.coeff i := by
  rw [coeff_mul_uniform_sum]
  calc
    (∑ j ∈ range L, if j ≤ k then P.coeff (k - j) else 0) =
        ∑ j ∈ range (k + 1), if j ≤ k then P.coeff (k - j) else 0 := by
      symm
      apply sum_subset (range_mono (by omega : k + 1 ≤ L))
      intro j hj hnot
      have hneg : ¬ j ≤ k := by simpa using hnot
      simp only [if_neg hneg]
    _ = ∑ j ∈ range (k + 1), P.coeff (k - j) := by
      apply sum_congr rfl
      intro j hj
      rw [if_pos (by simpa using mem_range.mp hj)]
    _ = ∑ i ∈ range (k + 1), P.coeff i := by
      simpa using sum_range_reflect (fun i => P.coeff i) (k + 1)

lemma coeff_mul_uniform_high (P : ℤ[X]) (L k : ℕ) (hk : L ≤ k) :
    (P * uniform L).coeff k = ∑ i ∈ Ico (k + 1 - L) (k + 1), P.coeff i := by
  rw [coeff_mul_uniform_sum]
  calc
    (∑ j ∈ range L, if j ≤ k then P.coeff (k - j) else 0) =
        ∑ j ∈ range L, P.coeff (k - j) := by
      apply sum_congr rfl
      intro j hj
      rw [if_pos (by have := mem_range.mp hj; omega)]
    _ = ∑ i ∈ Ico (k + 1 - L) (k + 1), P.coeff i := by
      simpa only [Nat.Ico_zero_eq_range, Nat.sub_zero] using
        (sum_Ico_reflect (fun i => P.coeff i) 0 (m := L) (n := k) (by omega))

lemma one_sub_X_mul_uniform (L : ℕ) :
    (1 - (X : ℤ[X])) * uniform L = 1 - X ^ L := by
  unfold uniform
  calc
    (1 - (X : ℤ[X])) * (∑ i ∈ range L, X ^ i) =
        -((∑ i ∈ range L, X ^ i) * (X - 1)) := by ring
    _ = -(X ^ L - 1) := by rw [geom_sum_mul]
    _ = 1 - X ^ L := by ring

lemma coefficient_difference (P : ℤ[X]) (k : ℕ) (hk : 1 ≤ k) :
    ((1 - X) * P).coeff k = P.coeff k - P.coeff (k - 1) := by
  rw [sub_mul, one_mul, coeff_sub]
  congr 1
  simpa only [pow_one, if_pos hk] using Polynomial.coeff_X_pow_mul' P 1 k

lemma triangle_difference (P : ℤ[X]) (L k : ℕ) (hk : 1 ≤ k) :
    (P * (uniform L) ^ 2).coeff k - (P * (uniform L) ^ 2).coeff (k - 1) =
      (P * uniform L).coeff k -
        if L ≤ k then (P * uniform L).coeff (k - L) else 0 := by
  rw [← coefficient_difference _ k hk]
  have he : (1 - (X : ℤ[X])) * (P * (uniform L) ^ 2) =
      (P * uniform L) - X ^ L * (P * uniform L) := by
    calc
      (1 - (X : ℤ[X])) * (P * (uniform L) ^ 2) =
          ((1 - X) * uniform L) * (P * uniform L) := by ring
      _ = (1 - X ^ L) * (P * uniform L) := by rw [one_sub_X_mul_uniform]
      _ = _ := by ring
  rw [he, coeff_sub, Polynomial.coeff_X_pow_mul']

def choosePrefix (r k : ℕ) : ℤ := ∑ i ∈ range (k + 1), (r.choose i : ℤ)

lemma choosePrefix_total (r k : ℕ) (hrk : r ≤ k) : choosePrefix r k = (2 : ℤ) ^ r := by
  have he : choosePrefix r r = choosePrefix r k := by
    apply sum_subset (range_mono (by omega : r + 1 ≤ k + 1))
    intro i hi hnot
    have hir : r < i := by simpa using hnot
    simp only [Nat.choose_eq_zero_of_lt hir, Nat.cast_zero]
  rw [← he]
  unfold choosePrefix
  exact_mod_cast Nat.sum_range_choose r

lemma binomial_uniform_high (r L k : ℕ) (hrL : r < L) (hLk : L ≤ k) :
    (((1 + X) ^ r : ℤ[X]) * uniform L).coeff k =
      (2 : ℤ) ^ r - choosePrefix r (k - L) := by
  rw [coeff_mul_uniform_high _ L k hLk]
  simp only [Polynomial.coeff_one_add_X_pow]
  have hsum := sum_range_add_sum_Ico (fun i => (r.choose i : ℤ))
    (show k + 1 - L ≤ k + 1 by omega)
  have he : k + 1 - L = k - L + 1 := by omega
  rw [he] at hsum ⊢
  change choosePrefix r (k - L) + _ = choosePrefix r k at hsum
  rw [choosePrefix_total r k (by omega)] at hsum
  omega

/-- The central binomial coefficient is a uniform lower bound for the
first differences of a binomial-smoothed triangle across its whole
specified central interval. This is an exact integer-polynomial theorem. -/
theorem triangle_binomial_difference (s L k : ℕ) (hs : 1 ≤ s)
    (hL : 2 * s + 2 ≤ L) (hks : s ≤ k) (hkL : k ≤ L + s - 1) :
    (((2 * s + 1).choose s : ℕ) : ℤ) ≤
      (((1 + X) ^ (2 * s + 1) : ℤ[X]) * (uniform L) ^ 2).coeff k -
      (((1 + X) ^ (2 * s + 1) : ℤ[X]) * (uniform L) ^ 2).coeff (k - 1) := by
  rw [triangle_difference _ L k (by omega)]
  by_cases hk : k < L
  · rw [if_neg (by omega : ¬ L ≤ k), sub_zero, coeff_mul_uniform_low _ L k hk]
    simp only [Polynomial.coeff_one_add_X_pow]
    exact single_le_sum (f := fun i => ((2 * s + 1).choose i : ℤ))
      (fun i _ => Int.natCast_nonneg _) (mem_range.mpr (by omega : s < k + 1))
  · have hLk : L ≤ k := by omega
    have ht : k - L < s := by omega
    rw [if_pos hLk, binomial_uniform_high _ L k (by omega) hLk,
      coeff_mul_uniform_low _ L (k - L) (by omega)]
    simp only [Polynomial.coeff_one_add_X_pow]
    change ((2 * s + 1).choose s : ℤ) ≤
      (2 : ℤ) ^ (2 * s + 1) - choosePrefix (2 * s + 1) (k - L) -
        choosePrefix (2 * s + 1) (k - L)
    have hhalf : choosePrefix (2 * s + 1) s = (4 : ℤ) ^ s := by
      unfold choosePrefix
      exact_mod_cast Nat.sum_range_choose_halfway s
    have hsum := sum_range_add_sum_Ico (fun i => ((2 * s + 1).choose i : ℤ))
      (show k - L + 1 ≤ s + 1 by omega)
    change choosePrefix (2 * s + 1) (k - L) + _ = choosePrefix (2 * s + 1) s at hsum
    have hcentral : ((2 * s + 1).choose s : ℤ) ≤
        ∑ i ∈ Ico (k - L + 1) (s + 1), ((2 * s + 1).choose i : ℤ) := by
      exact single_le_sum (f := fun i => ((2 * s + 1).choose i : ℤ))
        (fun i _ => Int.natCast_nonneg _)
        (show s ∈ Ico (k - L + 1) (s + 1) from mem_Ico.mpr ⟨by omega, by omega⟩)
    have hpow : (2 : ℤ) ^ (2 * s + 1) = 2 * 4 ^ s := by
      rw [pow_add, pow_mul]
      norm_num
      ring
    have hnonneg : 0 ≤ ((2 * s + 1).choose s : ℤ) := by positivity
    rw [hhalf] at hsum
    rw [hpow]
    omega

end BinaryShape

#print axioms BinaryShape.triangle_binomial_difference
