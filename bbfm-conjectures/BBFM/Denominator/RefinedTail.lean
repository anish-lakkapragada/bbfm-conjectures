import BBFM.Denominator.RefinedDifferential
import BBFM.Denominator.Analytic.Sequence

noncomputable section
namespace BBFMRefined
open Polynomial Finset DenominatorResearch

def tailProduct (m : ℕ → ℕ) (n : ℕ) : ℝ[X] :=
  ∏ i ∈ range n, (1+X^(i+3))^m (i+3)

def tailMajorant (m : ℕ → ℕ) (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range n, C ((m (i+3) : ℝ)*(i+3))*X^(i+2)

lemma tailProduct_nonneg (m : ℕ → ℕ) (n : ℕ) : Nonneg (tailProduct m n) :=
  nonneg_prod _ _ (fun i _ => nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow _)) _)

lemma tailProduct_derivative_upper (m : ℕ → ℕ) (n : ℕ) :
    CoeffLE (tailProduct m n).derivative (tailProduct m n*tailMajorant m n) := by
  apply product_derivative_upper
  · intro i hi
    exact nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow _)) _
  · intro i hi
    have hh := factor_derivative_upper (i+2) (m (i+3))
    norm_num [Nat.add_assoc, add_assoc] at hh ⊢
    exact hh

lemma weightedProduct_split_two (m : ℕ → ℕ) (n : ℕ) :
    weightedProduct m (n+2) = (1+X)^m 1*(1+X^2)^m 2*tailProduct m n := by
  simp only [weightedProduct, tailProduct, prod_range_succ', Nat.add_assoc,
    Nat.reduceAdd, Nat.zero_add, pow_one, Nat.add_comm]
  ring

lemma tailMajorant_coeff (m : ℕ → ℕ) (n j : ℕ) :
    (tailMajorant m n).coeff j =
      if 2 ≤ j ∧ j < n+2 then (m (j+1) : ℝ)*(j+1) else 0 := by
  simp only [tailMajorant, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hj : 2 ≤ j ∧ j < n+2
  · rw [if_pos hj]
    rw [sum_eq_single (j-2)]
    · have he : j-2+2=j := by omega
      have he' : j-2+3=j+1 := by omega
      simp only [he,he',if_true]
      rw [Nat.cast_sub hj.1]
      push_cast
      ring
    · intro b hb hbj
      have he : j ≠ b+2 := by omega
      simp [he]
    · simp only [mem_range]
      intro hh
      omega
  · rw [if_neg hj]
    apply sum_eq_zero
    intro b hb
    have he : j ≠ b+2 := by have := mem_range.mp hb; omega
    simp [he]

lemma tailMajorant_coeff_le (m : ℕ → ℕ) (n r j : ℕ)
    (hm : ∀ i, 3 ≤ i → i ≤ n+2 → m i ≤ r) :
    (tailMajorant m n).coeff j ≤
      if 2 ≤ j then (r : ℝ)*(j+1) else 0 := by
  rw [tailMajorant_coeff]
  split_ifs with h h'
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm (j+1) (by omega) (by omega))
      (by positivity)
  · omega
  · positivity
  · rfl

lemma tailMajorant_nonneg (m : ℕ → ℕ) (n : ℕ) : Nonneg (tailMajorant m n) := by
  intro j
  rw [tailMajorant_coeff]
  split_ifs <;> positivity

def tailErrorMajorant (m : ℕ → ℕ) (n : ℕ) : ℝ[X] :=
  C (2*(m 2 : ℝ))*X^2+(1+X)*tailMajorant m n

lemma tailErrorMajorant_zero_one (m : ℕ → ℕ) (n : ℕ) :
    (tailErrorMajorant m n).coeff 0=0 ∧
    (tailErrorMajorant m n).coeff 1=0 := by
  constructor <;> simp only [tailErrorMajorant,add_mul,one_mul,coeff_add,
    coeff_C_mul_X_pow,tailMajorant_coeff,coeff_X_mul_zero,coeff_X_mul] <;> norm_num

lemma tailErrorMajorant_coeff_le (m : ℕ → ℕ) (n r j : ℕ)
    (hm : ∀ i, 2 ≤ i → i ≤ n+2 → m i ≤ r) :
    (tailErrorMajorant m n).coeff j ≤ (r : ℝ)*(2*j+3) := by
  have hs : (m 2 : ℝ) ≤ r := by exact_mod_cast hm 2 le_rfl (by omega)
  have ht : ∀ q, (tailMajorant m n).coeff q ≤ (r : ℝ)*(q+1) := by
    intro q
    have hh := tailMajorant_coeff_le m n r q (fun i hi hin => hm i (by omega) hin)
    split_ifs at hh with hq
    · exact hh
    · exact hh.trans (by positivity)
  cases j with
  | zero => rw [(tailErrorMajorant_zero_one m n).1]; positivity
  | succ j =>
    have h1 := ht (j+1)
    have h2 := ht j
    have h3 : (C (2*(m 2 : ℝ))*X^2 : ℝ[X]).coeff (j+1) ≤ 2*r := by
      rw [coeff_C_mul_X_pow]
      split_ifs <;> linarith
    simp only [tailErrorMajorant,add_mul,one_mul,coeff_add,coeff_X_mul]
    push_cast at h1 ⊢
    nlinarith

lemma convolution_tail_bound (P H : ℝ[X]) (r : ℝ) (m : ℕ)
    (hP : Nonneg P) (hr : 0 ≤ r) (hzero : H.coeff 0=0) (hone : H.coeff 1=0)
    (hH : ∀ j, H.coeff j ≤ r*(2*j+3))
    (hg : ∀ j < m, 3*P.coeff j ≤ P.coeff (j+1)) :
    (P*H).coeff (m+2) ≤ 14*r*P.coeff m := by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [sum_range_succ,sum_range_succ]
  rw [show m+2-(m+1)=1 by omega]
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left, Nat.sub_self,hzero,hone,
    mul_zero,add_zero]
  obtain ⟨hs,hw⟩ := growing_sums (fun j => P.coeff j) hP m hg
  have hh : (∑ j ∈ range (m+1), P.coeff j*H.coeff (m+2-j)) ≤
      r*(2*(∑ j ∈ range (m+1), ((m : ℝ)+2-j)*P.coeff j)+
        3*(∑ j ∈ range (m+1), P.coeff j)) := by
    rw [mul_add]
    simp_rw [mul_sum]
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    have hjm : j ≤ m := by have := mem_range.mp hj; omega
    have hc := mul_le_mul_of_nonneg_left (hH (m+2-j)) (hP j)
    rw [Nat.cast_sub (by omega : j ≤ m+2)] at hc
    push_cast at hc
    nlinarith
  have hs' := mul_le_mul_of_nonneg_left hs hr
  have hw' := mul_le_mul_of_nonneg_left hw hr
  nlinarith

#print axioms tailProduct_derivative_upper
#print axioms weightedProduct_split_two
#print axioms tailMajorant_coeff_le
#print axioms convolution_tail_bound
end BBFMRefined
