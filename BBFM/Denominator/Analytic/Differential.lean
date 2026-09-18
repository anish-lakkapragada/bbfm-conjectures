import BBFM.Denominator.Analytic.Basic

noncomputable section
namespace DenominatorResearch
open Polynomial Finset

lemma nonneg_C (r : ℝ) (hr : 0 ≤ r) : Nonneg (C r) := by
  intro k
  rw [coeff_C]
  split_ifs <;> positivity

lemma factor_derivative_upper (i r : ℕ) :
    CoeffLE (((1 + (X : ℝ[X]) ^ (i + 1)) ^ r).derivative)
      ((1 + X ^ (i + 1)) ^ r * (C ((r : ℝ) * (i + 1)) * X ^ i)) := by
  cases r with
  | zero => simp [CoeffLE]
  | succ r =>
    have hbase : CoeffLE ((1 + (X : ℝ[X]) ^ (i + 1)) ^ r)
        ((1 + X ^ (i + 1)) ^ (r + 1)) := by
      rw [pow_succ (1 + (X : ℝ[X]) ^ (i + 1)) r, mul_add, mul_one]
      exact coeffLE_add_nonneg _
        (nonneg_mul (nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow _)) _) (nonneg_X_pow _))
    have h := coeffLE_mul_right hbase
      (nonneg_mul (nonneg_C (((r + 1 : ℕ) : ℝ) * (i + 1)) (by positivity)) (nonneg_X_pow i))
    convert h using 1
    rw [derivative_pow_succ, derivative_add, derivative_one, zero_add, derivative_X_pow]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, map_mul]
    ring

lemma product_derivative_upper {α : Type*} (s : Finset α) (P B : α → ℝ[X])
    (hP : ∀ i ∈ s, Nonneg (P i))
    (hD : ∀ i ∈ s, CoeffLE (P i).derivative (P i * B i)) :
    CoeffLE (∏ i ∈ s, P i).derivative ((∏ i ∈ s, P i) * ∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [CoeffLE]
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi, derivative_mul]
    have hp := hP i (by simp)
    have hrest := nonneg_prod s P (fun j hj => hP j (by simp [hj]))
    have hd := hD i (by simp)
    have hr := ih (fun j hj => hP j (by simp [hj])) (fun j hj => hD j (by simp [hj]))
    have h := coeffLE_add (coeffLE_mul_right hd hrest) (coeffLE_mul_left hr hp)
    convert h using 1 <;> ring

/-- The polynomial majorizing the logarithmic derivative coefficientwise. -/
def derivativeMajorant (m : ℕ → ℕ) (n : ℕ) : ℝ[X] :=
  ∑ i ∈ range n, C ((m (i + 1) : ℝ) * (i + 1)) * X ^ i

lemma weightedProduct_derivative_upper (m : ℕ → ℕ) (n : ℕ) :
    CoeffLE (weightedProduct m n).derivative
      (weightedProduct m n * derivativeMajorant m n) := by
  exact product_derivative_upper _ _ _
    (fun i _ => nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow _)) _)
    (fun i _ => factor_derivative_upper i (m (i + 1)))

lemma derivativeMajorant_coeff (m : ℕ → ℕ) (n j : ℕ) :
    (derivativeMajorant m n).coeff j =
      if j < n then (m (j + 1) : ℝ) * (j + 1) else 0 := by
  simp only [derivativeMajorant, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hj : j < n
  · rw [if_pos hj]
    rw [sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [Ne.symm hbj]
    · simp [hj]
  · rw [if_neg hj]
    apply sum_eq_zero
    intro b hb
    have hbj : j ≠ b := by have := mem_range.mp hb; omega
    simp [hbj]

lemma derivativeMajorant_coeff_le (m : ℕ → ℕ) (n t : ℕ)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) (j : ℕ) :
    (derivativeMajorant m n).coeff j ≤ (t : ℝ) * (j + 1) := by
  rw [derivativeMajorant_coeff]
  split_ifs with hj
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm (j + 1) (by omega) (by omega))
      (by positivity)
  · positivity

lemma weightedProduct_coeff_upper (m : ℕ → ℕ) (n t k : ℕ)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    ((k : ℝ) + 1) * (weightedProduct m n).coeff (k + 1) ≤
      (t : ℝ) * ∑ r ∈ range (k + 1), ((k : ℝ) + 1 - r) * (weightedProduct m n).coeff r := by
  have h := weightedProduct_derivative_upper m n k
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hpos := weightedProduct_nonneg m n
  have hsum : (∑ r ∈ range (k + 1),
      (weightedProduct m n).coeff r * (derivativeMajorant m n).coeff (k - r)) ≤
      (t : ℝ) * ∑ r ∈ range (k + 1), ((k : ℝ) + 1 - r) * (weightedProduct m n).coeff r := by
    rw [mul_sum]
    apply sum_le_sum
    intro r hr
    have hrk : r ≤ k := by have := mem_range.mp hr; omega
    have hB := derivativeMajorant_coeff_le m n t hm (k - r)
    have hh := mul_le_mul_of_nonneg_left hB (hpos r)
    rw [Nat.cast_sub hrk] at hh
    nlinarith [hh]
  have := h.trans hsum
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using this

lemma weightedProduct_coeff_lower (m : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    ((m 1 : ℝ) - j) * (weightedProduct m n).coeff j ≤
      ((j : ℝ) + 1) * (weightedProduct m n).coeff (j + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let Q : ℝ[X] := ∏ i ∈ range n, (1 + X ^ (i + 1 + 1)) ^ m (i + 1 + 1)
  have hQ : Nonneg Q := nonneg_prod _ _
    (fun i _ => nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow _)) _)
  have hfac : weightedProduct m (n + 1) = (1 + X) ^ m 1 * Q := by
    simp only [weightedProduct, prod_range_succ', zero_add, pow_one]
    exact mul_comm _ _
  rw [hfac]
  have h := unit_differential_lower (m 1) hQ j
  rw [coeff_C_mul, add_mul, one_mul, coeff_add] at h
  cases j with
  | zero =>
    simpa only [coeff_X_mul_zero, coeff_derivative, Nat.cast_zero, Nat.cast_one,
      zero_add, add_zero, sub_zero, mul_one, one_mul] using h
  | succ j =>
    rw [coeff_X_mul, coeff_derivative, coeff_derivative] at h
    push_cast at h ⊢
    nlinarith

end DenominatorResearch
