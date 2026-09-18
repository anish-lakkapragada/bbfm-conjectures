import Mathlib

noncomputable section
namespace DenominatorResearch
open Polynomial Finset

/-- Coefficientwise nonnegativity. -/
def Nonneg (P : ℝ[X]) : Prop := ∀ k, 0 ≤ P.coeff k

/-- Coefficientwise comparison; this is not evaluation comparison. -/
def CoeffLE (P Q : ℝ[X]) : Prop := ∀ k, P.coeff k ≤ Q.coeff k

lemma nonneg_one : Nonneg (1 : ℝ[X]) := by intro k; simp [coeff_one]; positivity
lemma nonneg_X_pow (i : ℕ) : Nonneg ((X : ℝ[X]) ^ i) := by
  intro k; simp [coeff_X_pow]; positivity
lemma nonneg_add {P Q : ℝ[X]} (hP : Nonneg P) (hQ : Nonneg Q) : Nonneg (P + Q) := by
  intro k; simpa only [coeff_add] using add_nonneg (hP k) (hQ k)
lemma nonneg_mul {P Q : ℝ[X]} (hP : Nonneg P) (hQ : Nonneg Q) : Nonneg (P * Q) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hP ij.1) (hQ ij.2)
lemma nonneg_pow {P : ℝ[X]} (hP : Nonneg P) (r : ℕ) : Nonneg (P ^ r) := by
  induction r with
  | zero => simpa using nonneg_one
  | succ r ih => simpa [pow_succ] using nonneg_mul ih hP
lemma nonneg_prod {α : Type*} (s : Finset α) (P : α → ℝ[X])
    (hP : ∀ i ∈ s, Nonneg (P i)) : Nonneg (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using nonneg_one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact nonneg_mul (hP i (by simp)) (ih (fun j hj => hP j (by simp [hj])))
lemma nonneg_derivative {P : ℝ[X]} (hP : Nonneg P) : Nonneg P.derivative := by
  intro k
  rw [coeff_derivative]
  exact mul_nonneg (hP (k + 1)) (by positivity)

lemma coeffLE_refl (P : ℝ[X]) : CoeffLE P P := fun _ => le_rfl
lemma coeffLE_trans {P Q R : ℝ[X]} (hPQ : CoeffLE P Q) (hQR : CoeffLE Q R) :
    CoeffLE P R := fun k => (hPQ k).trans (hQR k)
lemma coeffLE_add {P Q R S : ℝ[X]} (hPQ : CoeffLE P Q) (hRS : CoeffLE R S) :
    CoeffLE (P + R) (Q + S) := by
  intro k; simpa only [coeff_add] using add_le_add (hPQ k) (hRS k)
lemma coeffLE_mul_right {P Q R : ℝ[X]} (hPQ : CoeffLE P Q) (hR : Nonneg R) :
    CoeffLE (P * R) (Q * R) := by
  intro k
  simp only [coeff_mul]
  exact Finset.sum_le_sum fun ij _ => mul_le_mul_of_nonneg_right (hPQ ij.1) (hR ij.2)
lemma coeffLE_mul_left {P Q R : ℝ[X]} (hPQ : CoeffLE P Q) (hR : Nonneg R) :
    CoeffLE (R * P) (R * Q) := by
  simpa only [mul_comm R] using coeffLE_mul_right hPQ hR
lemma coeffLE_add_nonneg (P : ℝ[X]) {Q : ℝ[X]} (hQ : Nonneg Q) :
    CoeffLE P (P + Q) := by
  intro k
  simpa only [coeff_add] using le_add_of_nonneg_right (hQ k)

/-- A product of bounded multiplicities of weighted Bernoulli factors. -/
def weightedProduct (m : ℕ → ℕ) (n : ℕ) : ℝ[X] :=
  ∏ i ∈ Finset.range n, (1 + X ^ (i + 1)) ^ m (i + 1)

/-- BBFM Proposition 3.8's concrete ordinary partition denominator. -/
def den (n : ℕ) : ℝ[X] := weightedProduct (fun i => Nat.log 2 (n / i) + 1) n

lemma weightedProduct_nonneg (m : ℕ → ℕ) (n : ℕ) : Nonneg (weightedProduct m n) := by
  exact nonneg_prod _ _ fun i _ => nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow _)) _
lemma den_nonneg (n : ℕ) : Nonneg (den n) := weightedProduct_nonneg _ _

lemma coeffLE_one_factor (s r : ℕ) : CoeffLE 1 ((1 + (X : ℝ[X]) ^ s) ^ r) := by
  induction r with
  | zero => exact coeffLE_refl _
  | succ r ih =>
    rw [pow_succ]
    have h := coeffLE_mul_right ih (nonneg_add nonneg_one (nonneg_X_pow s))
    simp only [one_mul] at h
    exact coeffLE_trans (coeffLE_add_nonneg 1 (nonneg_X_pow s)) h

lemma unit_derivative_identity (t : ℕ) :
    (1 + (X : ℝ[X])) * ((1 + X) ^ t).derivative = C (t : ℝ) * (1 + X) ^ t := by
  cases t with
  | zero => simp
  | succ t =>
    rw [derivative_pow_succ]
    simp only [derivative_add, derivative_one, derivative_X, zero_add, mul_one, Nat.cast_succ]
    rw [pow_succ]
    ring

lemma unit_differential_lower (t : ℕ) {Q : ℝ[X]} (hQ : Nonneg Q) :
    CoeffLE (C (t : ℝ) * ((1 + X) ^ t * Q))
      ((1 + X) * ((1 + X) ^ t * Q).derivative) := by
  have hpos : Nonneg ((1 + X) ^ (t + 1) * Q.derivative) :=
    nonneg_mul (nonneg_pow (nonneg_add nonneg_one (by simpa using nonneg_X_pow 1)) _)
      (nonneg_derivative hQ)
  have hid : (1 + (X : ℝ[X])) * ((1 + X) ^ t * Q).derivative =
      C (t : ℝ) * ((1 + X) ^ t * Q) + (1 + X) ^ (t + 1) * Q.derivative := by
    rw [derivative_mul, mul_add]
    rw [← mul_assoc, unit_derivative_identity]
    ring
  rw [hid]
  exact coeffLE_add_nonneg _ hpos

end DenominatorResearch
