import BBFM.Binary.Unimodality.TriangleSubtraction
import Mathlib.Algebra.Polynomial.Expand

open Finset Polynomial
namespace BinaryShape

/-- Coefficient shape relative to an explicit degree, allowing zero padding. -/
structure HasShape (P : ℤ[X]) (d : ℕ) : Prop where
  support : ∀ k, d < k → P.coeff k = 0
  symm : ∀ k, k ≤ d → P.coeff k = P.coeff (d - k)
  nonneg : ∀ k, 0 ≤ P.coeff k
  mono : ∀ k, 2 * k < d → P.coeff k ≤ P.coeff (k + 1)

lemma intCoeff_nonneg (P : ℤ[X]) (h : ∀ k, 0 ≤ P.coeff k) (z : ℤ) :
    0 ≤ intCoeff P z := by
  unfold intCoeff
  split_ifs
  · exact h _
  · exact le_rfl

lemma intCoeff_mono (P : ℤ[X]) (d : ℕ) (h : HasShape P d) (z : ℤ)
    (hz : 2 * z < d) : intCoeff P z ≤ intCoeff P (z + 1) := by
  by_cases hz0 : 0 ≤ z
  · have hz1 : 0 ≤ z + 1 := by omega
    have he : (z + 1).toNat = z.toNat + 1 := by omega
    simpa only [intCoeff, if_pos hz0, if_pos hz1, he] using h.mono z.toNat (by omega)
  · simp only [intCoeff, if_neg hz0]
    exact intCoeff_nonneg P h.nonneg (z + 1)

lemma intCoeff_one_add_X_mul (P : ℤ[X]) (z : ℤ) :
    intCoeff ((1 + X) * P) z = intCoeff P z + intCoeff P (z - 1) := by
  by_cases hz0 : 0 ≤ z
  · simp only [intCoeff, if_pos hz0, add_mul, one_mul, coeff_add]
    have hx := Polynomial.coeff_X_pow_mul' P 1 z.toNat
    rw [pow_one] at hx
    rw [hx]
    by_cases hz1 : 1 ≤ z
    · have hn : 1 ≤ z.toNat := by omega
      have hm : 0 ≤ z - 1 := by omega
      have he : (z - 1).toNat = z.toNat - 1 := by omega
      simp only [if_pos hn, if_pos hm, he]
    · have hn : ¬ 1 ≤ z.toNat := by omega
      have hm : ¬ 0 ≤ z - 1 := by omega
      simp only [if_neg hn, if_neg hm]
  · have hm : ¬ 0 ≤ z - 1 := by omega
    simp only [intCoeff, if_neg hz0, if_neg hm, add_zero]

theorem one_add_X_mul_shape (P : ℤ[X]) (d : ℕ) (h : HasShape P d) :
    HasShape ((1 + X) * P) (d + 1) := by
  have hr := intCoeff_reflection P d h.support h.symm
  have hc (k : ℕ) : ((1 + X) * P).coeff k = intCoeff P k + intCoeff P (k - 1) := by
    rw [← intCoeff_nat, intCoeff_one_add_X_mul]
  constructor
  · intro k hk
    rw [hc, intCoeff_nat, h.support k (by omega)]
    have hz : 0 ≤ (k : ℤ) - 1 := by omega
    rw [intCoeff, if_pos hz, h.support _ (by omega)]
    ring
  · intro k hk
    rw [hc, hc]
    have ha : ((d + 1 - k : ℕ) : ℤ) = (d : ℤ) - ((k : ℤ) - 1) := by omega
    have hb : ((d + 1 - k : ℕ) : ℤ) - 1 = (d : ℤ) - k := by omega
    rw [hb, ha, hr, hr]
    ring
  · intro k
    rw [hc]
    exact add_nonneg (intCoeff_nonneg P h.nonneg _) (intCoeff_nonneg P h.nonneg _)
  · intro k hk
    rw [hc, hc]
    have he : ((k + 1 : ℕ) : ℤ) - 1 = k := by omega
    rw [he]
    by_cases hkd : 2 * k < d
    · have h1 := intCoeff_mono P d h (k - 1) (by omega)
      have h2 := intCoeff_mono P d h k (by exact_mod_cast hkd)
      have hz1 : (k : ℤ) - 1 + 1 = k := by ring
      have hz2 : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
      rw [hz1] at h1
      rw [hz2] at h2
      omega
    · have heq : (d : ℤ) - ((k : ℤ) - 1) = ((k + 1 : ℕ) : ℤ) := by omega
      have hh := hr ((k : ℤ) - 1)
      rw [heq] at hh
      omega

theorem binomial_mul_shape (P : ℤ[X]) (d r : ℕ) (h : HasShape P d) :
    HasShape (((1 + X) ^ r) * P) (d + r) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
    have hh := one_add_X_mul_shape _ (d + r) ih
    simpa only [pow_succ', mul_assoc, Nat.add_assoc] using hh

lemma duplicated_coeff (P : ℤ[X]) (k : ℕ) :
    ((1 + X) * P.comp (X ^ 2)).coeff k = P.coeff (k / 2) := by
  have hc : ∀ j, (P.comp (X ^ 2)).coeff j = if 2 ∣ j then P.coeff (j / 2) else 0 := by
    intro j
    exact Polynomial.coeff_expand (by decide : 0 < 2) P j
  rw [add_mul, one_mul, coeff_add]
  cases k with
  | zero => simp [hc]
  | succ k =>
    rw [Polynomial.coeff_X_mul, hc, hc]
    by_cases he : 2 ∣ k
    · have ho : ¬ 2 ∣ k + 1 := by omega
      rw [if_pos he, if_neg ho, zero_add]
      congr 1
      omega
    · have ho : 2 ∣ k + 1 := by omega
      rw [if_neg he, if_pos ho, add_zero]

theorem duplicated_shape (P : ℤ[X]) (d : ℕ) (h : HasShape P d) :
    HasShape ((1 + X) * P.comp (X ^ 2)) (2 * d + 1) := by
  constructor
  · intro k hk
    rw [duplicated_coeff, h.support _ (by omega)]
  · intro k hk
    rw [duplicated_coeff, duplicated_coeff, h.symm (k / 2) (by omega)]
    congr 1
    omega
  · intro k
    rw [duplicated_coeff]
    exact h.nonneg _
  · intro k hk
    rw [duplicated_coeff, duplicated_coeff]
    by_cases he : k / 2 = (k + 1) / 2
    · rw [he]
    · have hs : (k + 1) / 2 = k / 2 + 1 := by omega
      rw [hs]
      exact h.mono _ (by omega)

/-- Every positive binomial smoothing removes the gaps introduced by X ↦ X²
and preserves symmetric nonnegative unimodality. -/
theorem binomial_comp_square_shape (P : ℤ[X]) (d r : ℕ) (hr : 1 ≤ r)
    (h : HasShape P d) :
    HasShape (((1 + X) ^ r) * P.comp (X ^ 2)) (2 * d + r) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hh := binomial_mul_shape _ _ s (duplicated_shape P d h)
  convert hh using 1 <;> ring

end BinaryShape

#print axioms BinaryShape.binomial_comp_square_shape
