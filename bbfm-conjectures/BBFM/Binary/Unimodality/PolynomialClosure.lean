import BBFM.Binary.Unimodality.OddGeometric

open Finset Polynomial
namespace BinaryShape

def intCoeff (P : ℤ[X]) (z : ℤ) : ℤ := if 0 ≤ z then P.coeff z.toNat else 0

@[simp] lemma intCoeff_nat (P : ℤ[X]) (k : ℕ) : intCoeff P k = P.coeff k := by
  simp [intCoeff]

lemma intCoeff_reflection (P : ℤ[X]) (d : ℕ)
    (hsupport : ∀ k, d < k → P.coeff k = 0)
    (hsymm : ∀ k, k ≤ d → P.coeff k = P.coeff (d - k)) :
    ∀ z : ℤ, intCoeff P (d - z) = intCoeff P z := by
  intro z
  by_cases hz : 0 ≤ z
  · by_cases hzd : z ≤ d
    · have hz' : 0 ≤ (d : ℤ) - z := by omega
      have hnat : z.toNat ≤ d := by omega
      have he : ((d : ℤ) - z).toNat = d - z.toNat := by omega
      simpa only [intCoeff, if_pos hz, if_pos hz', he] using (hsymm z.toNat hnat).symm
    · have hz' : ¬ 0 ≤ (d : ℤ) - z := by omega
      simp only [intCoeff, if_pos hz, if_neg hz', hsupport z.toNat (by omega)]
  · have hz' : 0 ≤ (d : ℤ) - z := by omega
    simp only [intCoeff, if_neg hz, if_pos hz', hsupport ((d : ℤ) - z).toNat (by omega)]

lemma intCoeff_lower_mono (P : ℤ[X]) (c : ℕ)
    (hnonneg : ∀ k, 0 ≤ P.coeff k)
    (hmono : ∀ k, 2 * k < 2 * c + 1 → P.coeff k ≤ P.coeff (k + 1)) :
    ∀ z : ℤ, z < (c : ℤ) + 1 → intCoeff P z ≤ intCoeff P (z + 1) := by
  intro z hz
  by_cases hz0 : 0 ≤ z
  · have hz1 : 0 ≤ z + 1 := by omega
    have he : (z + 1).toNat = z.toNat + 1 := by omega
    simpa [intCoeff, hz0, hz1, he] using hmono z.toNat (by omega)
  · by_cases hz1 : 0 ≤ z + 1
    · simp only [intCoeff, if_neg hz0, if_pos hz1]
      exact hnonneg _
    · simp [intCoeff, hz0, hz1]

noncomputable def evenGeometric (q : ℕ) : ℤ[X] := ∑ j ∈ range q, X ^ (2 * j)

lemma intCoeff_mul_evenGeometric (P : ℤ[X]) (q : ℕ) (z : ℤ) :
    intCoeff (P * evenGeometric q) z =
      ∑ j ∈ range q, intCoeff P (z - 2 * j) := by
  by_cases hz : 0 ≤ z
  · simp only [intCoeff, if_pos hz, evenGeometric, Finset.mul_sum, finsetSum_coeff]
    apply sum_congr rfl
    intro j hj
    rw [Polynomial.coeff_mul_X_pow']
    by_cases hjz : 2 * j ≤ z.toNat
    · have hzj : 0 ≤ z - 2 * j := by omega
      have he : (z - 2 * j).toNat = z.toNat - 2 * j := by omega
      simp only [if_pos hjz, if_pos hzj, he]
    · have hzj : ¬ 0 ≤ z - 2 * j := by omega
      simp only [if_neg hjz, if_neg hzj]
  · simp only [intCoeff, if_neg hz]
    symm
    apply sum_eq_zero
    intro j _
    have hzj : ¬ 0 ≤ z - 2 * j := by omega
    simp only [if_neg hzj]

/-- An odd-degree symmetric, nonnegative, unimodal polynomial remains
increasing on its entire lower half after multiplication by G_q(X²).
The explicit degree/support inputs match the binary residual invariant. -/
theorem polynomial_odd_geometric_lower_mono (P : ℤ[X]) (c q : ℕ)
    (hsupport : ∀ k, 2 * c + 1 < k → P.coeff k = 0)
    (hsymm : ∀ k, k ≤ 2 * c + 1 → P.coeff k = P.coeff (2 * c + 1 - k))
    (hnonneg : ∀ k, 0 ≤ P.coeff k)
    (hmono : ∀ k, 2 * k < 2 * c + 1 → P.coeff k ≤ P.coeff (k + 1))
    (k : ℕ) (hk : k < c + q) :
    (P * evenGeometric q).coeff k ≤ (P * evenGeometric q).coeff (k + 1) := by
  have hs : ∀ z : ℤ, intCoeff P (2 * ((c : ℤ) + 1) - 1 - z) = intCoeff P z := by
    intro z
    have he : 2 * ((c : ℤ) + 1) - 1 - z = ((2 * c + 1 : ℕ) : ℤ) - z := by omega
    rw [he]
    exact intCoeff_reflection P (2 * c + 1) hsupport hsymm z
  have h := odd_geometric_lower_mono (intCoeff P) ((c : ℤ) + 1) q hs
    (intCoeff_lower_mono P c hnonneg hmono) k (by omega)
  rw [← intCoeff_mul_evenGeometric, ← intCoeff_mul_evenGeometric] at h
  have he : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by simp
  rw [he, intCoeff_nat, intCoeff_nat] at h
  exact h

end BinaryShape

#print axioms BinaryShape.polynomial_odd_geometric_lower_mono
