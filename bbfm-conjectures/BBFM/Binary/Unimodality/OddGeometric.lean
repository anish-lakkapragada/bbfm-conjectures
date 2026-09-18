import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

open Finset Polynomial
namespace BinaryShape

/-- Reflection pairs the negative terms of an arithmetic-progression sum
with their positive partners. -/
theorem antisymmetric_progression_nonneg (delta : ℤ → ℤ) (C K : ℤ) (q : ℕ)
    (hanti : ∀ z, delta (2 * C - z) = -delta z)
    (hpos : ∀ z, z ≤ C → 0 ≤ delta z)
    (hK : K ≤ C + q - 1) :
    0 ≤ ∑ j ∈ range q, delta (K - 2 * j) := by
  by_cases hKC : K ≤ C
  · apply sum_nonneg
    intro j _
    apply hpos
    omega
  · let T : ℕ := (K - C).toNat
    have hT : (T : ℤ) = K - C := by dsimp [T]; omega
    have hTq : T + 1 ≤ q := by omega
    have hzero : (∑ j ∈ range (T + 1), delta (K - 2 * j)) = 0 := by
      have href := sum_range_reflect (fun j : ℕ => delta (K - 2 * j)) (T + 1)
      have hneg : (∑ j ∈ range (T + 1), delta (K - 2 * ((T + 1 - 1 - j : ℕ) : ℤ))) =
          -(∑ j ∈ range (T + 1), delta (K - 2 * j)) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro j hj
        have hjT : j ≤ T := by simpa using (mem_range.mp hj)
        have he : K - 2 * ((T + 1 - 1 - j : ℕ) : ℤ) =
            2 * C - (K - 2 * j) := by
          simp only [Nat.add_sub_cancel, Nat.cast_sub hjT]
          omega
        rw [he, hanti]
      linarith
    rw [← sum_range_add_sum_Ico (fun j : ℕ => delta (K - 2 * j)) hTq, hzero, zero_add]
    apply sum_nonneg
    intro j hj
    apply hpos
    have hjT := (mem_Ico.mp hj).1
    omega

/-- A symmetric sequence with an odd integer degree stays increasing on its
lower half when convolved with an even-step geometric interval. -/
theorem odd_geometric_lower_mono (a : ℤ → ℤ) (C : ℤ) (q : ℕ)
    (hsymm : ∀ z, a (2 * C - 1 - z) = a z)
    (hmono : ∀ z, z < C → a z ≤ a (z + 1))
    (k : ℤ) (hk : k < C + q - 1) :
    (∑ j ∈ range q, a (k - 2 * j)) ≤ ∑ j ∈ range q, a (k + 1 - 2 * j) := by
  let delta : ℤ → ℤ := fun z => a z - a (z - 1)
  have ha : ∀ z, delta (2 * C - z) = -delta z := by
    intro z
    dsimp [delta]
    have h1 := hsymm (z - 1)
    have h2 := hsymm z
    have he : 2 * C - 1 - (z - 1) = 2 * C - z := by omega
    rw [he] at h1
    have he2 : 2 * C - z - 1 = 2 * C - 1 - z := by omega
    rw [h1, he2, h2]
    ring
  have hp : ∀ z, z ≤ C → 0 ≤ delta z := by
    intro z hz
    dsimp [delta]
    have h := hmono (z - 1) (by omega)
    simpa using sub_nonneg.mpr h
  have h := antisymmetric_progression_nonneg delta C (k + 1) q ha hp (by omega)
  dsimp [delta] at h
  simp only [show ∀ j : ℕ, k + 1 - 2 * j - 1 = k - 2 * j by intro j; omega,
    sum_sub_distrib] at h
  exact sub_nonneg.mp h

end BinaryShape

#print axioms BinaryShape.odd_geometric_lower_mono
