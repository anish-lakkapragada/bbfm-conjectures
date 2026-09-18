import BBFM.Binary.PowerComparison
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Expand

namespace BinaryResearch

def negativeBinomial (p k : ℕ) : ℤ := (p + k).choose p

theorem negativeBinomial_positive (p k : ℕ) : 0 < negativeBinomial p k := by
  unfold negativeBinomial
  exact_mod_cast Nat.choose_pos (by omega : p ≤ p + k)

/-- Negative-binomial coefficient profiles saturate the quantitative inequality. -/
theorem negativeBinomial_power_equality (p k : ℕ) :
    powerDefect p (negativeBinomial p k) (negativeBinomial p (k + 1))
      (negativeBinomial p (k + 2)) = 0 := by
  have h1 := Nat.choose_mul_succ_eq (p + k) p
  have h2 := Nat.choose_mul_succ_eq (p + k + 1) p
  have he1 : p + k + 1 - p = k + 1 := by omega
  have he2 : p + k + 1 + 1 - p = k + 2 := by omega
  rw [he1] at h1
  rw [he2] at h2
  have h1Z : negativeBinomial p k * (p + k + 1 : ℤ) =
      negativeBinomial p (k + 1) * (k + 1 : ℤ) := by
    unfold negativeBinomial
    exact_mod_cast h1
  have h2Z : negativeBinomial p (k + 1) * (p + k + 2 : ℤ) =
      negativeBinomial p (k + 2) * (k + 2 : ℤ) := by
    unfold negativeBinomial
    convert (show ((p + k + 1).choose p : ℤ) * (p + k + 1 + 1 : ℤ) =
      ((p + k + 1 + 1).choose p : ℤ) * (k + 2 : ℤ) from by exact_mod_cast h2) using 1 <;>
      congr 1 <;> omega
  unfold powerDefect
  linear_combination
    (negativeBinomial p (k + 1) - negativeBinomial p k) * h2Z -
    (negativeBinomial p (k + 2) - negativeBinomial p (k + 1)) * h1Z

open PowerSeries

/-- The extremal series, including its actual zero boundary, is fixed by the
minimal dyadic refinement mask. -/
theorem negativeBinomial_series_refinement (p : ℕ) :
    (1 + X : ℤ⟦X⟧) ^ (p + 1) *
      PowerSeries.expand 2 (by omega) (invOneSubPow ℤ (p + 1)).val =
      (invOneSubPow ℤ (p + 1)).val := by
  let S : ℤ⟦X⟧ := (invOneSubPow ℤ (p + 1)).val
  have hS : S * (1 - X) ^ (p + 1) = 1 := (invOneSubPow ℤ (p + 1)).val_inv
  have hS' : (1 - X) ^ (p + 1) * S = 1 := (invOneSubPow ℤ (p + 1)).inv_val
  have hexp := congrArg (PowerSeries.expand 2 (by omega)) hS
  simp only [map_mul, map_pow, map_sub, map_one, PowerSeries.expand_X] at hexp
  have hprod : ((1 + X : ℤ⟦X⟧) ^ (p + 1) * PowerSeries.expand 2 (by omega) S) *
      (1 - X) ^ (p + 1) = 1 := by
    calc
      _ = PowerSeries.expand 2 (by omega) S * ((1 + X) * (1 - X)) ^ (p + 1) := by
        rw [mul_pow]
        ring
      _ = PowerSeries.expand 2 (by omega) S * (1 - X ^ 2) ^ (p + 1) := by
        congr 2
        ring
      _ = 1 := hexp
  change (1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) S = S
  calc
    _ = ((1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) S) *
        ((1 - X) ^ (p + 1) * S) := by rw [hS', mul_one]
    _ = (((1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) S) *
        (1 - X) ^ (p + 1)) * S := by ring
    _ = S := by rw [hprod, one_mul]

#print axioms negativeBinomial_power_equality
#print axioms negativeBinomial_series_refinement
end BinaryResearch
