import BBFM.Binary.MinimalRefinement
import BBFM.Binary.LogConcavity.PowerConcavityPolynomial
import BBFM.Binary.Positivity

open Polynomial BinaryShape BinaryPowerClosure
namespace BinaryResearch
noncomputable section

lemma shape_interval_positive (P : ℤ[X]) (d : ℕ) (h : HasShape P d)
    (hzero : 0 < P.coeff 0) : IntervalPositive (intCoeff P) 0 d := by
  refine ⟨by positivity, intCoeff_nonneg P h.nonneg, ?_⟩
  intro z
  by_cases hz : 0 ≤ z
  · rw [intCoeff, if_pos hz]
    constructor
    · intro hp
      refine ⟨hz, ?_⟩
      by_contra hzd
      rw [h.support z.toNat (by omega)] at hp
      omega
    · rintro ⟨_, hzd⟩
      exact BinaryLC.shape_positive P d h hzero z.toNat (by omega)
  · simp [intCoeff, hz]

lemma center_degree_lower (n : ℕ) : n - 1 ≤ 2 * center n := by
  by_cases hn : n = 0
  · subst n; omega
  · have hs : (∑ j ∈ Finset.range 1, 2 ^ j * (n / 2 ^ (j + 1))) ≤ center n := by
      unfold center
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    norm_num at hs
    omega

/-- Additional binomial factors raise the parameter exactly as required by the
source recurrence. The minimal-refinement premise is explicit here. -/
theorem extended_refinement_of_minimal (P : ℤ[X]) (d p r : ℕ)
    (hp : 1 ≤ p) (hr : p + 1 ≤ r) (hshape : HasShape P d)
    (hzero : 0 < P.coeff 0)
    (hmin : PowerConcave p (((1 + X) ^ (p + 1)) * P.comp (X ^ 2))) :
    PowerConcave ((r : ℤ) - 1) (((1 + X) ^ r) * P.comp (X ^ 2)) := by
  let Q : ℤ[X] := ((1 + X) ^ (p + 1)) * P.comp (X ^ 2)
  have hQ : HasShape Q (2 * d + (p + 1)) :=
    binomial_comp_square_shape P d (p + 1) (by omega) hshape
  have hQzero : 0 < Q.coeff 0 := by
    dsimp only [Q]
    rw [minimal_refinement_coeff_zero]
    exact hzero
  have hs := shape_interval_positive Q _ hQ hQzero
  have hb := (binomial_preserves Q 0 ((2 * d + (p + 1) : ℕ) : ℤ) p
    (by exact_mod_cast hp) hs hmin (r - (p + 1))).2
  have hparam : (p : ℤ) + (r - (p + 1) : ℕ) = (r : ℤ) - 1 := by omega
  rw [hparam] at hb
  have he : ((1 + X : ℤ[X]) ^ (r - (p + 1))) * Q =
      ((1 + X) ^ r) * P.comp (X ^ 2) := by
    dsimp only [Q]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  rw [he] at hb
  exact hb

/-- Every mask at least as long as the minimal one preserves quantitative
curvature, with final parameter equal to the mask exponent minus one. -/
theorem extended_refinement_powerConcave (P : ℤ[X]) (d p r : ℕ)
    (hp : 1 ≤ p) (hpd : p ≤ d) (hr : p + 1 ≤ r)
    (hshape : HasShape P d) (hzero : 0 < P.coeff 0) (hpc : PowerConcave p P) :
    PowerConcave ((r : ℤ) - 1) (((1 + X) ^ r) * P.comp (X ^ 2)) :=
  extended_refinement_of_minimal P d p r hp hr hshape hzero
    (minimal_refinement_powerConcave P d p hp hpd hshape hzero hpc)

/-- Exact source-recursion smoothing step. The only inductive hypothesis is
source power-concavity at the half index; every shape/support premise is an
unconditional theorem for the actual public numerator. -/
theorem source_smoothing_powerConcave (n : ℕ) (hn : 2 ≤ n)
    (hpc : PowerConcave ((n : ℤ) - 1) (numB n)) :
    PowerConcave ((2 * n : ℕ) - 1 : ℤ)
      (((1 + X) ^ (2 * n)) * (numB n).comp (X ^ 2)) := by
  have hpcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have h := extended_refinement_powerConcave (numB n) (2 * center n) (n - 1) (2 * n)
    (by omega) (center_degree_lower n) (by omega) (numB_shape n hn)
    (numB_coeff_pos n hn 0 (by omega)) (by rw [hpcast]; exact hpc)
  exact h

#print axioms extended_refinement_powerConcave
#print axioms source_smoothing_powerConcave
#print axioms shape_interval_positive
#print axioms center_degree_lower
#print axioms extended_refinement_of_minimal
end
end BinaryResearch
