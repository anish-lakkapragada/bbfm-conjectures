import BBFM.Binary.EnvelopeRefinement
import BBFM.Binary.FlatLowerBound
import BBFM.Binary.LogConcavity.RealificationBridge
import BBFM.Binary.LogConcavity.UniformClosure
import BBFM.Binary.LogConcavity.PowerConcavityReflection

open Polynomial BinaryShape BinaryRealification
namespace BinaryResearch
noncomputable section

lemma shape_coeff_mono (P : ℤ[X]) (d : ℕ) (h : HasShape P d)
    (i j : ℕ) (hij : i ≤ j) (hj : 2 * j ≤ d) : P.coeff i ≤ P.coeff j := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; rfl
    · exact le_trans (ih i (by omega) (by omega)) (h.mono j (by omega))

lemma powerConcave_first_bound (p : ℤ) (P : ℤ[X]) (hzero : 0 < P.coeff 0)
    (hpc : PowerConcave p P) : P.coeff 1 ≤ (p + 1) * P.coeff 0 := by
  have h := hpc 0
  norm_num [BinaryShape.intCoeff, PowerConcaveAt] at h
  apply le_of_mul_le_mul_left (show P.coeff 0 * P.coeff 1 ≤ P.coeff 0 * ((p + 1) * P.coeff 0) by nlinarith) hzero

lemma minimal_refinement_coeff_zero (P : ℤ[X]) (p : ℕ) :
    (((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff 0 = P.coeff 0 := by
  rw [mul_coeff_zero, comp_square_coeff]
  simp [coeff_one_add_X_pow]

lemma minimal_refinement_coeff_one (P : ℤ[X]) (p : ℕ) :
    (((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff 1 = (p + 1 : ℤ) * P.coeff 0 := by
  rw [mul_coeff_one, comp_square_coeff, comp_square_coeff]
  simp [coeff_one_add_X_pow]

/-- The left endpoint of minimal refinement is an exact power-concavity equality. -/
lemma minimal_refinement_pc_zero (P : ℤ[X]) (p : ℕ) :
    PowerConcaveAt p 0 ((((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff 0)
      ((((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff 1) := by
  rw [minimal_refinement_coeff_zero, minimal_refinement_coeff_one]
  unfold PowerConcaveAt
  nlinarith

/-- Minimal dyadic refinement preserves the quantitative curvature inequality
on the entire lower half. The hypotheses concern an arbitrary finite symmetric
unimodal positive polynomial, rather than any source-specific recurrence. -/
theorem minimal_refinement_pc_lower (P : ℤ[X]) (d p k : ℕ)
    (hp : 1 ≤ p) (hpd : p ≤ d) (hshape : HasShape P d)
    (hzero : 0 < P.coeff 0) (hpc : PowerConcave p P)
    (hk : 1 ≤ k) (hhalf : 2 * k ≤ 2 * d + (p + 1)) :
    PowerConcaveAt p
      ((((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff (k - 1))
      ((((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff k)
      ((((1 + X) ^ (p + 1)) * P.comp (X ^ 2)).coeff (k + 1)) := by
  let Q : ℤ[X] := ((1 + X) ^ (p + 1)) * P.comp (X ^ 2)
  have hQ : HasShape Q (2 * d + (p + 1)) :=
    binomial_comp_square_shape P d (p + 1) (by omega) hshape
  have hQzero : 0 < Q.coeff 0 := by
    dsimp only [Q]
    rw [minimal_refinement_coeff_zero]
    exact hzero
  have hPpos (i : ℕ) (hi : i ≤ d) : 0 < P.coeff i := BinaryLC.shape_positive P d hshape hzero i hi
  have hQpos (i : ℕ) (hi : i ≤ 2 * d + (p + 1)) : 0 < Q.coeff i :=
    BinaryLC.shape_positive Q _ hQ hQzero i hi
  let F := toRealSeries P
  have hout (i : ℕ) : PowerSeries.coeff i (refineSeries p F) = (Q.coeff i : ℝ) := by
    rw [refineSeries_toRealSeries, coeff_toRealSeries]
  have hfpos (i : ℕ) (hi : i ≤ d) : 0 < PowerSeries.coeff i F := by
    simp only [F, coeff_toRealSeries]
    exact_mod_cast hPpos i hi
  have hfsup (i : ℕ) (hi : d < i) : PowerSeries.coeff i F = 0 := by
    simp only [F, coeff_toRealSeries, hshape.support i hi, Int.cast_zero]
  have hf (i : ℕ) (hi : i + 2 ≤ d) : BinaryPowerConcavity.PC p
      (PowerSeries.coeff i F) (PowerSeries.coeff (i + 1) F) (PowerSeries.coeff (i + 2) F) := by
    have h := hpc (i + 1)
    have he₁ : (i : ℤ) + 1 - 1 = i := by omega
    have he₂ : (i : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) := by omega
    have he₃ : (i : ℤ) + 1 + 1 = ((i + 2 : ℕ) : ℤ) := by omega
    rw [he₁, he₃, he₂, intCoeff_nat, intCoeff_nat, intCoeff_nat] at h
    have hr := (powerConcaveAt_iff_real _ _ _ _).mp h
    simpa only [F, coeff_toRealSeries, Int.cast_natCast] using hr
  have hfirst : PowerSeries.coeff 1 F ≤ (p + 1 : ℝ) * PowerSeries.coeff 0 F := by
    have h := powerConcave_first_bound p P hzero hpc
    simp only [F, coeff_toRealSeries]
    exact_mod_cast h
  have ha : 0 < PowerSeries.coeff (k - 1) (refineSeries p F) := by
    rw [hout]
    exact_mod_cast hQpos (k - 1) (by omega)
  have hb : 0 < PowerSeries.coeff k (refineSeries p F) := by
    rw [hout]
    exact_mod_cast hQpos k (by omega)
  have hflat : flatRefinementCoeff p k / flatRefinementCoeff p (k - 1) ≤
      PowerSeries.coeff k (refineSeries p F) / PowerSeries.coeff (k - 1) (refineSeries p F) := by
    by_cases hkp : k ≤ p
    · apply refined_flat_bound_of_input_mono p k hk F _ ha
      intro i hi j hj hij
      simp only [F, coeff_toRealSeries]
      exact_mod_cast shape_coeff_mono P d hshape i j hij (by omega)
    · apply refined_flat_bound_of_output_mono p k (by omega) F _ ha
      rw [hout, hout]
      have hm := hQ.mono (k - 1) (by omega)
      rw [Nat.sub_add_cancel hk] at hm
      exact_mod_cast hm
  have h := refined_pc_of_flat_bound p d k hp hk F hfpos hfsup hf hfirst ha hb hflat
  rw [hout, hout, hout] at h
  apply real_pc_to_integer
  simpa only [Int.cast_natCast] using h

/-- Full zero-extended quantitative curvature preservation under the minimal
binomial mask for dyadic stretching. This is a generic all-degree theorem. -/
theorem minimal_refinement_powerConcave (P : ℤ[X]) (d p : ℕ)
    (hp : 1 ≤ p) (hpd : p ≤ d) (hshape : HasShape P d)
    (hzero : 0 < P.coeff 0) (hpc : PowerConcave p P) :
    PowerConcave p (((1 + X) ^ (p + 1)) * P.comp (X ^ 2)) := by
  apply powerConcave_of_lower_half p _ (2 * d + (p + 1))
    (binomial_comp_square_shape P d (p + 1) (by omega) hshape)
  intro k hhalf
  by_cases hk : k = 0
  · subst k
    simpa [intCoeff] using minimal_refinement_pc_zero P p
  · have he₁ : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
    have he₂ : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
    rw [he₁, he₂, intCoeff_nat, intCoeff_nat, intCoeff_nat]
    exact minimal_refinement_pc_lower P d p k hp hpd hshape hzero hpc (by omega) hhalf

#print axioms minimal_refinement_powerConcave
#print axioms minimal_refinement_pc_lower
#print axioms minimal_refinement_pc_zero
end
end BinaryResearch
