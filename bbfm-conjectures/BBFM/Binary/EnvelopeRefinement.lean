import BBFM.Binary.RefinementMLRBridge
import BBFM.Binary.FlatProfile
import BBFM.Binary.LogConcavity.ProfileAffineTransfer

open PowerSeries BinaryPowerConcavity
namespace BinaryResearch
noncomputable section

lemma refined_profile_ratio_match (p k : ℕ) (ρ : ℝ)
    (hlo : flatRefinementCoeff p k / flatRefinementCoeff p (k - 1) < ρ)
    (hhi : ρ < PowerSeries.coeff k (refinedShiftedSeries p 0) /
      PowerSeries.coeff (k - 1) (refinedShiftedSeries p 0)) :
    ∃ h : ℝ, 0 < h ∧ PowerSeries.coeff k (refinedShiftedSeries p h) /
      PowerSeries.coeff (k - 1) (refinedShiftedSeries p h) = ρ := by
  have he := BinaryProfileMixtures.exists_positive_shift_ratio p ((k - 1) / 2) (k / 2)
    (fun j => ((p + 1).choose (k - 1 - 2 * j) : ℝ))
    (fun j => ((p + 1).choose (k - 2 * j) : ℝ))
    (by intro j hj; positivity) (flatRefinementCoeff_positive p (k - 1)) ρ hlo
    (by simpa only [refinedShiftedSeries_mix] using hhi)
  simpa only [refinedShiftedSeries_mix] using he

/-- Local minimal-refinement closure whenever the output growth is at least
that of the flat-input envelope. The remaining shape proof supplies this bound. -/
theorem refined_pc_of_flat_bound (p d k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (F : ℝ⟦X⟧)
    (hfpos : ∀ i ≤ d, 0 < PowerSeries.coeff i F)
    (hfsup : ∀ i, d < i → PowerSeries.coeff i F = 0)
    (hf : ∀ i, i + 2 ≤ d → PC p (PowerSeries.coeff i F)
      (PowerSeries.coeff (i + 1) F) (PowerSeries.coeff (i + 2) F))
    (hfirst : PowerSeries.coeff 1 F ≤ (p + 1 : ℝ) * PowerSeries.coeff 0 F)
    (ha : 0 < PowerSeries.coeff (k - 1) (refineSeries p F))
    (hb : 0 < PowerSeries.coeff k (refineSeries p F))
    (hflat : flatRefinementCoeff p k / flatRefinementCoeff p (k - 1) ≤
      PowerSeries.coeff k (refineSeries p F) / PowerSeries.coeff (k - 1) (refineSeries p F)) :
    PC p (PowerSeries.coeff (k - 1) (refineSeries p F))
      (PowerSeries.coeff k (refineSeries p F)) (PowerSeries.coeff (k + 1) (refineSeries p F)) := by
  let a := PowerSeries.coeff (k - 1) (refineSeries p F)
  let b := PowerSeries.coeff k (refineSeries p F)
  let c := PowerSeries.coeff (k + 1) (refineSeries p F)
  let A := fun h => PowerSeries.coeff (k - 1) (refinedShiftedSeries p h)
  let B := fun h => PowerSeries.coeff k (refinedShiftedSeries p h)
  let D := fun h => PowerSeries.coeff (k + 1) (refinedShiftedSeries p h)
  have hApos (h : ℝ) (hh : 0 ≤ h) : 0 < A h := refinedShiftedSeries_positive p (k - 1) h hh
  have hBpos (h : ℝ) (hh : 0 ≤ h) : 0 < B h := refinedShiftedSeries_positive p k h hh
  have hprofile (h : ℝ) (hh : 0 ≤ h) : PC p (A h) (B h) (D h) :=
    refinedShiftedSeries_pc p k hp hk h hh
  have hu := refined_zero_profile_mlr p d hp F hfpos hfsup hf hfirst (k - 1)
  rw [Nat.sub_add_cancel hk] at hu
  change b * A 0 ≤ a * B 0 at hu
  have hupper : b / a ≤ B 0 / A 0 := by
    apply (div_le_div_iff₀ ha (hApos 0 (le_refl 0))).mpr
    nlinarith only [hu]
  rcases eq_or_lt_of_le hupper with heq | hlt
  · have hm : b * A 0 = a * B 0 := by
      have hh := (div_eq_div_iff ha.ne' (hApos 0 (le_refl 0)).ne').mp heq
      nlinarith only [hh]
    have hc := refined_zero_profile_mlr p d hp F hfpos hfsup hf hfirst k
    exact pc_of_exact_profile_match p (A 0) (B 0) (D 0) a b c (by exact_mod_cast hp)
      (hApos 0 (le_refl 0)) (hBpos 0 (le_refl 0)) ha hb (hprofile 0 (le_refl 0)) hm hc
  · apply pc_of_affine_bounds p a b c (B 0 / A 0) ha hlt
    intro ρ hrlo hrhi
    have hlo : flatRefinementCoeff p k / flatRefinementCoeff p (k - 1) < ρ :=
      lt_of_le_of_lt hflat hrlo
    obtain ⟨h, hh, hmatch⟩ := refined_profile_ratio_match p k ρ hlo hrhi
    have hd : b * A h < a * B h := by
      have hrat : b / a < B h / A h := by rw [hmatch]; exact hrlo
      have hx := (div_lt_div_iff₀ ha (hApos h hh.le)).mp hrat
      nlinarith only [hx]
    have hc := refined_profile_ratio_drop p d k hp hk F hfpos hfsup hf h hh.le hd
    have hcross : c * B h ≤ b * D h := by
      change c * B h ≤ D h * b at hc
      nlinarith only [hc]
    have hbound := profile_affine_bound p (A h) (B h) (D h) b c
      (by exact_mod_cast hp) (hApos h hh.le) (hBpos h hh.le) hb.le (hprofile h hh.le) hcross
    rw [hmatch] at hbound
    exact hbound

#print axioms refined_pc_of_flat_bound
end
end BinaryResearch
