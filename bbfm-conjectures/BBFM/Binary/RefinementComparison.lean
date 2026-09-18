import BBFM.Binary.RealPowerComparison
import BBFM.Binary.RefinementCoefficients

open PowerSeries BinaryPowerConcavity BinaryRealSeries
namespace BinaryResearch
noncomputable section

def refineSeries (p : ℕ) (F : ℝ⟦X⟧) : ℝ⟦X⟧ :=
  (1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) F

lemma refineSeries_sub_C_mul (p : ℕ) (F G : ℝ⟦X⟧) (α : ℝ) :
    refineSeries p (F - C α * G) = refineSeries p F - C α * refineSeries p G := by
  unfold refineSeries
  rw [map_sub, map_mul, PowerSeries.expand_C]
  ring

/-- The comparison interval survives the exact real formal-series refinement. -/
theorem refined_pc_profile_positiveInterval (p d : ℕ) (hp : 1 ≤ p) (F : ℝ⟦X⟧)
    (hfpos : ∀ i ≤ d, 0 < PowerSeries.coeff i F)
    (hfsup : ∀ i, d < i → PowerSeries.coeff i F = 0)
    (hf : ∀ i, i + 2 ≤ d → PC p (PowerSeries.coeff i F)
      (PowerSeries.coeff (i + 1) F) (PowerSeries.coeff (i + 2) F))
    (h : ℝ) (hh : 0 ≤ h) (α : ℝ) :
    BinaryRealSign.PositiveInterval (fun z => seriesIntCoeff (refineSeries p F) z -
      α * seriesIntCoeff (refinedShiftedSeries p h) z) := by
  have hi := pc_shiftedProfile_positiveInterval p d hp (fun i => PowerSeries.coeff i F)
    hfpos hfsup hf h hh α
  have he : (fun z : ℤ => if 0 ≤ z then PowerSeries.coeff z.toNat F -
      α * shiftedProfile p h z.toNat else 0) =
      seriesIntCoeff (F - C α * shiftedSeries p h) := by
    funext z
    by_cases hz : 0 ≤ z <;> simp [seriesIntCoeff, hz]
  rw [he] at hi
  have ho := positiveInterval_series_refinement p (F - C α * shiftedSeries p h) hi
  change BinaryRealSign.PositiveInterval (seriesIntCoeff (refineSeries p (F - C α * shiftedSeries p h))) at ho
  rw [refineSeries_sub_C_mul] at ho
  have hout : seriesIntCoeff (refineSeries p F - C α * refineSeries p (shiftedSeries p h)) =
      (fun z => seriesIntCoeff (refineSeries p F) z -
        α * seriesIntCoeff (refinedShiftedSeries p h) z) := by
    funext z
    rw [seriesIntCoeff_sub, seriesIntCoeff_C_mul]
    rfl
  rw [hout] at ho
  exact ho

/-- A strict decrease relative to a comparison profile cannot reverse at the
next output coefficient. -/
theorem refined_profile_ratio_drop (p d k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k) (F : ℝ⟦X⟧)
    (hfpos : ∀ i ≤ d, 0 < PowerSeries.coeff i F)
    (hfsup : ∀ i, d < i → PowerSeries.coeff i F = 0)
    (hf : ∀ i, i + 2 ≤ d → PC p (PowerSeries.coeff i F)
      (PowerSeries.coeff (i + 1) F) (PowerSeries.coeff (i + 2) F))
    (h : ℝ) (hh : 0 ≤ h)
    (hd : PowerSeries.coeff k (refineSeries p F) *
        PowerSeries.coeff (k - 1) (refinedShiftedSeries p h) <
      PowerSeries.coeff (k - 1) (refineSeries p F) *
        PowerSeries.coeff k (refinedShiftedSeries p h)) :
    PowerSeries.coeff (k + 1) (refineSeries p F) *
        PowerSeries.coeff k (refinedShiftedSeries p h) ≤
      PowerSeries.coeff (k + 1) (refinedShiftedSeries p h) *
        PowerSeries.coeff k (refineSeries p F) := by
  let a := PowerSeries.coeff (k - 1) (refineSeries p F)
  let b := PowerSeries.coeff k (refineSeries p F)
  let c := PowerSeries.coeff (k + 1) (refineSeries p F)
  let A := PowerSeries.coeff (k - 1) (refinedShiftedSeries p h)
  let B := PowerSeries.coeff k (refinedShiftedSeries p h)
  let Cc := PowerSeries.coeff (k + 1) (refinedShiftedSeries p h)
  have hB : 0 < B := refinedShiftedSeries_positive p k h hh
  have hi := refined_pc_profile_positiveInterval p d hp F hfpos hfsup hf h hh (b / B)
  by_contra hn
  have ha : 0 < a - (b / B) * A := by
    apply sub_pos.mpr
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hB).mpr hd
  have hc : 0 < c - (b / B) * Cc := by
    apply sub_pos.mpr
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hB).mpr
    dsimp [b, B, c, Cc]
    nlinarith
  have hmid := hi ((k - 1 : ℕ) : ℤ) (k : ℤ) ((k + 1 : ℕ) : ℤ) (by omega) (by omega)
    (by simpa only [seriesIntCoeff_nat] using ha)
    (by simpa only [seriesIntCoeff_nat] using hc)
  simp only [seriesIntCoeff_nat] at hmid
  change 0 < b - (b / B) * B at hmid
  simp [hB.ne'] at hmid

#print axioms refined_pc_profile_positiveInterval
#print axioms refined_profile_ratio_drop
end
end BinaryResearch
