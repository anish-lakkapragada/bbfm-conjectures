import BBFM.Binary.SeriesMask
import BBFM.Binary.LogConcavity.RealSignInterval

namespace BinaryRealSeries
open PowerSeries BinaryRealSign

noncomputable def seriesIntCoeff (F : ℝ⟦X⟧) (z : ℤ) : ℝ :=
  if 0 ≤ z then F.coeff z.toNat else 0

lemma seriesIntCoeff_nat (F : ℝ⟦X⟧) (k : ℕ) : seriesIntCoeff F k = F.coeff k := by
  simp [seriesIntCoeff]

lemma seriesIntCoeff_bernoulli (F : ℝ⟦X⟧) (z : ℤ) :
    seriesIntCoeff ((1 + X) * F) z = bernoulliSequence (seriesIntCoeff F) z := by
  unfold bernoulliSequence
  by_cases hz0 : 0 ≤ z
  · simp only [seriesIntCoeff, if_pos hz0, add_mul, one_mul, map_add]
    have hx := PowerSeries.coeff_X_pow_mul' F 1 z.toNat
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
    simp only [seriesIntCoeff, if_neg hz0, if_neg hm, add_zero]

lemma series_duplicated_coeff (F : ℝ⟦X⟧) (k : ℕ) :
    (((1 + X) * PowerSeries.expand 2 (by omega) F).coeff k) = F.coeff (k / 2) := by
  have hc : ∀ j, (PowerSeries.expand 2 (by omega) F).coeff j =
      if 2 ∣ j then F.coeff (j / 2) else 0 := fun _ => PowerSeries.coeff_expand _ _ _
  rw [add_mul, one_mul, map_add]
  cases k with
  | zero => simp [hc]
  | succ k =>
    have hx := PowerSeries.coeff_X_pow_mul (PowerSeries.expand 2 (by omega) F) 1 k
    rw [pow_one] at hx
    rw [hx, hc, hc]
    by_cases he : 2 ∣ k
    · have ho : ¬ 2 ∣ k + 1 := by omega
      rw [if_pos he, if_neg ho, zero_add]
      have heq : k / 2 = (k + 1) / 2 := by omega
      rw [heq]
    · have ho : 2 ∣ k + 1 := by omega
      rw [if_neg he, if_pos ho, add_zero]

lemma seriesIntCoeff_duplicate (F : ℝ⟦X⟧) (z : ℤ) :
    seriesIntCoeff ((1 + X) * PowerSeries.expand 2 (by omega) F) z =
      duplicateSequence (seriesIntCoeff F) z := by
  by_cases hz : 0 ≤ z
  · have he : z = (z.toNat : ℤ) := by omega
    rw [he, seriesIntCoeff_nat, series_duplicated_coeff]
    unfold duplicateSequence
    rw [show (z.toNat : ℤ) / 2 = ((z.toNat / 2 : ℕ) : ℤ) by omega, seriesIntCoeff_nat]
  · have hh : ¬ 0 ≤ z / 2 := by omega
    simp [seriesIntCoeff, duplicateSequence, hz, hh]

lemma seriesIntCoeff_refined (r : ℕ) (F : ℝ⟦X⟧) (z : ℤ) :
    seriesIntCoeff ((1 + X) ^ (r + 1) * PowerSeries.expand 2 (by omega) F) z =
      refinedSequence r (seriesIntCoeff F) z := by
  induction r generalizing z with
  | zero => simpa [refinedSequence] using seriesIntCoeff_duplicate F z
  | succ r ih =>
    have he : (1 + X : ℝ⟦X⟧) ^ (r + 1 + 1) * PowerSeries.expand 2 (by omega) F =
        (1 + X) * ((1 + X) ^ (r + 1) * PowerSeries.expand 2 (by omega) F) := by
      rw [pow_succ]
      ring
    rw [he, seriesIntCoeff_bernoulli]
    unfold bernoulliSequence
    rw [ih, ih]
    rfl

lemma seriesIntCoeff_sub (F G : ℝ⟦X⟧) (z : ℤ) :
    seriesIntCoeff (F - G) z = seriesIntCoeff F z - seriesIntCoeff G z := by
  by_cases hz : 0 ≤ z <;> simp [seriesIntCoeff, hz]

lemma seriesIntCoeff_C_mul (a : ℝ) (F : ℝ⟦X⟧) (z : ℤ) :
    seriesIntCoeff (C a * F) z = a * seriesIntCoeff F z := by
  by_cases hz : 0 ≤ z <;> simp [seriesIntCoeff, hz]

/-- Real formal power-series version, allowing infinite comparison profiles. -/
theorem positiveInterval_series_refinement (r : ℕ) (F : ℝ⟦X⟧)
    (h : PositiveInterval (seriesIntCoeff F)) :
    PositiveInterval (seriesIntCoeff ((1 + X) ^ (r + 1) * PowerSeries.expand 2 (by omega) F)) := by
  have he : seriesIntCoeff ((1 + X) ^ (r + 1) * PowerSeries.expand 2 (by omega) F) =
      refinedSequence r (seriesIntCoeff F) := funext (seriesIntCoeff_refined r F)
  rw [he]
  exact positiveInterval_refinedSequence r _ h

#print axioms positiveInterval_series_refinement
end BinaryRealSeries
