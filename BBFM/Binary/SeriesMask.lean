import BBFM.Binary.ShiftedProfile

open PowerSeries Finset
namespace BinaryResearch
noncomputable section

lemma series_mul_nonneg (A B : ℝ⟦X⟧)
    (hA : ∀ k, 0 ≤ PowerSeries.coeff k A) (hB : ∀ k, 0 ≤ PowerSeries.coeff k B)
    (k : ℕ) : 0 ≤ PowerSeries.coeff k (A * B) := by
  rw [PowerSeries.coeff_mul]
  exact sum_nonneg fun ij hij => mul_nonneg (hA ij.1) (hB ij.2)

lemma series_one_add_X_pow_coeff (p k : ℕ) :
    PowerSeries.coeff k ((1 + X : ℝ⟦X⟧) ^ p) = (p.choose k : ℝ) := by
  have he : (((1 + Polynomial.X : Polynomial ℝ) ^ p : Polynomial ℝ) : ℝ⟦X⟧) =
      (1 + X) ^ p := by simp
  rw [← he, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

lemma series_one_add_X_pow_nonneg (p k : ℕ) :
    0 ≤ PowerSeries.coeff k ((1 + X : ℝ⟦X⟧) ^ p) := by
  rw [series_one_add_X_pow_coeff]
  positivity

lemma series_expand_two_nonneg (A : ℝ⟦X⟧)
    (hA : ∀ k, 0 ≤ PowerSeries.coeff k A) (k : ℕ) :
    0 ≤ PowerSeries.coeff k (PowerSeries.expand 2 (by omega) A) := by
  rw [PowerSeries.coeff_expand]
  split_ifs
  · exact hA _
  · exact le_refl _

lemma eulerSeries_binomial_identity (p : ℕ) (A : ℝ⟦X⟧) :
    (1 + X) * eulerSeries ((1 + X) ^ (p + 1) * A) =
      C ((p + 1 : ℕ) : ℝ) * (X * ((1 + X) ^ (p + 1) * A)) +
        (1 + X) ^ (p + 2) * eulerSeries A := by
  rw [eulerSeries_binomial_mul]
  simp only [pow_succ, map_natCast]
  ring

/-- Every nonnegative input has the binomial mask's lower-boundary ratio. -/
theorem series_binomial_mask_ratio (p k : ℕ) (A : ℝ⟦X⟧)
    (hA : ∀ i, 0 ≤ PowerSeries.coeff i A) :
    (p + 1 - (k : ℝ)) * PowerSeries.coeff k ((1 + X) ^ (p + 1) * A) ≤
      (k + 1 : ℝ) * PowerSeries.coeff (k + 1) ((1 + X) ^ (p + 1) * A) := by
  have he := congrArg (PowerSeries.coeff (k + 1)) (eulerSeries_binomial_identity p A)
  simp only [add_mul, one_mul, series_coeff_add, coeff_succ_X_mul,
    coeff_C_mul, eulerSeries_coeff] at he
  have hn : 0 ≤ PowerSeries.coeff (k + 1) ((1 + X) ^ (p + 2) * eulerSeries A) :=
    series_mul_nonneg _ _ (series_one_add_X_pow_nonneg (p + 2))
      (fun i => by rw [eulerSeries_coeff]; exact mul_nonneg (Nat.cast_nonneg _) (hA i)) _
  push_cast at he ⊢
  linarith

lemma refinedShiftedSeries_nonneg (p : ℕ) (h : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    0 ≤ PowerSeries.coeff k (refinedShiftedSeries p h) :=
  series_mul_nonneg _ _ (series_one_add_X_pow_nonneg (p + 1))
    (series_expand_two_nonneg _ (fun i => by simpa using (shiftedProfile_positive p h hh i).le)) k

lemma refinedShiftedSeries_mask_ratio (p k : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    (p + 1 - (k : ℝ)) * PowerSeries.coeff k (refinedShiftedSeries p h) ≤
      (k + 1 : ℝ) * PowerSeries.coeff (k + 1) (refinedShiftedSeries p h) :=
  series_binomial_mask_ratio p k _
    (series_expand_two_nonneg _ (fun i => by simpa using (shiftedProfile_positive p h hh i).le))

#print axioms series_binomial_mask_ratio
#print axioms refinedShiftedSeries_mask_ratio
end
end BinaryResearch
