import BBFM.Binary.RefinementComparison
import BBFM.Binary.LogConcavity.BinomialRefinementMLR

open Finset PowerSeries
namespace BinaryResearch
noncomputable section

lemma series_refinement_kernel_sum (L k d : ℕ) (hkd : k / 2 ≤ d) (F : ℝ⟦X⟧) :
    PowerSeries.coeff k ((1 + X) ^ L * PowerSeries.expand 2 (by omega) F) =
      ∑ j ∈ range (d + 1), BinaryRefinementMLR.kernel L k j * PowerSeries.coeff j F := by
  rw [series_refinement_coeff]
  calc
    _ = ∑ j ∈ range (k / 2 + 1), BinaryRefinementMLR.kernel L k j * PowerSeries.coeff j F := by
      apply sum_congr rfl
      intro j hj
      rw [BinaryRefinementMLR.kernel, if_pos (by have hh := mem_range.mp hj; omega)]
    _ = _ := by
      apply sum_subset (range_mono (by omega))
      intro j hj hnot
      have hlarge : k < 2 * j := by
        simp only [mem_range] at hj hnot
        omega
      rw [BinaryRefinementMLR.kernel, if_neg (by omega), zero_mul]

/-- Exact finite-kernel bridge for the comparison of adjacent refined coefficients. -/
theorem series_refinement_mlr (L k d : ℕ) (hkd : (k + 1) / 2 ≤ d) (F G : ℝ⟦X⟧)
    (hfg : ∀ i ≤ d, ∀ j ≤ d, i ≤ j →
      PowerSeries.coeff j F * PowerSeries.coeff i G ≤ PowerSeries.coeff i F * PowerSeries.coeff j G) :
    PowerSeries.coeff (k + 1) ((1 + X) ^ L * PowerSeries.expand 2 (by omega) F) *
        PowerSeries.coeff k ((1 + X) ^ L * PowerSeries.expand 2 (by omega) G) ≤
      PowerSeries.coeff k ((1 + X) ^ L * PowerSeries.expand 2 (by omega) F) *
        PowerSeries.coeff (k + 1) ((1 + X) ^ L * PowerSeries.expand 2 (by omega) G) := by
  rw [series_refinement_kernel_sum L (k + 1) d hkd F,
    series_refinement_kernel_sum L k d (by omega) G,
    series_refinement_kernel_sum L k d (by omega) F,
    series_refinement_kernel_sum L (k + 1) d hkd G]
  apply BinaryRefinementMLR.binomial_refinement_mlr
  intro i hi j hj hij
  exact hfg i (by have hh := mem_range.mp hi; omega) j (by have hh := mem_range.mp hj; omega) hij

/-- The zero-shift equality profile bounds all input ratios from above. -/
theorem pc_zero_profile_mlr (p d : ℕ) (hp : 1 ≤ p) (f : ℕ → ℝ)
    (hfpos : ∀ i ≤ d, 0 < f i) (hfsup : ∀ i, d < i → f i = 0)
    (hf : ∀ i, i + 2 ≤ d → BinaryPowerConcavity.PC p (f i) (f (i + 1)) (f (i + 2)))
    (hfirst : f 1 ≤ (p + 1 : ℝ) * f 0) (i j : ℕ) (hij : i ≤ j) :
    f j * shiftedProfile p 0 i ≤ f i * shiftedProfile p 0 j := by
  have hgpos := shiftedProfile_positive p 0 (le_refl 0)
  have hg1 : shiftedProfile p 0 1 = (p + 1 : ℝ) * shiftedProfile p 0 0 := by
    simpa using shiftedProfile_recurrence p 0 0
  have hs : f 1 / shiftedProfile p 0 1 ≤ f 0 / shiftedProfile p 0 0 := by
    apply (div_le_div_iff₀ (hgpos 1) (hgpos 0)).mpr
    rw [hg1]
    have he := mul_le_mul_of_nonneg_right hfirst (hgpos 0).le
    nlinarith
  have hr := pc_ratio_local_descent p f (shiftedProfile p 0) d (by exact_mod_cast hp)
    hfpos hfsup hgpos hf (fun k => shiftedProfile_equality p k 0 (le_refl 0))
  have htail := ratio_descent_tail (fun k => f k / shiftedProfile p 0 k) hr 0 i j (by omega) hij hs
  exact (div_le_div_iff₀ (hgpos j) (hgpos i)).mp htail

/-- The maximal profile comparison remains valid at every output index. -/
theorem refined_zero_profile_mlr (p d : ℕ) (hp : 1 ≤ p) (F : ℝ⟦X⟧)
    (hfpos : ∀ i ≤ d, 0 < PowerSeries.coeff i F)
    (hfsup : ∀ i, d < i → PowerSeries.coeff i F = 0)
    (hf : ∀ i, i + 2 ≤ d → BinaryPowerConcavity.PC p (PowerSeries.coeff i F)
      (PowerSeries.coeff (i + 1) F) (PowerSeries.coeff (i + 2) F))
    (hfirst : PowerSeries.coeff 1 F ≤ (p + 1 : ℝ) * PowerSeries.coeff 0 F) (k : ℕ) :
    PowerSeries.coeff (k + 1) (refineSeries p F) * PowerSeries.coeff k (refinedShiftedSeries p 0) ≤
      PowerSeries.coeff k (refineSeries p F) * PowerSeries.coeff (k + 1) (refinedShiftedSeries p 0) := by
  apply series_refinement_mlr (p + 1) k ((k + 1) / 2) (le_refl _) F (shiftedSeries p 0)
  intro i hi j hj hij
  simp only [shiftedSeries_coeff]
  exact pc_zero_profile_mlr p d hp (fun k => PowerSeries.coeff k F) hfpos hfsup hf hfirst i j hij

#print axioms series_refinement_mlr
#print axioms refined_zero_profile_mlr
end
end BinaryResearch
