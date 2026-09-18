import BBFM.Binary.FlatProfile
import BBFM.Binary.RefinementMLRBridge

open PowerSeries
namespace BinaryResearch
noncomputable section

/-- At the left boundary, input monotonicity supplies the exact flat-envelope
ratio through the binomial kernel's TP2 inequality. -/
theorem refined_flat_bound_of_input_mono (p k : ℕ) (hk : 1 ≤ k) (F : ℝ⟦X⟧)
    (hmono : ∀ i ≤ k / 2, ∀ j ≤ k / 2, i ≤ j → PowerSeries.coeff i F ≤ PowerSeries.coeff j F)
    (ha : 0 < PowerSeries.coeff (k - 1) (refineSeries p F)) :
    flatRefinementCoeff p k / flatRefinementCoeff p (k - 1) ≤
      PowerSeries.coeff k (refineSeries p F) / PowerSeries.coeff (k - 1) (refineSeries p F) := by
  have hm := series_refinement_mlr (p + 1) (k - 1) (k / 2) (by omega) flatSeries F
    (by
      intro i hi j hj hij
      simp only [flatSeries_coeff, one_mul]
      exact hmono i hi j hj hij)
  rw [Nat.sub_add_cancel hk, flatSeries_refinement_coeff, flatSeries_refinement_coeff] at hm
  apply (div_le_div_iff₀ (flatRefinementCoeff_positive p (k - 1)) ha).mpr
  change flatRefinementCoeff p k * PowerSeries.coeff (k - 1) (refineSeries p F) ≤
    PowerSeries.coeff k (refineSeries p F) * flatRefinementCoeff p (k - 1)
  dsimp only [refineSeries]
  nlinarith only [hm]

/-- Past the forcing range the flat envelope is constant, so ordinary output
monotonicity is enough. -/
theorem refined_flat_bound_of_output_mono (p k : ℕ) (hk : p < k) (F : ℝ⟦X⟧)
    (hmono : PowerSeries.coeff (k - 1) (refineSeries p F) ≤ PowerSeries.coeff k (refineSeries p F))
    (ha : 0 < PowerSeries.coeff (k - 1) (refineSeries p F)) :
    flatRefinementCoeff p k / flatRefinementCoeff p (k - 1) ≤
      PowerSeries.coeff k (refineSeries p F) / PowerSeries.coeff (k - 1) (refineSeries p F) := by
  have he := flatRefinementCoeff_tail p (k - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k)] at he
  rw [he, div_self (flatRefinementCoeff_positive p (k - 1)).ne']
  exact (one_le_div ha).mpr hmono

#print axioms refined_flat_bound_of_input_mono
#print axioms refined_flat_bound_of_output_mono
end
end BinaryResearch
