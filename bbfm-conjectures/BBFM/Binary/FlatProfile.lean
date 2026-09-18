import BBFM.Binary.RefinementCoefficients
import BBFM.Binary.RealSeriesRefinement

open PowerSeries BinaryRealSeries
namespace BinaryResearch
noncomputable section

def flatSeries : ℝ⟦X⟧ := PowerSeries.mk (fun _ => 1)

@[simp] lemma flatSeries_coeff (k : ℕ) : PowerSeries.coeff k flatSeries = 1 := by
  simp [flatSeries]

lemma flatSeries_duplicate :
    (1 + X) * PowerSeries.expand 2 (by omega) flatSeries = flatSeries := by
  ext k
  rw [series_duplicated_coeff, flatSeries_coeff, flatSeries_coeff]

lemma flatSeries_difference : (1 - X) * flatSeries = 1 := by
  ext k
  rw [sub_mul, one_mul]
  cases k with
  | zero => simp [flatSeries]
  | succ k => simp [coeff_succ_X_mul]

lemma flatSeries_refinement (p : ℕ) :
    (1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) flatSeries =
      (1 + X) ^ p * flatSeries := by
  rw [pow_succ, mul_assoc, flatSeries_duplicate]

lemma flatSeries_refinement_coeff (p k : ℕ) :
    PowerSeries.coeff k ((1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) flatSeries) =
      flatRefinementCoeff p k := by
  rw [series_refinement_coeff]
  simp only [flatSeries_coeff, mul_one, flatRefinementCoeff]

/-- The flat-input lower envelope is the cumulative binomial sequence. -/
theorem flatRefinementCoeff_difference (p k : ℕ) :
    flatRefinementCoeff p (k + 1) - flatRefinementCoeff p k = (p.choose (k + 1) : ℝ) := by
  let Q : ℝ⟦X⟧ := (1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) flatSeries
  have he : (1 - X) * Q = (1 + X) ^ p := by
    dsimp [Q]
    rw [flatSeries_refinement]
    calc
      (1 - X) * ((1 + X) ^ p * flatSeries) = (1 + X) ^ p * ((1 - X) * flatSeries) := by ring
      _ = (1 + X) ^ p := by rw [flatSeries_difference, mul_one]
  have hc := congrArg (PowerSeries.coeff (k + 1)) he
  rw [sub_mul, one_mul, map_sub, coeff_succ_X_mul] at hc
  dsimp [Q] at hc
  rw [flatSeries_refinement_coeff, flatSeries_refinement_coeff, series_one_add_X_pow_coeff] at hc
  exact hc

theorem flatRefinementCoeff_tail (p k : ℕ) (hk : p ≤ k) :
    flatRefinementCoeff p (k + 1) = flatRefinementCoeff p k := by
  have he := flatRefinementCoeff_difference p k
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero] at he
  exact sub_eq_zero.mp he

#print axioms flatRefinementCoeff_difference
#print axioms flatRefinementCoeff_tail
end
end BinaryResearch
