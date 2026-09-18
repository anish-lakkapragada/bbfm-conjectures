import BBFM.Binary.SeriesMask
import BBFM.Binary.LogConcavity.ShiftedProfileMixtures

open PowerSeries Finset
namespace BinaryResearch
noncomputable section

/-- A finite expansion valid for arbitrary real formal series. -/
theorem series_refinement_coeff (L k : ℕ) (F : ℝ⟦X⟧) :
    PowerSeries.coeff k ((1 + X) ^ L * PowerSeries.expand 2 (by omega) F) =
      ∑ j ∈ range (k / 2 + 1), (L.choose (k - 2 * j) : ℝ) * PowerSeries.coeff j F := by
  rw [mul_comm, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_rw [PowerSeries.coeff_expand, series_one_add_X_pow_coeff]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i _ => i / 2) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_filter.mp hi with ⟨hir, hi2⟩
    simp only [mem_range] at hir ⊢
    omega
  · intro i hi j hj he
    rcases mem_filter.mp hi with ⟨hir, hi2⟩
    rcases mem_filter.mp hj with ⟨hjr, hj2⟩
    omega
  · intro j hj
    refine ⟨2 * j, mem_filter.mpr ⟨?_, by omega⟩, ?_⟩
    · simp only [mem_range] at hj ⊢
      omega
    · omega
  · intro i hi
    rcases mem_filter.mp hi with ⟨hir, hi2⟩
    have he : 2 * (i / 2) = i := by omega
    rw [he]
    ring

lemma refinedShiftedSeries_mix (p k : ℕ) (h : ℝ) :
    PowerSeries.coeff k (refinedShiftedSeries p h) =
      BinaryProfileMixtures.mix p (k / 2)
        (fun j => ((p + 1).choose (k - 2 * j) : ℝ)) h := by
  unfold refinedShiftedSeries BinaryProfileMixtures.mix
  rw [series_refinement_coeff]
  simp only [shiftedSeries_coeff]

def flatRefinementCoeff (p k : ℕ) : ℝ :=
  ∑ j ∈ range (k / 2 + 1), ((p + 1).choose (k - 2 * j) : ℝ)

lemma flatRefinementCoeff_positive (p k : ℕ) : 0 < flatRefinementCoeff p k := by
  apply Finset.sum_pos'
  · intro j hj
    positivity
  · refine ⟨k / 2, mem_range.mpr (by omega), ?_⟩
    exact_mod_cast Nat.choose_pos (by omega : k - 2 * (k / 2) ≤ p + 1)

lemma refinedShiftedSeries_positive (p k : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    0 < PowerSeries.coeff k (refinedShiftedSeries p h) := by
  rw [refinedShiftedSeries_mix]
  apply BinaryProfileMixtures.mix_positive
  · intro j hj
    positivity
  · exact flatRefinementCoeff_positive p k
  · exact hh

#print axioms series_refinement_coeff
#print axioms refinedShiftedSeries_positive
end
end BinaryResearch
