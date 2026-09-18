import BBFM.Denominator.VarianceMoment

noncomputable section
namespace BBFMRelative
open Finset Complex Real DenominatorResearch
set_option maxHeartbeats 0

/-- Third logarithmic-derivative estimate in terms of its finite moment. -/
theorem thirdLogSum_moment_bound (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrone : r ≤ 1)
    (hd : ∀ i, 1 ≤ i → i ≤ n → 1/2 ≤ ‖1+factorPhase r θ i‖) :
    ‖thirdLogSum m n r θ‖ ≤ 16*weightedMoment m n 3 r := by
  unfold thirdLogSum weightedMoment
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hratio := thirdLogRatio_norm_bound (factorPhase r θ (i+1))
    (by rw [factorPhase_norm r θ (i+1) hr]; exact pow_le_one₀ hr hrone)
    (hd (i+1) (by omega) (by have := mem_range.mp hi; omega))
  rw [factorPhase_norm r θ (i+1) hr] at hratio
  simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ (m (i+1) : ℝ)*((i+1 : ℕ) : ℝ)^3 by positivity)
  push_cast at hh ⊢
  nlinarith only [hh]

theorem thirdLogSum_relative_large (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hn : 0 < n) (hr : 1/2 < r) (hrone : r ≤ 1)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i)
    (hθ : |θ| ≤ 1/(4*effectiveScale n r)) :
    ‖thirdLogSum m n r θ‖ ≤ 384*effectiveScale n r*tiltedVariance m n r := by
  have hh := thirdLogSum_moment_bound m n r θ (by linarith) hrone
    (fun i hi hin => (factorPhase_large_local n i r θ hn hr hrone hi hin hθ).2)
  have hm' := third_moment_le_scale_variance m n r hn hr hrone hm
  nlinarith only [hh,hm']

theorem thirdLogSum_relative_small (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1/2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i) :
    ‖thirdLogSum m n r θ‖ ≤ 384*tiltedVariance m n r := by
  have hh := thirdLogSum_moment_bound m n r θ hr (by linarith) (by
    intro i hi hin
    have hp : r^i ≤ 1/2 :=
      (pow_le_of_le_one hr (by linarith) (by omega)).trans hrhalf
    have hz : ‖factorPhase r θ i‖ ≤ 1/2 := by rw [factorPhase_norm r θ i hr]; exact hp
    have hs := norm_sub_norm_le (1 : ℂ) (-factorPhase r θ i)
    simp only [norm_one,norm_neg,sub_neg_eq_add] at hs
    linarith)
  have hm' := third_moment_le_variance_small m n r hr hrhalf hm
  nlinarith only [hh,hm']

#print axioms thirdLogSum_relative_large
#print axioms thirdLogSum_relative_small
end BBFMRelative
