import BBFM.Denominator.LocalThirdRatio

noncomputable section
namespace BBFMLocal
open Finset Complex Real DenominatorResearch BBFMRelative
set_option maxHeartbeats 0

lemma thirdLogSum_of_factor_bound (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hfactor : ∀ i, 1 ≤ i → i ≤ n →
      ‖thirdLogRatio (factorPhase r θ i)‖ ≤ (4/3 : ℝ)*r^i) :
    ‖thirdLogSum m n r θ‖ ≤ (4/3 : ℝ)*weightedMoment m n 3 r := by
  unfold thirdLogSum weightedMoment
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hh := hfactor (i+1) (by omega) (by have := mem_range.mp hi; omega)
  simp only [norm_mul,norm_pow,Complex.norm_I,one_mul,Complex.norm_natCast]
  have hp := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (m (i+1) : ℝ)*((i+1 : ℕ) : ℝ)^3 by positivity)
  push_cast at hp ⊢
  nlinarith only [hp]

theorem thirdLogSum_relative_large (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hn : 0<n) (hr : 1/2<r) (hrone : r≤1)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1)≤ m i)
    (hθ : |θ|≤1/(4*effectiveScale n r)) :
    ‖thirdLogSum m n r θ‖ ≤ 36*effectiveScale n r*tiltedVariance m n r := by
  have hh := thirdLogSum_of_factor_bound m n r θ
    (fun i _ hin => factorPhase_third_large n i r θ hn hr hrone hin hθ)
  have hm' := third_moment_le_scale_variance m n r hn hr hrone hm
  have hV : 0≤tiltedVariance m n r := by unfold tiltedVariance; positivity
  have hL : 0≤effectiveScale n r := le_trans (by norm_num) (effectiveScale_bounds n r hn hr hrone).1
  nlinarith only [hh,hm',mul_nonneg hL hV]

theorem thirdLogSum_relative_small (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hr : 0≤r) (hrhalf : r≤1/2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1)≤ m i) (hθ : |θ|≤1/4) :
    ‖thirdLogSum m n r θ‖ ≤ 36*tiltedVariance m n r := by
  have hh := thirdLogSum_of_factor_bound m n r θ
    (fun i _ _ => factorPhase_third_small r θ i hr hrhalf hθ)
  have hm' := third_moment_le_variance_small m n r hr hrhalf hm
  have hV : 0≤tiltedVariance m n r := by unfold tiltedVariance; positivity
  nlinarith only [hh,hm',hV]

#print axioms BBFMLocal.thirdLogSum_relative_large
#print axioms BBFMLocal.thirdLogSum_relative_small
end BBFMLocal
