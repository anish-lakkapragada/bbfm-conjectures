import BBFM.Denominator.BernoulliSmallMoment
import BBFM.Denominator.LocalDerivatives

/-! New raw third-moment bounds in the exact local derivative sums. -/
noncomputable section
namespace BBFMMoment
open Finset Complex Real DenominatorResearch BBFMRelative BBFMLocal
set_option maxHeartbeats 0

theorem thirdLogSum_sharp_large (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hn : 0<n) (hr : 1/2<r) (hrone : r≤1)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1)≤ m i)
    (hθ : |θ|≤1/(4*effectiveScale n r)) :
    ‖thirdLogSum m n r θ‖ ≤ 6*effectiveScale n r*tiltedVariance m n r := by
  have hh := thirdLogSum_of_factor_bound m n r θ
    (fun i _ hin => factorPhase_third_large n i r θ hn hr hrone hin hθ)
  have hm' := third_moment_sharp_scale m n r hn hr hrone hm
  have hV : 0≤tiltedVariance m n r := by unfold tiltedVariance; positivity
  have hL : 0≤effectiveScale n r := le_trans (by norm_num) (effectiveScale_bounds n r hn hr hrone).1
  nlinarith only [hh,hm',mul_nonneg hL hV]

theorem thirdLogSum_sharp_small (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hr : 0≤r) (hrhalf : r≤1/2)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1)≤ m i) (hθ : |θ|≤1/4) :
    ‖thirdLogSum m n r θ‖ ≤ 8*tiltedVariance m n r := by
  have hh := thirdLogSum_of_factor_bound m n r θ
    (fun i _ _ => factorPhase_third_small r θ i hr hrhalf hθ)
  have hm' := third_moment_sharp_small m n r hr hrhalf hm
  have hV : 0≤tiltedVariance m n r := by unfold tiltedVariance; positivity
  nlinarith only [hh,hm',hV]

#print axioms BBFMMoment.thirdLogSum_sharp_large
#print axioms BBFMMoment.thirdLogSum_sharp_small
end BBFMMoment
