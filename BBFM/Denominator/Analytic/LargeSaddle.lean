import BBFM.Denominator.Analytic.LargeRadiusTaylor
import BBFM.Denominator.Analytic.SmallSaddle

noncomputable section
namespace DenominatorResearch
open Finset Complex Real

/-- Complete strict Turan inequality at every sufficiently large large-radius saddle.
The radius, profile, variance, Fourier decay, and Taylor remainder are all concrete. -/
theorem den_logconcave_of_large_saddle (n k : ℕ) (r : ℝ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree) (hr : 1 / 2 < r) (hrone : r ≤ 1)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ))
    (hN : (10 : ℝ) ^ 100 ≤
      (1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) * effectiveScale n r) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) < (den n).coeff k ^ 2 := by
  let L := effectiveScale n r
  let M := 1 + Real.logb 2 ((n : ℝ) / L)
  let N := M * L
  let V := tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r
  obtain ⟨hL, hLn, _⟩ := effectiveScale_bounds n r hn hr hrone
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hM : 1 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ) / L := (le_div_iff₀ hL0).2 (by simpa using hLn)
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  have hLN : L ≤ N := by
    dsimp [N]
    simpa using mul_le_mul_of_nonneg_right hM hL0.le
  have hvlo := den_large_radius_variance_lower n r hn hr hrone
  have hvhi := (tiltedVariance_le_moment (fun i => Nat.log 2 (n / i) + 1) n r
    (by linarith)).trans (den_large_radius_moments n r hn hr hrone).1
  change M * L ^ 3 ≤ 576 * V at hvlo
  change V ≤ 20 * M * L ^ 3 at hvhi
  have hV0 : 0 ≤ V := by unfold V tiltedVariance; positivity
  have hp : 0 ≤ M * L ^ 3 := by positivity
  apply den_turan_of_centered_fourier_positive n k r (by linarith) hk hkd
  apply quantitative_fourier_positive (centeredDenChar n k r) (continuous_centeredDenChar n k r)
    N L V hN hL hLN
  · dsimp [N]
    nlinarith
  · dsimp [N]
    nlinarith
  · intro θ
    exact centeredDenChar_even_re n k r θ (by linarith)
  · intro θ hθ
    rw [centeredDenChar_norm]
    simpa only [N, M, L, neg_mul] using denChar_large_radius_decay n r θ hn hr hrone
      (by rw [abs_of_nonneg hθ.1]; exact hθ.2)
  · intro θ hθ
    exact den_large_radius_local_taylor n k r θ hn hr hrone hθ.1 hθ.2 hmean

end DenominatorResearch
