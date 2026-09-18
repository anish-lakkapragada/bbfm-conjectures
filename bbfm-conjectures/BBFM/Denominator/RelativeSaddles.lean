import BBFM.Denominator.Analytic.LargeSaddle
import BBFM.Denominator.RelativeCriterion
import BBFM.Denominator.RelativeTaylor
import BBFM.Denominator.SharpDecay

/-! Small- and large-radius saddle bounds using variance-relative Taylor
remainders, block decay, and the effective-size 10^13 Fourier criterion. -/
noncomputable section
namespace BBFMRelative
open Finset Complex Real DenominatorResearch

/-- Complete strict log-concavity theorem at every sufficiently large small-radius saddle.
All Fourier and Taylor hypotheses are discharged for the concrete denominator. -/
theorem den_logconcave_of_small_saddle (n k : ℕ) (r : ℝ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ))
    (hN : (10 : ℝ) ^ 13 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * r) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) < (den n).coeff k ^ 2 := by
  let N : ℝ := ((Nat.log 2 n + 1 : ℕ) : ℝ) * r
  let V : ℝ := tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r
  have hpar := den_small_radius_parameters n r hn hr.le hrhalf
  dsimp only at hpar
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have h1N : 1 ≤ N := le_trans (by norm_num) hN
  apply den_turan_of_centered_fourier_positive n k r hr hk hkd
  apply BBFMRelative.quantitative_fourier_positive (centeredDenChar n k r) (continuous_centeredDenChar n k r)
    N 1 V hN (by norm_num) h1N
  · dsimp [N, V]
    nlinarith [hpar.2.1]
  · dsimp [N, V]
    nlinarith [hpar.2.2]
  · intro θ
    exact centeredDenChar_even_re n k r θ hr.le
  · intro θ hθ
    have hθabs : |θ| ≤ Real.pi := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    rw [centeredDenChar_norm]
    have hd := denChar_unit_decay n r θ hn hr.le (by linarith) hθabs
    apply hd.trans
    apply Real.exp_le_exp.mpr
    dsimp [N]
    norm_num
    have hmin : 0 ≤ min (1 : ℝ) (θ ^ 2) := le_min (by norm_num) (sq_nonneg _)
    have hh := mul_nonneg (show 0 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * r by positivity) hmin
    push_cast at hh
    nlinarith
  · intro θ hθ
    have ht := den_small_radius_relative_taylor n k r θ hr.le hrhalf hθ.1 hmean
    simpa only [one_pow, mul_one] using ht


/-- Complete strict Turan inequality at every sufficiently large large-radius saddle.
The radius, profile, variance, Fourier decay, and Taylor remainder are all concrete. -/
theorem den_logconcave_of_large_saddle (n k : ℕ) (r : ℝ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree) (hr : 1 / 2 < r) (hrone : r ≤ 1)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ))
    (hN : (10 : ℝ) ^ 13 ≤
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
  apply BBFMRelative.quantitative_fourier_positive (centeredDenChar n k r) (continuous_centeredDenChar n k r)
    N L V hN hL hLN
  · dsimp [N]
    nlinarith
  · dsimp [N]
    nlinarith
  · intro θ
    exact centeredDenChar_even_re n k r θ (by linarith)
  · intro θ hθ
    rw [centeredDenChar_norm]
    have hscale := (effectiveScale_bounds n r hn hr hrone).2.2
    simpa only [N, M, L, neg_mul] using BBFMRelative.denChar_effective_decay
      n r (effectiveScale n r) θ (by linarith) hrone hL hLn hscale
      (by rw [abs_of_nonneg hθ.1]; exact hθ.2)
  · intro θ hθ
    exact den_large_radius_relative_taylor n k r θ hn hr hrone hθ.1 hθ.2 hmean


#print axioms den_logconcave_of_small_saddle
#print axioms den_logconcave_of_large_saddle
end BBFMRelative
