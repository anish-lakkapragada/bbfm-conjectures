import BBFM.Denominator.Analytic.SmallRadiusTaylor
import BBFM.Denominator.Analytic.QuantitativeFourier

noncomputable section
namespace DenominatorResearch
open Finset Complex Real

lemma continuous_centeredDenChar (n k : ℕ) (r : ℝ) : Continuous (centeredDenChar n k r) := by
  unfold centeredDenChar denChar weightedBernoulliChar bernoulliChar
  fun_prop

lemma centeredDenChar_norm (n k : ℕ) (r θ : ℝ) :
    ‖centeredDenChar n k r θ‖ = ‖denChar n r θ‖ := by
  unfold centeredDenChar
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- Complete strict log-concavity theorem at every sufficiently large small-radius saddle.
All Fourier and Taylor hypotheses are discharged for the concrete denominator. -/
theorem den_logconcave_of_small_saddle (n k : ℕ) (r : ℝ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ))
    (hN : (10 : ℝ) ^ 100 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * r) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) < (den n).coeff k ^ 2 := by
  let N : ℝ := ((Nat.log 2 n + 1 : ℕ) : ℝ) * r
  let V : ℝ := tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r
  have hpar := den_small_radius_parameters n r hn hr.le hrhalf
  dsimp only at hpar
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have h1N : 1 ≤ N := le_trans (by norm_num) hN
  apply den_turan_of_centered_fourier_positive n k r hr hk hkd
  apply quantitative_fourier_positive (centeredDenChar n k r) (continuous_centeredDenChar n k r)
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
    have ht := den_small_radius_local_taylor n k r θ hr.le hrhalf hθ.1 hmean
    simpa only [one_pow, mul_one] using ht

end DenominatorResearch
