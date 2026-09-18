import BBFM.Denominator.Analytic.LargeSaddle
import BBFM.Denominator.LocalVariance
import BBFM.Denominator.MomentCriterion
import BBFM.Denominator.MomentTaylor
import BBFM.Denominator.LocalDecay

/-! Source saddle bounds for the third-moment criterion. At small radii
the criterion uses N = 14 * m1 * r and L = 4/3. -/

noncomputable section
namespace BBFMMoment
open Finset Complex Real DenominatorResearch BBFMRelative

/-- Complete strict log-concavity theorem at every sufficiently large small-radius saddle.
All Fourier and Taylor hypotheses are discharged for the concrete denominator. -/
theorem den_logconcave_of_small_saddle (n k : ℕ) (r : ℝ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree) (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ))
    (hN : 12*(10 : ℝ) ^ 6 ≤ 14*(((Nat.log 2 n + 1 : ℕ) : ℝ) * r)) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) < (den n).coeff k ^ 2 := by
  let N : ℝ := ((Nat.log 2 n + 1 : ℕ) : ℝ) * r
  let V : ℝ := tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r
  have hpar := den_small_radius_parameters n r hn hr.le hrhalf
  dsimp only at hpar
  have hN0 : 0 ≤ N := by dsimp [N]; positivity
  have h1N : (4/3 : ℝ) ≤ 14*N := le_trans (by norm_num) hN
  apply den_turan_of_centered_fourier_positive n k r hr hk hkd
  apply BBFMMoment.quantitative_fourier_positive (centeredDenChar n k r) (continuous_centeredDenChar n k r)
    (14*N) (4/3) V hN (by norm_num) h1N
  · dsimp [N, V]
    nlinarith [hpar.2.1]
  · dsimp [N, V]
    nlinarith [hpar.2.2]
  · intro θ
    exact centeredDenChar_even_re n k r θ hr.le
  · intro θ hθ
    have hθabs : |θ| ≤ Real.pi := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    rw [centeredDenChar_norm]
    have hd := BBFMRelative.denChar_unit_decay n r θ hn hr.le (by linarith) hθabs
    apply hd.trans
    apply Real.exp_le_exp.mpr
    rw [neg_mul]
    change -N/200*min 1 (θ^2) ≤ -(14*N)/5000*min 1 ((4/3 : ℝ)^2*θ^2)
    have hmin0 : 0 ≤ min (1 : ℝ) (θ^2) := le_min (by norm_num) (sq_nonneg _)
    have hmin : min (1 : ℝ) ((4/3 : ℝ)^2*θ^2) ≤ (16/9 : ℝ)*min 1 (θ^2) := by
      by_cases hθ1 : θ^2 ≤ 1
      · rw [min_eq_right hθ1]
        norm_num
      · rw [min_eq_left (le_of_not_ge hθ1)]
        exact (min_le_left _ _).trans (by norm_num)
    have hp := mul_le_mul_of_nonneg_left hmin hN0
    have hq := mul_nonneg hN0 hmin0
    nlinarith only [hp,hq]
  · intro θ hθ
    have ht := den_small_radius_sharp_taylor n k r θ hr.le hrhalf hθ.1
      (by norm_num at hθ; linarith) hmean
    obtain ⟨R,hR,hb⟩ := ht
    refine ⟨R,hR,?_⟩
    dsimp [V]
    nlinarith only [hb]



/-- Complete strict Turan inequality at every sufficiently large large-radius saddle.
The radius, profile, variance, Fourier decay, and Taylor remainder are all concrete. -/
theorem den_logconcave_of_large_saddle (n k : ℕ) (r : ℝ) (hn : 0 < n)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree) (hr : 1 / 2 < r) (hrone : r ≤ 1)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ))
    (hN : 12*(10 : ℝ) ^ 6 ≤
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
  have hvlo := BBFMLocal.den_large_radius_variance_lower n r hn hr hrone
  have hvhi := (tiltedVariance_le_moment (fun i => Nat.log 2 (n / i) + 1) n r
    (by linarith)).trans (den_large_radius_moments n r hn hr hrone).1
  change M * L ^ 3 ≤ 100 * V at hvlo
  change V ≤ 20 * M * L ^ 3 at hvhi
  have hV0 : 0 ≤ V := by unfold V tiltedVariance; positivity
  have hp : 0 ≤ M * L ^ 3 := by positivity
  apply den_turan_of_centered_fourier_positive n k r (by linarith) hk hkd
  apply BBFMMoment.quantitative_fourier_positive (centeredDenChar n k r) (continuous_centeredDenChar n k r)
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
    simpa only [N, M, L, neg_mul] using BBFMLocal.denChar_effective_decay
      n r (effectiveScale n r) θ (by linarith) hrone hL hLn hscale
      (by rw [abs_of_nonneg hθ.1]; exact hθ.2)
  · intro θ hθ
    exact den_large_radius_sharp_taylor n k r θ hn hr hrone hθ.1 hθ.2 hmean


#print axioms BBFMMoment.den_logconcave_of_small_saddle
#print axioms BBFMMoment.den_logconcave_of_large_saddle
end BBFMMoment
