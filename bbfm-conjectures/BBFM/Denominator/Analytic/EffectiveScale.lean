import BBFM.Denominator.Analytic.EffectiveFourier

noncomputable section
namespace DenominatorResearch
open Real

/-- The actual scale chosen by the written large-radius argument, including r=1. -/
def effectiveScale (n : ℕ) (r : ℝ) : ℝ :=
  if r = 1 then n else min (n : ℝ) (1 / (-Real.log r))

theorem effectiveScale_bounds (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) :
    1 ≤ effectiveScale n r ∧ effectiveScale n r ≤ n ∧
      (-Real.log r) * effectiveScale n r ≤ 1 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases heq : r = 1
  · subst r
    simpa [effectiveScale] using hn1
  · have hr0 : 0 < r := by linarith
    have hrlt : r < 1 := lt_of_le_of_ne hrone heq
    have hh0 : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hrlt)
    have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hr0)
    rw [Real.log_inv] at hlog
    have hinv : r⁻¹ < 2 := by
      rw [inv_eq_one_div]
      exact (div_lt_iff₀ hr0).2 (by linarith)
    have hh1 : -Real.log r ≤ 1 := by linarith
    have hrec : (1 : ℝ) ≤ 1 / (-Real.log r) := by
      exact (le_div_iff₀ hh0).2 (by simpa using hh1)
    simp only [effectiveScale, if_neg heq]
    refine ⟨le_min hn1 hrec, min_le_left _ _, ?_⟩
    have hm := mul_le_mul_of_nonneg_left
      (min_le_right (n : ℝ) (1 / (-Real.log r))) hh0.le
    calc
      (-Real.log r) * min (n : ℝ) (1 / (-Real.log r)) ≤
        (-Real.log r) * (1 / (-Real.log r)) := hm
      _ = 1 := by rw [mul_one_div, div_self hh0.ne']

/-- Fully instantiated large-radius Fourier estimate, with no supplied scale or decay bound. -/
theorem denChar_large_radius_decay (n : ℕ) (r θ : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) (hθ : |θ| ≤ Real.pi) :
    ‖denChar n r θ‖ ≤ Real.exp
      (-(1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) * effectiveScale n r /
        100000000 * min 1 ((effectiveScale n r) ^ 2 * θ ^ 2)) := by
  obtain ⟨hL, hLn, hs⟩ := effectiveScale_bounds n r hn hr hrone
  exact denChar_effective_decay n r (effectiveScale n r) θ
    (by linarith) hrone hL hLn hs hθ

/-- Fully instantiated large-radius variance lower bound for the concrete polynomial. -/
theorem den_large_radius_variance_lower (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) :
    (1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) * (effectiveScale n r) ^ 3 ≤
      576 * tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r := by
  obtain ⟨hL, hLn, hs⟩ := effectiveScale_bounds n r hn hr hrone
  have hr0 : 0 < r := by linarith
  apply den_effective_variance_lower n r (effectiveScale n r) hL hLn hr0.le hrone
  exact radius_floor_pow_lower r (effectiveScale n r) hr0 hrone (by linarith) hs

end DenominatorResearch
