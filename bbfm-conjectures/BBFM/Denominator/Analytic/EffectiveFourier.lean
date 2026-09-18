import BBFM.Denominator.Analytic.EffectiveVariance

noncomputable section
namespace DenominatorResearch
open Real

/-- The complete large-radius Fourier norm estimate for the actual denominator profile.
The scale condition is exactly the one satisfied by min(n,1/(-log r)). -/
theorem denChar_effective_decay (n : ℕ) (r L θ : ℝ) (hr : 0 < r) (hrone : r ≤ 1)
    (hL : 1 ≤ L) (hLn : L ≤ n) (hscale : (-Real.log r) * L ≤ 1)
    (hθ : |θ| ≤ Real.pi) :
    ‖denChar n r θ‖ ≤ Real.exp
      (-(1 + Real.logb 2 ((n : ℝ) / L)) * L / 100000000 * min 1 (L ^ 2 * θ ^ 2)) := by
  let q := ⌊L⌋₊
  let M := 1 + Real.logb 2 ((n : ℝ) / L)
  have hL0 : 0 ≤ L := by linarith
  have hqL : (q : ℝ) ≤ L := Nat.floor_le hL0
  have hqn : q ≤ n := by exact_mod_cast hqL.trans hLn
  have hq1 : 1 ≤ q := (Nat.one_le_floor_iff L).2 hL
  have hqhalf : L / 2 ≤ (q : ℝ) := floor_ge_half L hL
  have hrq : 1 / 3 ≤ r ^ q := radius_floor_pow_lower r L hr hrone hL0 hscale
  have hdec := denChar_block_decay n q r θ hqn hr.le hrone hrq hθ
  have hm := den_profile_lower n q L hq1 hqn hL hqL
  have hm0 : 0 ≤ ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) := by positivity
  have hM0 : 0 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ) / L := by
      apply (le_div_iff₀ (by linarith : 0 < L)).2
      simpa only [one_mul] using hLn
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  have hcoeff : M * L / 4 ≤ ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * q := by
    have hh := mul_le_mul hm hqhalf (by positivity : (0 : ℝ) ≤ L / 2) hm0
    change M / 2 * (L / 2) ≤ _ at hh
    nlinarith
  have hA0 : 0 ≤ min (1 : ℝ) (L ^ 2 * θ ^ 2) := le_min (by norm_num) (by positivity)
  have hmin : min (1 : ℝ) (L ^ 2 * θ ^ 2) / 4 ≤ min 1 ((q : ℝ) ^ 2 * θ ^ 2) := by
    apply le_min
    · have hh := min_le_left (1 : ℝ) (L ^ 2 * θ ^ 2)
      linarith
    · have hh := min_le_right (1 : ℝ) (L ^ 2 * θ ^ 2)
      have hq2 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ L / 2) hqhalf 2
      have hp := mul_le_mul_of_nonneg_right hq2 (sq_nonneg θ)
      nlinarith
  have hprod := mul_le_mul hcoeff hmin (by positivity : (0 : ℝ) ≤ min 1 (L ^ 2 * θ ^ 2) / 4)
    (show 0 ≤ ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * (q : ℝ) by positivity)
  apply hdec.trans
  apply Real.exp_le_exp.mpr
  change -((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * (q : ℝ) / 600000 *
      min 1 ((q : ℝ) ^ 2 * θ ^ 2) ≤ -M * L / 100000000 * min 1 (L ^ 2 * θ ^ 2)
  have hpos := mul_nonneg (mul_nonneg hM0 hL0) hA0
  nlinarith

end DenominatorResearch
