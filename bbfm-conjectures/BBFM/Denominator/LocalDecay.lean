import BBFM.Denominator.SharpDecay

/-! Credited refinement of SharpDecay: the exact variance minimum3/16
on [1/3,1] improves the effective decay denominator10000 to5000. -/
noncomputable section
namespace BBFMLocal
open Finset Real DenominatorResearch BBFMRelative
set_option maxHeartbeats 0

/-- A radius-adapted consecutive block yields decay for the actual denominator. -/
theorem denChar_block_decay (n q : ℕ) (r θ : ℝ) (hq : q ≤ n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hrq : 1 / 3 ≤ r ^ q) (hθ : |θ| ≤ Real.pi) :
    ‖denChar n r θ‖ ≤ Real.exp
      (-3*((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * (q : ℝ) / 800 *
        min 1 ((q : ℝ) ^ 2 * θ ^ 2)) := by
  have hblock : ∀ i, 1 ≤ i → i ≤ q →
      3*((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) / 16 ≤
        ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) * tiltedProbability r i *
          (1 - tiltedProbability r i) := by
    intro i hi hiq
    have hri : 1 / 3 ≤ r ^ i := hrq.trans (pow_le_pow_of_le_one hr hrone hiq)
    have hri1 : r ^ i ≤ 1 := by exact pow_le_one₀ hr hrone
    have hvar : 3 / 16 ≤ tiltedProbability r i * (1 - tiltedProbability r i) := by
      rw [tiltedProbability_variance r i hr]
      apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + r ^ i))).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hri) (show 0 ≤ 3-r^i by linarith)]
    have hm : ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) ≤
        ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) := by
      exact_mod_cast den_multiplicity_antitone n i q hi hiq
    have hh := mul_le_mul_of_nonneg_left hvar
      (show 0 ≤ ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) by positivity)
    nlinarith
  have h := BBFMRelative.weightedBernoulliChar_decay (fun i => Nat.log 2 (n / i) + 1)
    (tiltedProbability r) n q θ (3*((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) / 16)
    hq (by positivity) hθ (fun i _ _ => tiltedProbability_range r i hr) hblock
  convert h using 1
  congr 1
  ring
/-- The complete large-radius Fourier norm estimate for the actual denominator profile.
The scale condition is exactly the one satisfied by min(n,1/(-log r)). -/
theorem denChar_effective_decay (n : ℕ) (r L θ : ℝ) (hr : 0 < r) (hrone : r ≤ 1)
    (hL : 1 ≤ L) (hLn : L ≤ n) (hscale : (-Real.log r) * L ≤ 1)
    (hθ : |θ| ≤ Real.pi) :
    ‖denChar n r θ‖ ≤ Real.exp
      (-(1 + Real.logb 2 ((n : ℝ) / L)) * L / 5000 * min 1 (L ^ 2 * θ ^ 2)) := by
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
  change -3*((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * (q : ℝ) / 800 *
      min 1 ((q : ℝ) ^ 2 * θ ^ 2) ≤ -M * L / 5000 * min 1 (L ^ 2 * θ ^ 2)
  have hpos := mul_nonneg (mul_nonneg hM0 hL0) hA0
  nlinarith

#print axioms BBFMLocal.denChar_effective_decay
end BBFMLocal
