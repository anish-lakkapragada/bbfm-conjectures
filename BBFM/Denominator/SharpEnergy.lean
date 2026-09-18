import BBFM.Denominator.Analytic.EffectiveScale

/-! Middle-frequency sine-energy estimates using a split at pi and a half block. -/

noncomputable section
namespace BBFMRelative
open Finset Real DenominatorResearch
set_option maxHeartbeats 0

theorem sineEnergy_middle_sharp (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) (hqθ : Real.pi ≤ (q : ℝ)*θ)
    (hqθ' : (q : ℝ)*θ ≤ 2*Real.pi) :
    (q : ℝ) ≤ 81*sineEnergy q θ := by
  have hE := sineEnergy_nonneg q θ
  by_cases hq : q ≤ 1
  · have hqone : q = 1 := by
      by_contra hn
      have hz : q = 0 := by omega
      subst q
      norm_num at hqθ
      linarith [Real.pi_pos]
    subst q
    have heq : θ = Real.pi := by norm_num at hqθ; linarith
    subst θ
    norm_num [sineEnergy]
  · let l := q/2
    have hlq : l ≤ q := Nat.div_le_self _ _
    have h2l : (2 : ℝ)*l ≤ q := by exact_mod_cast (show 2*l ≤ q by dsimp [l]; omega)
    have hq3l : (q : ℝ) ≤ 3*l := by exact_mod_cast (show q ≤ 3*l by dsimp [l]; omega)
    have hlθ : (l : ℝ)*θ ≤ Real.pi := by
      have hh := mul_le_mul_of_nonneg_right h2l hθ
      nlinarith
    have hlow := sineEnergy_low l θ hθ hlθ
    have hmono := sineEnergy_mono hlq θ
    have hc : (q : ℝ)^3 ≤ 27*(l : ℝ)^3 := by
      have hh := pow_le_pow_left₀ (show 0 ≤ (q : ℝ) by positivity) hq3l 3
      nlinarith only [hh]
    have hcθ := mul_le_mul_of_nonneg_right hc (sq_nonneg θ)
    have hπq := pow_le_pow_left₀ Real.pi_pos.le hqθ 2
    have hπqq := mul_le_mul_of_nonneg_right hπq (show 0 ≤ (q : ℝ) by positivity)
    have hm := mul_le_mul_of_nonneg_left hmono (show 0 ≤ 3*Real.pi^2 by positivity)
    have hh : Real.pi^2*(q : ℝ) ≤ Real.pi^2*(81*sineEnergy q θ) := by
      nlinarith only [hcθ,hπqq,hlow,hm]
    exact (mul_le_mul_iff_right₀ (sq_pos_of_pos Real.pi_pos)).mp (by nlinarith only [hh])

theorem sineEnergy_bound_sharp_nonneg (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) :
    (q : ℝ)*min 1 ((q : ℝ)^2*θ^2) ≤ 100*sineEnergy q θ := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hE := sineEnergy_nonneg q θ
  by_cases hlow : (q : ℝ)*θ ≤ Real.pi
  · have hh := sineEnergy_low q θ hθ hlow
    have hπ : Real.pi^2 ≤ 16 := by nlinarith [Real.pi_pos,Real.pi_lt_four]
    have hp := mul_le_mul_of_nonneg_right hπ hE
    have hm := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) ((q : ℝ)^2*θ^2)) hq0
    nlinarith only [hh,hp,hm,hE]
  · have hm := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) ((q : ℝ)^2*θ^2)) hq0
    by_cases hhigh : 2*Real.pi ≤ (q : ℝ)*θ
    · have hh := sineEnergy_high q θ hθ hθπ hhigh
      nlinarith only [hh,hm,hE]
    · have hh := sineEnergy_middle_sharp q θ hθ hθπ (by linarith) (by linarith)
      nlinarith only [hh,hm,hE]

theorem sineEnergy_bound_sharp (q : ℕ) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    (q : ℝ)*min 1 ((q : ℝ)^2*θ^2) ≤ 100*sineEnergy q θ := by
  by_cases hθ0 : 0 ≤ θ
  · exact sineEnergy_bound_sharp_nonneg q θ hθ0 (by rwa [abs_of_nonneg hθ0] at hθ)
  · have hh := sineEnergy_bound_sharp_nonneg q (-θ) (by linarith)
      (by rwa [abs_of_neg (by linarith)] at hθ)
    simpa only [neg_sq, sineEnergy_neg] using hh

#print axioms sineEnergy_bound_sharp
end BBFMRelative
