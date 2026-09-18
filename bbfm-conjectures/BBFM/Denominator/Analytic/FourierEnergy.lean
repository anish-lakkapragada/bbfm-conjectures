import Mathlib

noncomputable section
namespace DenominatorResearch
open Finset Real

/-- Energy supplied by a consecutive block of Bernoulli weights. -/
def sineEnergy (q : ℕ) (θ : ℝ) : ℝ :=
  ∑ i ∈ range q, Real.sin (((i : ℝ) + 1) * θ / 2) ^ 2

lemma sineEnergy_nonneg (q : ℕ) (θ : ℝ) : 0 ≤ sineEnergy q θ := by
  exact sum_nonneg fun i _ => sq_nonneg _

lemma sineEnergy_mono {l q : ℕ} (hlq : l ≤ q) (θ : ℝ) : sineEnergy l θ ≤ sineEnergy q θ := by
  exact sum_le_sum_of_subset_of_nonneg (range_mono hlq) (fun i _ _ => sq_nonneg _)

lemma sum_successor_sq_lower (q : ℕ) :
    (q : ℝ) ^ 3 ≤ 3 * ∑ i ∈ range q, ((i : ℝ) + 1) ^ 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ]
    push_cast
    nlinarith [show (0 : ℝ) ≤ q by positivity]

lemma sineEnergy_low (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : (q : ℝ) * θ ≤ Real.pi) :
    (q : ℝ) ^ 3 * θ ^ 2 ≤ 3 * Real.pi ^ 2 * sineEnergy q θ := by
  have hsum : (∑ i ∈ range q, ((i : ℝ) + 1) ^ 2 * θ ^ 2) ≤
      ∑ i ∈ range q, Real.pi ^ 2 * Real.sin (((i : ℝ) + 1) * θ / 2) ^ 2 := by
    apply sum_le_sum
    intro i hi
    have hiq : (i : ℝ) + 1 ≤ q := by exact_mod_cast (mem_range.mp hi)
    have hi0 : 0 ≤ (i : ℝ) + 1 := by positivity
    have hx0 : 0 ≤ ((i : ℝ) + 1) * θ / 2 := by positivity
    have hxπ : ((i : ℝ) + 1) * θ / 2 ≤ Real.pi / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hiq hθ]
    have hJ := Real.mul_le_sin hx0 hxπ
    have hJ' : ((i : ℝ) + 1) * θ ≤ Real.pi * Real.sin (((i : ℝ) + 1) * θ / 2) := by
      have := mul_le_mul_of_nonneg_left hJ Real.pi_pos.le
      field_simp at this
      nlinarith [this]
    have hs0 := Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith :
      ((i : ℝ) + 1) * θ / 2 ≤ Real.pi)
    have hsquare := (sq_le_sq₀ (mul_nonneg hi0 hθ) (mul_nonneg Real.pi_pos.le hs0)).2 hJ'
    nlinarith [hsquare]
  rw [← sum_mul, ← mul_sum] at hsum
  have hpow := mul_le_mul_of_nonneg_right (sum_successor_sq_lower q) (sq_nonneg θ)
  unfold sineEnergy
  nlinarith [hsum, hpow]

lemma sineEnergy_cos_identity (q : ℕ) (θ : ℝ) :
    2 * sineEnergy q θ = (q : ℝ) - ∑ i ∈ range q, Real.cos (θ * i + θ) := by
  unfold sineEnergy
  rw [mul_sum]
  have hid : (q : ℝ) = ∑ _i ∈ range q, (1 : ℝ) := by simp
  rw [hid, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  have h := Real.sin_sq_eq_half_sub (((i : ℝ) + 1) * θ / 2)
  have heq : 2 * (((i : ℝ) + 1) * θ / 2) = θ * i + θ := by ring
  rw [heq] at h
  linarith

lemma sineEnergy_high (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hqθ : 2 * Real.pi ≤ (q : ℝ) * θ) :
    (q : ℝ) / 4 ≤ sineEnergy q θ := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hθpos : 0 < θ := by nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hJ := Real.mul_le_sin (by linarith : 0 ≤ θ / 2) (by linarith : θ / 2 ≤ Real.pi / 2)
  have hJ' : θ ≤ Real.pi * Real.sin (θ / 2) := by
    have := mul_le_mul_of_nonneg_left hJ Real.pi_pos.le
    field_simp at this
    nlinarith
  have hqsin : 2 ≤ (q : ℝ) * Real.sin (θ / 2) := by
    have hh := mul_le_mul_of_nonneg_left hJ' hq0
    nlinarith [hh, Real.pi_pos]
  have hprod : Real.sin (θ / 2) * (∑ i ∈ range q, Real.cos (θ * i + θ)) ≤ 1 := by
    rw [Real.sin_mul_sum_cos]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
        (abs_nonneg _) (by norm_num)).trans (by norm_num))
  have hcos : (∑ i ∈ range q, Real.cos (θ * i + θ)) ≤ (q : ℝ) / 2 := by
    apply (mul_le_mul_iff_right₀ hsinpos).mp
    nlinarith [hprod, hqsin]
  have := sineEnergy_cos_identity q θ
  nlinarith


lemma sineEnergy_middle (q : ℕ) (hq : 1 ≤ q) (θ : ℝ) (hθ : 0 ≤ θ)
    (hθπ : θ ≤ Real.pi) (hqθ : 1 ≤ (q : ℝ) * θ)
    (hqθ' : (q : ℝ) * θ ≤ 2 * Real.pi) :
    (q : ℝ) ≤ 100000 * sineEnergy q θ := by
  have hE := sineEnergy_nonneg q θ
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hπ2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have hqsq : 1 ≤ (q : ℝ) ^ 2 * θ ^ 2 := by nlinarith [sq_nonneg ((q : ℝ) * θ - 1)]
  have hqcube : (q : ℝ) ≤ (q : ℝ) ^ 3 * θ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hqsq hq0
    nlinarith
  by_cases hq8 : 8 ≤ q
  · let l := q / 4
    have hlq : l ≤ q := Nat.div_le_self _ _
    have h4l : (4 : ℝ) * l ≤ q := by exact_mod_cast (show 4 * l ≤ q by dsimp [l]; omega)
    have hq8l : (q : ℝ) ≤ 8 * l := by exact_mod_cast (show q ≤ 8 * l by dsimp [l]; omega)
    have hl0 : 0 ≤ (l : ℝ) := by positivity
    have hlθ : (l : ℝ) * θ ≤ Real.pi := by
      have := mul_le_mul_of_nonneg_right h4l hθ
      nlinarith
    have hlow := sineEnergy_low l θ hθ hlθ
    have hmono := sineEnergy_mono hlq θ
    have hc : (q : ℝ) ^ 3 ≤ 512 * (l : ℝ) ^ 3 := by
      have := pow_le_pow_left₀ hq0 hq8l 3
      nlinarith
    have hcθ := mul_le_mul_of_nonneg_right hc (sq_nonneg θ)
    have hm := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 3 * Real.pi ^ 2)
    have hp := mul_le_mul_of_nonneg_right hπ2 hE
    nlinarith [hqcube, hcθ, hlow, hm, hp]
  · have hq7 : (q : ℝ) ≤ 7 := by exact_mod_cast (show q ≤ 7 by omega)
    have hc : (q : ℝ) ^ 3 ≤ 343 := by
      have := pow_le_pow_left₀ hq0 hq7 3
      norm_num at this
      exact this
    have hcθ := mul_le_mul_of_nonneg_right hc (sq_nonneg θ)
    have hlow := sineEnergy_low 1 θ hθ (by simpa using hθπ)
    have hmono := sineEnergy_mono hq θ
    have hm := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 3 * Real.pi ^ 2)
    have hp := mul_le_mul_of_nonneg_right hπ2 hE
    norm_num at hlow
    nlinarith [hqcube, hcθ, hlow, hm, hp]

/-- A uniform explicit lower bound for the Fourier energy of consecutive weights.
This is one of the unconditional analytic ingredients used in the written eventual proof. -/
theorem sineEnergy_bound_nonneg (q : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    (q : ℝ) * min 1 ((q : ℝ) ^ 2 * θ ^ 2) ≤ 100000 * sineEnergy q θ := by
  by_cases hq : q = 0
  · subst q; simp [sineEnergy]
  have hq1 : 1 ≤ q := by omega
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hE := sineEnergy_nonneg q θ
  have hπ2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  by_cases hsmall : (q : ℝ) * θ ≤ 1
  · have hlow := sineEnergy_low q θ hθ (by linarith [Real.two_le_pi])
    have hp := mul_le_mul_of_nonneg_right hπ2 hE
    have hmin := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) ((q : ℝ) ^ 2 * θ ^ 2)) hq0
    nlinarith
  · have hbig : 1 ≤ (q : ℝ) * θ := by linarith
    have hmin := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) ((q : ℝ) ^ 2 * θ ^ 2)) hq0
    by_cases hhigh : 2 * Real.pi ≤ (q : ℝ) * θ
    · have hh := sineEnergy_high q θ hθ hθπ hhigh
      nlinarith
    · exact hmin.trans (by simpa using sineEnergy_middle q hq1 θ hθ hθπ hbig (by linarith))

lemma sineEnergy_neg (q : ℕ) (θ : ℝ) : sineEnergy q (-θ) = sineEnergy q θ := by
  unfold sineEnergy
  apply sum_congr rfl
  intro i _
  rw [mul_neg, neg_div, Real.sin_neg]
  ring

theorem sineEnergy_bound (q : ℕ) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    (q : ℝ) * min 1 ((q : ℝ) ^ 2 * θ ^ 2) ≤ 100000 * sineEnergy q θ := by
  by_cases hθ0 : 0 ≤ θ
  · exact sineEnergy_bound_nonneg q θ hθ0 (by rwa [abs_of_nonneg hθ0] at hθ)
  · have hh := sineEnergy_bound_nonneg q (-θ) (by linarith) (by rwa [abs_of_neg (by linarith)] at hθ)
    simpa only [neg_sq, sineEnergy_neg] using hh

end DenominatorResearch
