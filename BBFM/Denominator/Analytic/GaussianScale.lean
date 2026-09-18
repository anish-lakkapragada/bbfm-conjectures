import BBFM.Denominator.Analytic.LocalCentral

noncomputable section
namespace DenominatorResearch
open Real

lemma variance_positive (N L V : ℝ) (hN : (10 : ℝ) ^ 100 ≤ N)
    (hL : 1 ≤ L) (hV : N * L ^ 2 / 1000 ≤ V) : 0 < V := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hL0 : 0 < L := by linarith
  exact lt_of_lt_of_le (by positivity) hV

lemma variance_sqrt_large (N L V : ℝ) (hN : (10 : ℝ) ^ 100 ≤ N)
    (hL : 1 ≤ L) (hV : N * L ^ 2 / 1000 ≤ V) :
    1000000000 * L ≤ Real.sqrt V := by
  have hV0 := variance_positive N L V hN hL hV
  have hN' : (1000000000000000000000 : ℝ) ≤ N := le_trans (by norm_num) hN
  have hh := mul_le_mul_of_nonneg_right hN' (sq_nonneg L)
  apply (Real.le_sqrt (by positivity) hV0.le).2
  nlinarith

/-- The explicit threshold makes the entire local cubic remainder small. -/
theorem cubic_remainder_small (N L V θ : ℝ) (hN : (10 : ℝ) ^ 100 ≤ N)
    (hL : 1 ≤ L) (hV : N * L ^ 2 / 1000 ≤ V)
    (hθ : 0 ≤ θ) (hθmax : θ ≤ 100000000 / Real.sqrt V) :
    10000 * N * L ^ 3 * θ ^ 3 ≤ 1 / 10 := by
  have hV0 := variance_positive N L V hN hL hV
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hL0 : 0 ≤ L := by linarith
  have hN0 : 0 ≤ N := le_trans (by positivity) hN
  have hmul := (le_div_iff₀ hs0).1 hθmax
  have hsquare := pow_le_pow_left₀ (mul_nonneg hθ hs0.le) hmul 2
  rw [mul_pow, Real.sq_sqrt hV0.le] at hsquare
  have hvθ := mul_le_mul_of_nonneg_right hV (sq_nonneg θ)
  have hu : N * (L * θ) ^ 2 ≤ 10000000000000000000 := by nlinarith
  have hu0 : 0 ≤ L * θ := mul_nonneg hL0 hθ
  have huSmall : L * θ ≤ 1 / (10 : ℝ) ^ 30 := by
    by_contra h
    have huLower : 1 / (10 : ℝ) ^ 30 ≤ L * θ := le_of_lt (lt_of_not_ge h)
    have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (10 : ℝ) ^ 30) huLower 2
    have hh := mul_le_mul_of_nonneg_right hN (sq_nonneg (L * θ))
    norm_num at hs hh
    nlinarith
  have hh := mul_le_mul hu huSmall hu0 (by norm_num : (0 : ℝ) ≤ 10000000000000000000)
  calc
    10000 * N * L ^ 3 * θ ^ 3 = 10000 * (N * (L * θ) ^ 2 * (L * θ)) := by ring
    _ ≤ 10000 * (10000000000000000000 * (1 / (10 : ℝ) ^ 30)) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ ≤ 1 / 10 := by norm_num

/-- The exponential far tail is uniformly smaller than the cubic central scale.
An eighth-order exponential bound avoids fractional-power arithmetic. -/
theorem far_tail_small (N V : ℝ) (hN : (10 : ℝ) ^ 100 ≤ N)
    (hV0 : 0 < V) (hV : V ≤ 100 * N ^ 3) :
    Real.exp (-N / 100000000) ≤ (1 / Real.sqrt V) ^ 3 / 10000 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : 0 ≤ N := by linarith
  have hNN := mul_le_mul_of_nonneg_right hN1 (pow_nonneg hN0 3)
  have hsupper : Real.sqrt V ≤ 10 * N ^ 2 := by
    have hsq := Real.sq_sqrt hV0.le
    have hs0 := Real.sqrt_nonneg V
    have hN2 := sq_nonneg N
    nlinarith
  have hcube := pow_le_pow_left₀ (Real.sqrt_nonneg V) hsupper 3
  have hcube' : (Real.sqrt V) ^ 3 ≤ 1000 * N ^ 6 := by nlinarith
  let E : ℝ := 40320 * (100000000 : ℝ) ^ 8
  have hE0 : 0 < E := by norm_num [E]
  have hpowN := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (10 : ℝ) ^ 100) hN 2
  have hN2 : E * 10000000 ≤ N ^ 2 := by norm_num [E] at hpowN ⊢; linarith
  have hprod := mul_le_mul_of_nonneg_right hN2 (pow_nonneg hN0 6)
  have hfrac : 10000000 * N ^ 6 ≤ N ^ 8 / E := by
    apply (le_div_iff₀ hE0).2
    nlinarith
  have he := Real.pow_div_factorial_le_exp (N / 100000000) (by positivity) 8
  have he' : N ^ 8 / E ≤ Real.exp (N / 100000000) := by
    convert he using 1 <;> norm_num [E, div_pow] <;> ring
  have hfinal : 10000 * (Real.sqrt V) ^ 3 ≤ Real.exp (N / 100000000) := by
    have hh := hfrac.trans he'
    linarith
  have hspos : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hright : (1 / Real.sqrt V) ^ 3 / 10000 = 1 / (10000 * (Real.sqrt V) ^ 3) := by
    field_simp
  rw [hright, show -N / 100000000 = -(N / 100000000) by ring, Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
  simpa using hfinal

end DenominatorResearch
