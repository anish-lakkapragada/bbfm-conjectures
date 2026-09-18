import BBFM.Denominator.SharpGaussian

/-! Credited refinement of RelativeScale using cubic coefficient6 and
local radius1/(24L). New effective-size threshold is4·10^8. -/

noncomputable section
namespace BBFMLocal
open Real

lemma variance_positive (N L V : ℝ) (hN : 4*(10 : ℝ)^8 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/100 ≤ V) : 0 < V := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hL0 : 0 < L := by linarith
  exact lt_of_lt_of_le (by positivity) hV

lemma variance_sqrt_large (N L V : ℝ) (hN : 4*(10 : ℝ)^8 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/100 ≤ V) :
    24*L ≤ Real.sqrt V := by
  have hV0 := variance_positive N L V hN hL hV
  have hN' : (10 : ℝ)^6 ≤ N := le_trans (by norm_num) hN
  have hh := mul_le_mul_of_nonneg_right hN' (sq_nonneg L)
  apply (Real.le_sqrt (by positivity) hV0.le).2
  nlinarith

/-- A variance-relative cubic remainder has normalized squared error
O(L²/V), eliminating the cubed lower-variance loss. -/
theorem normalized_cubic_small (N L V : ℝ) (hN : 4*(10 : ℝ)^8 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/100 ≤ V) :
    (6*V*L)^2 * (1/Real.sqrt V)^6 ≤ 1/(10 : ℝ)^5 := by
  have hV0 := variance_positive N L V hN hL hV
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hbound : 4*(10 : ℝ)^6*L^2 ≤ V := by
    have hh := mul_le_mul_of_nonneg_right hN (sq_nonneg L)
    nlinarith only [hh,hV]
  have hp := mul_le_mul_of_nonneg_right hbound (sq_nonneg V)
  have hs6 : (Real.sqrt V)^6 = V^3 := by
    calc
      _ = ((Real.sqrt V)^2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt hV0.le]
  have hb : (10 : ℝ)^5*(6*V*L)^2 ≤ (Real.sqrt V)^6 := by
    rw [hs6]
    have hz : 0 ≤ L^2*V^2 := by positivity
    nlinarith only [hp,hz]
  rw [one_div_pow,mul_one_div]
  apply (div_le_iff₀ (pow_pos hs0 6)).2
  nlinarith only [hb]

lemma local_cubic_relative (L V θ : ℝ) (hL : 1 ≤ L) (hV : 0 ≤ V)
    (hθ : 0 ≤ θ) (hθmax : θ ≤ 1/(24*L)) :
    6*V*L*θ^3 ≤ V*θ^2/4 := by
  have hL0 : 0 < L := by linarith
  have hm := (le_div_iff₀ (show 0 < 24*L by positivity)).1 hθmax
  have hp := mul_le_mul_of_nonneg_right hm (show 0 ≤ V*θ^2 by positivity)
  nlinarith only [hp]

/-- The far tail starts at 1/(24 L). A finite hundredth-order exponential
bound is enough at N≥4·10^8; no numerical exponential oracle is used. -/
theorem far_tail_small (N V : ℝ) (hN : 4*(10 : ℝ)^8 ≤ N)
    (hV0 : 0 < V) (hV : V ≤ 100*N^3) :
    Real.exp (-N/(3000000 : ℝ)) ≤ (1/Real.sqrt V)^3/10000 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : 0 ≤ N := by linarith
  have hNN := mul_le_mul_of_nonneg_right hN1 (pow_nonneg hN0 3)
  have hsupper : Real.sqrt V ≤ 10*N^2 := by
    have hsq := Real.sq_sqrt hV0.le
    have hs0 := Real.sqrt_nonneg V
    nlinarith [sq_nonneg N]
  have hcube' : (Real.sqrt V)^3 ≤ 1000*N^5 := by
    calc
      (Real.sqrt V)^3 = Real.sqrt V*V := by
        rw [show (Real.sqrt V)^3=Real.sqrt V*(Real.sqrt V)^2 by ring,Real.sq_sqrt hV0.le]
      _ ≤ (10*N^2)*(100*N^3) := mul_le_mul hsupper hV hV0.le (by positivity)
      _ = 1000*N^5 := by ring
  let E : ℝ := (Nat.factorial 100 : ℝ) * ((3000000 : ℝ))^100
  have hE0 : 0 < E := by norm_num [E]
  have hpowN := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4*(10 : ℝ)^8) hN 95
  have hN95 : E*10000000 ≤ N^95 := by
    norm_num [E] at hpowN ⊢
    linarith
  have hprod := mul_le_mul_of_nonneg_right hN95 (pow_nonneg hN0 5)
  have hfrac : 10000000*N^5 ≤ N^100/E := by
    apply (le_div_iff₀ hE0).2
    nlinarith only [hprod]
  have he := Real.pow_div_factorial_le_exp (N/(3000000 : ℝ)) (by positivity) 100
  have he' : N^100/E ≤ Real.exp (N/(3000000 : ℝ)) := by
    convert he using 1 <;> norm_num [E, div_pow] <;> ring
  have hfinal : 10000*(Real.sqrt V)^3 ≤ Real.exp (N/(3000000 : ℝ)) := by
    have hh := hfrac.trans he'
    linarith
  have hspos : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hright : (1/Real.sqrt V)^3/10000 = 1/(10000*(Real.sqrt V)^3) := by
    field_simp
  rw [hright, show -N/(3000000 : ℝ) = -(N/(3000000 : ℝ)) by ring,
    Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
  simpa using hfinal

#print axioms BBFMLocal.normalized_cubic_small
#print axioms BBFMLocal.far_tail_small
end BBFMLocal
