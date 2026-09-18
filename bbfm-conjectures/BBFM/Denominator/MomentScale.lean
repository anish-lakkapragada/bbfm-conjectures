import BBFM.Denominator.LocalScale

/-! Scaling for cubic coefficient one and the far-tail estimate at parameter 36N. -/

noncomputable section
namespace BBFMMoment
open Real

lemma variance_positive (N L V : ℝ) (hN : 12*(10 : ℝ)^6 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/100 ≤ V) : 0 < V := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hL0 : 0 < L := by linarith
  exact lt_of_lt_of_le (by positivity) hV

lemma variance_sqrt_large (N L V : ℝ) (hN : 12*(10 : ℝ)^6 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/100 ≤ V) :
    4*L ≤ Real.sqrt V := by
  have hV0 := variance_positive N L V hN hL hV
  have hN' : (10 : ℝ)^6 ≤ N := le_trans (by norm_num) hN
  have hh := mul_le_mul_of_nonneg_right hN' (sq_nonneg L)
  apply (Real.le_sqrt (by positivity) hV0.le).2
  nlinarith

/-- A variance-relative cubic remainder has normalized squared error
O(L²/V), eliminating the cubed lower-variance loss. -/
theorem normalized_cubic_small (N L V : ℝ) (hN : 12*(10 : ℝ)^6 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/100 ≤ V) :
    (V*L)^2 * (1/Real.sqrt V)^6 ≤ 1/(10 : ℝ)^5 := by
  have hV0 := variance_positive N L V hN hL hV
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hbound : 100000*L^2 ≤ V := by
    have hh := mul_le_mul_of_nonneg_right hN (sq_nonneg L)
    nlinarith only [hh,hV]
  have hp := mul_le_mul_of_nonneg_right hbound (sq_nonneg V)
  have hs6 : (Real.sqrt V)^6 = V^3 := by
    calc
      _ = ((Real.sqrt V)^2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt hV0.le]
  have hb : (10 : ℝ)^5*(V*L)^2 ≤ (Real.sqrt V)^6 := by
    rw [hs6]
    have hz : 0 ≤ L^2*V^2 := by positivity
    nlinarith only [hp,hz]
  rw [one_div_pow,mul_one_div]
  apply (div_le_iff₀ (pow_pos hs0 6)).2
  nlinarith only [hb]

lemma local_cubic_relative (L V θ : ℝ) (hL : 1 ≤ L) (hV : 0 ≤ V)
    (hθ : 0 ≤ θ) (hθmax : θ ≤ 1/(4*L)) :
    V*L*θ^3 ≤ V*θ^2/4 := by
  have hL0 : 0 < L := by linarith
  have hm := (le_div_iff₀ (show 0 < 4*L by positivity)).1 hθmax
  have hp := mul_le_mul_of_nonneg_right hm (show 0 ≤ V*θ^2 by positivity)
  nlinarith only [hp]

theorem far_tail_small (N V : ℝ) (hN : 12*(10 : ℝ)^6 ≤ N)
    (hV0 : 0 < V) (hV : V ≤ 100*N^3) :
    Real.exp (-N/(80000 : ℝ)) ≤ (1/Real.sqrt V)^3/10000 := by
  have hN0 : 0 ≤ N := le_trans (by norm_num) hN
  have hold : 4*(10 : ℝ)^8 ≤ 36*N := by linarith
  have hvold : V ≤ 100*(36*N)^3 := by
    have hh := pow_nonneg hN0 3
    nlinarith
  calc
    Real.exp (-N/(80000 : ℝ)) ≤ Real.exp (-(36*N)/(3000000 : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ _ := BBFMLocal.far_tail_small (36*N) V hold hV0 hvold

#print axioms normalized_cubic_small
#print axioms far_tail_small
end BBFMMoment
