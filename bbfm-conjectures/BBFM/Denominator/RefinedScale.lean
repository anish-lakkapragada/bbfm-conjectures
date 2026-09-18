import BBFM.Denominator.RefinedMoment

noncomputable section
namespace BBFMRefined
open Real

lemma variance_positive (N L V : ℝ) (hN : (10 : ℝ)^28 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/1000 ≤ V) : 0 < V := by
  have hN0 : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hL0 : 0 < L := by linarith
  exact lt_of_lt_of_le (by positivity) hV

lemma variance_sqrt_large (N L V : ℝ) (hN : (10 : ℝ)^28 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/1000 ≤ V) :
    100000000*L ≤ Real.sqrt V := by
  have hV0 := variance_positive N L V hN hL hV
  have hN' : (10 : ℝ)^19 ≤ N := le_trans (by norm_num) hN
  have hh := mul_le_mul_of_nonneg_right hN' (sq_nonneg L)
  apply (Real.le_sqrt (by positivity) hV0.le).2
  nlinarith

/-- The squared cubic error, in standard-deviation coordinates, is uniformly
small. The proof uses the variance lower bound rather than a huge pointwise
Taylor interval. -/
theorem normalized_cubic_small (N L V : ℝ) (hN : (10 : ℝ)^28 ≤ N)
    (hL : 1 ≤ L) (hV : N*L^2/1000 ≤ V) :
    (10000*N*L^3)^2 * (1/Real.sqrt V)^6 ≤ 1/(10 : ℝ)^10 := by
  have hV0 := variance_positive N L V hN hL hV
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hN0 : 0 ≤ N := le_trans (by positivity) hN
  have hL0 : 0 ≤ L := by linarith
  have hv3 := pow_le_pow_left₀ (show 0 ≤ N*L^2/1000 by positivity) hV 3
  have hN' : (10 : ℝ)^27 ≤ N := le_trans (by norm_num) hN
  have hn3 := mul_le_mul_of_nonneg_right hN' (show 0 ≤ N^2*L^6 by positivity)
  have hs6 : (Real.sqrt V)^6 = V^3 := by
    calc
      _ = ((Real.sqrt V)^2)^3 := by ring
      _ = _ := by rw [Real.sq_sqrt hV0.le]
  have hbound : (10 : ℝ)^10 * (10000*N*L^3)^2 ≤ (Real.sqrt V)^6 := by
    rw [hs6]
    nlinarith only [hv3, hn3]
  rw [one_div_pow, mul_one_div]
  apply (div_le_iff₀ (pow_pos hs0 6)).2
  nlinarith only [hbound]

lemma local_cubic_relative (N L V θ : ℝ) (hN : 0 ≤ N) (hL : 1 ≤ L)
    (hV : N*L^2/1000 ≤ V) (hθ : 0 ≤ θ)
    (hθmax : θ ≤ 1/(100000000*L)) :
    10000*N*L^3*θ^3 ≤ V*θ^2/4 := by
  have hL0 : 0 < L := by linarith
  have hm := (le_div_iff₀ (show 0 < 100000000*L by positivity)).1 hθmax
  have hlt : L*θ ≤ 1/100000000 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hlt (show 0 ≤ N*L^2*θ^2 by positivity)
  have hv := mul_le_mul_of_nonneg_right hV (sq_nonneg θ)
  have hz : 0 ≤ N*L^2*θ^2 := by positivity
  nlinarith only [hp,hv,hz]

/-- The far tail starts at 1/(10^8 L). A finite hundredth-order exponential
bound is enough at N≥10^28; no numerical exponential oracle is used. -/
theorem far_tail_small (N V : ℝ) (hN : (10 : ℝ)^28 ≤ N)
    (hV0 : 0 < V) (hV : V ≤ 100*N^3) :
    Real.exp (-N/(10 : ℝ)^24) ≤ (1/Real.sqrt V)^3/10000 := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hN0 : 0 ≤ N := by linarith
  have hNN := mul_le_mul_of_nonneg_right hN1 (pow_nonneg hN0 3)
  have hsupper : Real.sqrt V ≤ 10*N^2 := by
    have hsq := Real.sq_sqrt hV0.le
    have hs0 := Real.sqrt_nonneg V
    nlinarith [sq_nonneg N]
  have hcube := pow_le_pow_left₀ (Real.sqrt_nonneg V) hsupper 3
  have hcube' : (Real.sqrt V)^3 ≤ 1000*N^6 := by nlinarith
  let E : ℝ := (Nat.factorial 100 : ℝ) * ((10 : ℝ)^24)^100
  have hE0 : 0 < E := by norm_num [E]
  have hpowN := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (10 : ℝ)^28) hN 94
  have hN94 : E*10000000 ≤ N^94 := by
    norm_num [E] at hpowN ⊢
    linarith
  have hprod := mul_le_mul_of_nonneg_right hN94 (pow_nonneg hN0 6)
  have hfrac : 10000000*N^6 ≤ N^100/E := by
    apply (le_div_iff₀ hE0).2
    nlinarith only [hprod]
  have he := Real.pow_div_factorial_le_exp (N/(10 : ℝ)^24) (by positivity) 100
  have he' : N^100/E ≤ Real.exp (N/(10 : ℝ)^24) := by
    convert he using 1 <;> norm_num [E, div_pow] <;> ring
  have hfinal : 10000*(Real.sqrt V)^3 ≤ Real.exp (N/(10 : ℝ)^24) := by
    have hh := hfrac.trans he'
    linarith
  have hspos : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hright : (1/Real.sqrt V)^3/10000 = 1/(10000*(Real.sqrt V)^3) := by
    field_simp
  rw [hright, show -N/(10 : ℝ)^24 = -(N/(10 : ℝ)^24) by ring,
    Real.exp_neg, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
  simpa using hfinal

#print axioms normalized_cubic_small
#print axioms far_tail_small
end BBFMRefined
