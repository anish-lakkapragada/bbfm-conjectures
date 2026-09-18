import BBFM.Denominator.RefinedEdgeAlgebra

noncomputable section
namespace BBFMRefined
open Finset DenominatorResearch

lemma initial_growth (a : ℕ → ℝ) (r : ℝ) (K : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hr : 4*(K : ℝ) ≤ r)
    (hl : ∀ j, (r-j)*a j ≤ ((j : ℝ)+1)*a (j+1)) :
    ∀ j < K, 3*a j ≤ a (j+1) := by
  intro j hj
  have hjR : (j : ℝ)+1 ≤ K := by exact_mod_cast (show j+1 ≤ K by omega)
  have hc : 3*((j : ℝ)+1) ≤ r-j := by linarith
  have hh := mul_le_mul_of_nonneg_right hc (ha j)
  have hz := hl j
  have hp : 0 < (j : ℝ)+1 := by positivity
  nlinarith

lemma initial_positive (a : ℕ → ℝ) (r : ℝ) (K : ℕ)
    (hzero : a 0=1) (hr : (K : ℝ) < r)
    (hl : ∀ j, (r-j)*a j ≤ ((j : ℝ)+1)*a (j+1)) :
    ∀ j ≤ K+1, 0 < a j := by
  intro j hj
  induction j with
  | zero => rw [hzero]; norm_num
  | succ j ih =>
    have hi := ih (by omega)
    have hjR : (j : ℝ) ≤ K := by exact_mod_cast (show j ≤ K by omega)
    have hp : 0 < (r-j)*a j := mul_pos (by linarith) hi
    have hh := hl j
    have hpos : 0 < ((j : ℝ)+1)*a (j+1) := lt_of_lt_of_le hp hh
    exact pos_of_mul_pos_right hpos (by positivity)

lemma rough_ratio_bounds (a : ℕ → ℝ) (r : ℝ) (K j : ℕ)
    (hj : 1 ≤ j) (hjK : j ≤ K) (hr : 4*(K : ℝ) ≤ r)
    (ha : ∀ q, 0 ≤ a q) (hap : ∀ q ≤ K+1, 0 < a q)
    (hl : ∀ q, (r-q)*a q ≤ ((q : ℝ)+1)*a (q+1))
    (hu : ∀ q ≤ K, ((q : ℝ)+1)*a (q+1) ≤
      r*∑ t ∈ range (q+1), ((q : ℝ)+1-t)*a t) :
    r-j ≤ ((j : ℝ)+1)*a (j+1)/a j ∧
    ((j : ℝ)+1)*a (j+1)/a j ≤ r+8*j := by
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjKR : (j : ℝ) ≤ K := by exact_mod_cast hjK
  have hr0 : 0 < r := by linarith
  have haj := hap j (by omega)
  have hg := initial_growth a r K ha hr hl
  have heq : j-1+1=j := by omega
  have heqR : ((j-1 : ℕ) : ℝ)=(j : ℝ)-1 := by rw [Nat.cast_sub hj]; norm_num
  have hprev := hl (j-1)
  rw [heq,heqR] at hprev
  have hba : r*a (j-1) ≤ 2*(j : ℝ)*a j := by
    have hx := mul_le_mul_of_nonneg_right (show r/2 ≤ r-((j : ℝ)-1) by linarith) (ha (j-1))
    nlinarith
  obtain ⟨_,hw⟩ := growing_sums a ha (j-1) (fun q hq => hg q (by omega))
  rw [heq,heqR] at hw
  have hsum : (∑ t ∈ range (j+1), ((j : ℝ)+1-t)*a t) ≤ a j+4*a (j-1) := by
    rw [sum_range_succ]
    have hh : (∑ t ∈ range j, ((j : ℝ)+1-t)*a t) ≤ 4*a (j-1) := by
      convert hw using 1 <;> congr 1 <;> ext t <;> ring
    simp only [add_sub_cancel_left,one_mul]
    linarith
  constructor
  · exact (le_div_iff₀ haj).2 (by simpa [mul_comm] using hl j)
  · apply (div_le_iff₀ haj).2
    have hh := (hu j hjK).trans (mul_le_mul_of_nonneg_left hsum hr0.le)
    nlinarith

lemma sequence_ratio_error (a : ℕ → ℝ) (r s : ℝ) (K j : ℕ)
    (hj : 2 ≤ j) (hjK : j ≤ K) (hr : 4*(K : ℝ) ≤ r)
    (hs : 0 ≤ s) (hsr : s ≤ r)
    (ha : ∀ q, 0 ≤ a q) (hap : ∀ q ≤ K+1, 0 < a q)
    (hl : ∀ q, (r-q)*a q ≤ ((q : ℝ)+1)*a (q+1))
    (hu : ∀ q ≤ K, ((q : ℝ)+1)*a (q+1) ≤
      r*∑ t ∈ range (q+1), ((q : ℝ)+1-t)*a t)
    (he : |((j : ℝ)+1)*a (j+1)-(r-j)*a j-2*s*a (j-1)| ≤ 16*r*a (j-2)) :
    |r*(((j : ℝ)+1)*a (j+1)/a j)-(r^2-r*j+2*s*j)| ≤ 1000*(j : ℝ)^2 := by
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hjKR : (j : ℝ) ≤ K := by exact_mod_cast hjK
  have hr0 : 0 < r := by linarith
  have heq : j-1+1=j := by omega
  have heq' : j-2+1=j-1 := by omega
  have heqR : ((j-1 : ℕ) : ℝ)=(j : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ j)]; norm_num
  have heqR' : ((j-2 : ℕ) : ℝ)=(j : ℝ)-2 := by rw [Nat.cast_sub hj]; norm_num
  have hp := rough_ratio_bounds a r K (j-1) (by omega) (by omega) hr ha hap hl hu
  rw [heq,heqR,sub_add_cancel] at hp
  have h1 := hl (j-1)
  have h2 := hl (j-2)
  rw [heq,heqR,sub_add_cancel] at h1
  rw [heq',heqR'] at h2
  have hba : r*a (j-1) ≤ 2*(j : ℝ)*a j := by
    have hh := mul_le_mul_of_nonneg_right (show r/2 ≤ r-((j : ℝ)-1) by linarith) (ha (j-1))
    nlinarith
  have hcb : r*a (j-2) ≤ 2*(j : ℝ)*a (j-1) := by
    have hh := mul_le_mul_of_nonneg_right (show r/2 ≤ r-((j : ℝ)-2) by linarith) (ha (j-2))
    nlinarith [ha (j-1)]
  exact normalized_ratio_error r s j (a j) (a (j-1)) (a (j-2)) (a (j+1))
    hr0 hs hsr (by linarith) (by linarith) (hap j (by omega))
    (hap (j-1) (by omega)) (ha _) (by linarith [hp.1]) (by linarith [hp.2])
    hba hcb he

/-- A coefficient-sequence theorem with a retained quadratic term. All
hypotheses will be discharged for the actual weighted product. -/
theorem edge_logconcave_of_second_order_bounds (a : ℕ → ℝ) (r s : ℝ) (k : ℕ)
    (hk : 3 ≤ k) (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r)
    (hsize : 10000*(k : ℝ)^3 ≤ r^2)
    (ha : ∀ q, 0 ≤ a q) (hzero : a 0=1)
    (hl : ∀ q, (r-q)*a q ≤ ((q : ℝ)+1)*a (q+1))
    (hu : ∀ q ≤ k, ((q : ℝ)+1)*a (q+1) ≤
      r*∑ t ∈ range (q+1), ((q : ℝ)+1-t)*a t)
    (he : ∀ j, 2 ≤ j → j ≤ k →
      |((j : ℝ)+1)*a (j+1)-(r-j)*a j-2*s*a (j-1)| ≤ 16*r*a (j-2)) :
    a (k-1)*a (k+1) ≤ a k^2 := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk2 : (k : ℝ)^2 ≤ (k : ℝ)^3 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
  have hrk : 10*(k : ℝ) ≤ r := by
    by_contra hh
    have hh' : r < 10*(k : ℝ) := lt_of_not_ge hh
    have hh2 : r^2 < (10*(k : ℝ))^2 := (sq_lt_sq₀ hr.le (by positivity)).2 hh'
    nlinarith
  have hr4 : 4*(k : ℝ) ≤ r := by linarith
  have hap := initial_positive a r k hzero (by linarith) hl
  have hp := rough_ratio_bounds a r k (k-1) (by omega) (by omega) hr4 ha hap hl hu
  have hep := sequence_ratio_error a r s k (k-1) (by omega) (by omega) hr4 hs hsr ha hap hl hu
    (he (k-1) (by omega) (by omega))
  have hen := sequence_ratio_error a r s k k (by omega) le_rfl hr4 hs hsr ha hap hl hu
    (he k (by omega) le_rfl)
  have heq : k-1+1=k := by omega
  have heqR : ((k-1 : ℕ) : ℝ)=(k : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  rw [heq,heqR,sub_add_cancel] at hp hep
  have hh := ratio_comparison r s k ((k : ℝ)*a k/a (k-1)) (((k : ℝ)+1)*a (k+1)/a k)
    (by linarith) hr hs hsr hsize (by linarith [hp.1]) hep hen
  have ha0 := hap (k-1) (by omega)
  have hb0 := hap k (by omega)
  have hh' : (k : ℝ)*((k : ℝ)+1)*(a (k+1)/a k) ≤
      (k : ℝ)*((k : ℝ)+1)*(a k/a (k-1)) := by convert hh using 1 <;> ring
  have hrat := (mul_le_mul_iff_right₀ (show 0 < (k : ℝ)*((k : ℝ)+1) by positivity)).mp hh'
  have hfinal := (div_le_div_iff₀ hb0 ha0).mp hrat
  nlinarith

#print axioms initial_growth
#print axioms initial_positive
#print axioms rough_ratio_bounds
#print axioms sequence_ratio_error
#print axioms edge_logconcave_of_second_order_bounds
end BBFMRefined
