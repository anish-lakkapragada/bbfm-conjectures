/- Credited adaptation of StrictLinearEdge with the now discharged
28k threshold. The strict margin is 28k-k>16k. -/
import BBFM.Denominator.NewtonTwentyEight
import BBFM.Denominator.LinearLogDerivative

noncomputable section
namespace BBFM28
open BBFMLinear
open Finset DenominatorResearch BBFMRefined

lemma logconcave_of_ratio_increment_strict (a : ℕ → ℝ) (r : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hr : 28*(k : ℝ) ≤ r)
    (ha : 0<a k) (hap : 0<a (k-1))
    (hprev : r-k ≤ normRatio a (k-1))
    (hd : |normRatio a k-normRatio a (k-1)| ≤ 16) :
    a (k-1)*a (k+1) < a k^2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hh := (abs_le.mp hd).2
  have hc : 16*(k : ℝ) < normRatio a (k-1) := by linarith
  have hz : (k : ℝ)*normRatio a k < ((k : ℝ)+1)*normRatio a (k-1) := by
    nlinarith
  have he : ((k-1 : ℕ) : ℝ)=(k : ℝ)-1 := by rw [Nat.cast_sub hk]; norm_num
  simp only [normRatio,show k-1+1=k by omega,he,sub_add_cancel] at hz
  rw [← mul_div_assoc,← mul_div_assoc] at hz
  have hf := (div_lt_div_iff₀ ha hap).mp hz
  have hp : 0<(k : ℝ)*((k : ℝ)+1) := by positivity
  nlinarith

/-- Strict strengthening of the frozen uniform linear edge. The ratio proof
already has a strict margin because `28k-k > 16k`.
The underlying linear-edge proof and its analytic architecture retain their credit.
A uniform linear low-edge range for arbitrary bounded multiplicities.
No log-concavity or monotonicity assumption is imposed on the input product. -/
theorem weightedProduct_linear_edge_strict (m : ℕ → ℕ) (n k : ℕ)
    (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ m 1)
    (hsize : 28*k ≤ m 1) :
    (weightedProduct m n).coeff (k-1)*(weightedProduct m n).coeff (k+1) <
      (weightedProduct m n).coeff k^2 := by
  let a : ℕ → ℝ := fun j => (weightedProduct m n).coeff j
  let r : ℝ := m 1
  have hr : 28*(k : ℝ) ≤ r := by dsimp [r]; exact_mod_cast hsize
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr0 : 0<r := by linarith
  have ha0 : a 0=1 := weightedProduct_zero m n
  have ha : ∀ j, 0 ≤ a j := weightedProduct_nonneg m n
  have hl : ∀ j, (r-j)*a j ≤ ((j : ℝ)+1)*a (j+1) :=
    weightedProduct_coeff_lower m n (by omega)
  have hu : ∀ j ≤ k, ((j : ℝ)+1)*a (j+1) ≤
      r*∑ t ∈ range (j+1), ((j : ℝ)+1-t)*a t := by
    intro j hj
    exact weightedProduct_coeff_upper m n (m 1) j hm
  have hap : ∀ j ≤ k+1, 0<a j := initial_positive a r k ha0 (by linarith) hl
  obtain ⟨b,hrec,hbzero,hb⟩ := weightedProduct_log_recurrence m n
  have hb0 : b 0=r := hbzero hn
  have hR0 : normRatio a 0=r := by
    have hh := hrec 0
    norm_num only [Finset.sum_range_one,Nat.cast_zero,zero_add,one_mul,Nat.zero_sub] at hh
    change a 1=b 0*a 0 at hh
    rw [ha0,mul_one,hb0] at hh
    simpa [normRatio,ha0] using hh
  have hrough : ∀ j ≤ k, r-j ≤ normRatio a j ∧ normRatio a j ≤ r+8*j := by
    intro j hj
    by_cases hj0 : j=0
    · subst j; simp [hR0]
    · exact rough_ratio_bounds a r k j (by omega) hj (by linarith) ha hap hl hu
  have hd := normRatio_lipschitz a b r k hr hr0 hap (fun j hj => hrec j)
    (fun t ht => by simpa [r,add_assoc,show (1 : ℝ)+1=2 by norm_num] using hb hm (t+1)) hrough
  exact logconcave_of_ratio_increment_strict a r k hk hr (hap k (by omega))
    (hap (k-1) (by omega)) (by
      have hh := (hrough (k-1) (by omega)).1
      have hm1 : ((k-1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
      linarith) (hd k le_rfl)

theorem den_linear_edge_strict (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hsize : 28*k ≤ Nat.log 2 n+1) :
    (den n).coeff (k-1)*(den n).coeff (k+1) < (den n).coeff k^2 := by
  unfold den
  apply weightedProduct_linear_edge_strict _ n k hn hk
  · intro i hi hin
    simp only [Nat.div_one]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1
  · simpa using hsize

#print axioms weightedProduct_linear_edge_strict
#print axioms den_linear_edge_strict
end BBFM28
