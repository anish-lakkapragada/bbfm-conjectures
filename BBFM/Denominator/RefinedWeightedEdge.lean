import BBFM.Denominator.RefinedTail
import BBFM.Denominator.RefinedEdgeSequence

noncomputable section
namespace BBFMRefined
open Polynomial Finset DenominatorResearch

lemma weightedProduct_zero (m : ℕ → ℕ) (n : ℕ) :
    (weightedProduct m n).coeff 0=1 := by
  rw [coeff_zero_eq_eval_zero]
  simp [weightedProduct,eval_prod]

lemma second_differential_coeff (P : ℝ[X]) (j : ℕ) :
    ((1+X)*P.derivative).coeff (j+1) =
      ((j : ℝ)+2)*P.coeff (j+2)+((j : ℝ)+1)*P.coeff (j+1) := by
  simp only [add_mul,one_mul,coeff_add,coeff_X_mul,coeff_derivative]
  push_cast
  ring

lemma linear_multiplier_coeff (P : ℝ[X]) (r s : ℝ) (j : ℕ) :
    ((C r+C (2*s)*X)*P).coeff (j+1) =
      r*P.coeff (j+1)+2*s*P.coeff j := by
  simp only [add_mul,coeff_add,mul_assoc,coeff_C_mul,coeff_X_mul]

lemma shifted_cube_coeff_le (P : ℝ[X]) (j : ℕ) (hP : Nonneg P)
    (hg : ∀ i < j, P.coeff i ≤ P.coeff (i+1)) :
    (X^3*P).coeff (j+2) ≤ P.coeff j := by
  cases j with
  | zero => simp only [coeff_X_pow_mul']; norm_num; exact hP 0
  | succ j =>
    have he : j+1+2=j+3 := by omega
    rw [he,coeff_X_pow_mul]
    exact hg j (by omega)

/-- A concrete signed remainder bound for every finite weighted product.
No hypothesis about log-concavity is used. -/
theorem weightedProduct_second_remainder (m : ℕ → ℕ) (n K j : ℕ)
    (hm : ∀ i, 1 ≤ i → i ≤ n+2 → m i ≤ m 1)
    (hj : 2 ≤ j) (hjK : j ≤ K) (hr : 4*K ≤ m 1) :
    let P := weightedProduct m (n+2)
    |((j : ℝ)+1)*P.coeff (j+1)-((m 1 : ℝ)-j)*P.coeff j-
      2*(m 2 : ℝ)*P.coeff (j-1)| ≤ 16*(m 1 : ℝ)*P.coeff (j-2) := by
  dsimp only
  let P := weightedProduct m (n+2)
  change |((j : ℝ)+1)*P.coeff (j+1)-((m 1 : ℝ)-j)*P.coeff j-
    2*(m 2 : ℝ)*P.coeff (j-1)| ≤ 16*(m 1 : ℝ)*P.coeff (j-2)
  have hP : Nonneg P := weightedProduct_nonneg m (n+2)
  have hQ := tailProduct_nonneg m n
  have hfac := weightedProduct_split_two m n
  have hlow := differential_lower_second (m 1) (m 2) (tailProduct m n) hQ
  have hupp := differential_upper_second (m 1) (m 2) (tailProduct m n) (tailMajorant m n)
    hQ (tailProduct_derivative_upper m n)
  dsimp only at hlow hupp
  rw [← hfac] at hlow hupp
  change CoeffLE ((C (m 1 : ℝ)+C (2*(m 2 : ℝ))*X)*P)
    ((1+X)*P.derivative+C (2*(m 2 : ℝ))*X^3*P) at hlow
  change CoeffLE ((1+X)*P.derivative)
    ((C (m 1 : ℝ)+C (2*(m 2 : ℝ))*X)*P+P*tailErrorMajorant m n) at hupp
  have hrR : 4*(K : ℝ) ≤ (m 1 : ℝ) := by exact_mod_cast hr
  have hg := initial_growth (fun q => P.coeff q) (m 1) K hP hrR
    (weightedProduct_coeff_lower m (n+2) (by omega))
  have hzero := tailErrorMajorant_zero_one m n
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hj
  have heq : 2+t=t+2 := by omega
  rw [heq] at hjK ⊢
  have ht : (P*tailErrorMajorant m n).coeff (t+2) ≤ 14*(m 1 : ℝ)*P.coeff t :=
    convolution_tail_bound P _ (m 1) t hP (by positivity) hzero.1 hzero.2
      (fun q => tailErrorMajorant_coeff_le m n (m 1) q (fun i hi hin => hm i (by omega) hin))
      (fun q hq => hg q (by omega))
  have hshift := shifted_cube_coeff_le P t hP (fun q hq => by
    have hh := hg q (by omega)
    linarith [hP q])
  have hshift' := mul_le_mul_of_nonneg_left hshift (show 0 ≤ 2*(m 2 : ℝ) by positivity)
  have hs : (m 2 : ℝ) ≤ m 1 := by exact_mod_cast hm 2 (by omega) (by omega)
  have hs' := mul_le_mul_of_nonneg_right hs (hP t)
  have hl := hlow (t+2)
  have hu := hupp (t+2)
  have heq' : t+2=(t+1)+1 := by omega
  rw [heq',linear_multiplier_coeff,coeff_add,second_differential_coeff] at hl
  rw [heq',second_differential_coeff,coeff_add,linear_multiplier_coeff] at hu
  simp only [mul_assoc,coeff_C_mul] at hl
  have heq'' : t+1+1=t+2 := by omega
  have heq''' : t+1+2=t+3 := by omega
  rw [heq'',heq'''] at hl hu
  push_cast at hl hu ⊢
  rw [show t+2+1=t+3 by omega]
  have hrt : 0 ≤ (m 1 : ℝ)*P.coeff t := mul_nonneg (by positivity) (hP t)
  rw [abs_le]
  constructor <;> nlinarith [hP t]

/-- A general improved elementary edge theorem. The sufficient condition
is cubic in the index after squaring the number of unit factors. -/
theorem weightedProduct_cubic_edge (m : ℕ → ℕ) (n k : ℕ) (hn : 2 ≤ n)
    (hk : 1 ≤ k) (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ m 1)
    (hsize : 10000*k^3 ≤ (m 1)^2) :
    (weightedProduct m n).coeff (k-1)*(weightedProduct m n).coeff (k+1) ≤
      (weightedProduct m n).coeff k^2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsizeR : 10000*(k : ℝ)^3 ≤ (m 1 : ℝ)^2 := by exact_mod_cast hsize
  have hr0 : 0 < (m 1 : ℝ) := by
    have hk3 : (1 : ℝ) ≤ (k : ℝ)^3 := one_le_pow₀ hkR
    have hh : (0 : ℝ) ≤ m 1 := by positivity
    nlinarith
  by_cases hk3 : 3 ≤ k
  · have hk2 : (k : ℝ)^2 ≤ (k : ℝ)^3 := by nlinarith [sq_nonneg ((k : ℝ)-1)]
    have hrk : 10*(k : ℝ) ≤ (m 1 : ℝ) := by
      by_contra hh
      have hh' : (m 1 : ℝ) < 10*(k : ℝ) := lt_of_not_ge hh
      have hh2 : (m 1 : ℝ)^2 < (10*(k : ℝ))^2 :=
        (sq_lt_sq₀ hr0.le (by positivity)).2 hh'
      nlinarith
    obtain ⟨N,rfl⟩ := Nat.exists_eq_add_of_le hn
    have hnrewrite : 2+N=N+2 := by omega
    rw [hnrewrite] at hm ⊢
    apply edge_logconcave_of_second_order_bounds
      (fun j => (weightedProduct m (N+2)).coeff j) (m 1) (m 2) k hk3 hr0
      (by positivity) (by exact_mod_cast hm 2 (by omega) (by omega)) hsizeR
    · exact weightedProduct_nonneg m (N+2)
    · exact weightedProduct_zero m (N+2)
    · exact weightedProduct_coeff_lower m (N+2) (by omega)
    · intro j hj
      exact weightedProduct_coeff_upper m (N+2) (m 1) j hm
    · intro j hj hjk
      exact weightedProduct_second_remainder m N k j hm hj hjk
        (by exact_mod_cast (show 4*(k : ℝ) ≤ (m 1 : ℝ) by linarith))
  · have hk2 : k ≤ 2 := by omega
    have hsmall : 6*k^2 ≤ m 1 := by
      have hkR2 : (k : ℝ) ≤ 2 := by exact_mod_cast hk2
      have hk3R : (1 : ℝ) ≤ (k : ℝ)^3 := one_le_pow₀ hkR
      have hr24 : (24 : ℝ) ≤ m 1 := by
        by_contra hh
        have hh' : (m 1 : ℝ) < 24 := lt_of_not_ge hh
        have hsquare : (m 1 : ℝ)^2 < 24^2 := (sq_lt_sq₀ hr0.le (by norm_num)).2 hh'
        nlinarith
      have hh : 6*(k : ℝ)^2 ≤ (m 1 : ℝ) := by nlinarith
      exact_mod_cast hh
    exact weightedProduct_edge_logconcave m n k (by omega) hk hm hsmall

theorem den_cubic_edge (n k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hsize : 10000*k^3 ≤ (Nat.log 2 n+1)^2) :
    (den n).coeff (k-1)*(den n).coeff (k+1) ≤ (den n).coeff k^2 := by
  unfold den
  apply weightedProduct_cubic_edge _ n k hn hk
  · intro i hi hin
    simp only [Nat.div_one]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1
  · simpa using hsize

#print axioms weightedProduct_second_remainder
#print axioms weightedProduct_cubic_edge
#print axioms den_cubic_edge
end BBFMRefined
