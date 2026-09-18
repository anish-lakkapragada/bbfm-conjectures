import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import BBFM.Denominator.RefinedWeightedEdge

noncomputable section
namespace BBFMLinear
open Finset PowerSeries

def logD (P : ℝ⟦X⟧) : ℝ⟦X⟧ := derivative ℝ P * P⁻¹

lemma logD_mul (P Q : ℝ⟦X⟧) (hP : constantCoeff P = 1)
    (hQ : constantCoeff Q = 1) : logD (P*Q)=logD P+logD Q := by
  have hp := PowerSeries.mul_inv_cancel P (by rw [hP]; norm_num)
  have hq := PowerSeries.mul_inv_cancel Q (by rw [hQ]; norm_num)
  simp only [logD,Derivation.leibniz,PowerSeries.mul_inv_rev,smul_eq_mul]
  calc
    (P * derivative ℝ Q + Q * derivative ℝ P) * (Q⁻¹ * P⁻¹) =
      derivative ℝ P*P⁻¹*(Q*Q⁻¹)+derivative ℝ Q*Q⁻¹*(P*P⁻¹) := by ring
    _ = _ := by rw [hp,hq]; ring

lemma logD_pow (P : ℝ⟦X⟧) (hP : constantCoeff P=1) (m : ℕ) :
    logD (P^m)=(m : ℝ⟦X⟧)*logD P := by
  induction m with
  | zero => simp [logD,PowerSeries.derivative_one]
  | succ m ih =>
    rw [pow_succ,logD_mul _ _ (by simp [hP]) hP,ih]
    push_cast
    ring

lemma logD_prod {ι : Type*} (s : Finset ι) (P : ι → ℝ⟦X⟧)
    (hP : ∀ i ∈ s, constantCoeff (P i)=1) :
    logD (∏ i ∈ s, P i)=∑ i ∈ s, logD (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [logD,PowerSeries.derivative_one]
  | @insert i s hi ih =>
    rw [prod_insert hi,sum_insert hi,logD_mul]
    · rw [ih (fun j hj => hP j (mem_insert_of_mem hj))]
    · exact hP i (mem_insert_self _ _)
    · rw [map_prod]
      exact Finset.prod_eq_one (fun j hj => hP j (mem_insert_of_mem hj))

lemma one_add_X_constant (i : ℕ) (hi : 1 ≤ i) :
    constantCoeff (1+X^i : ℝ⟦X⟧)=1 := by
  simp [show i ≠ 0 by omega]

lemma binomial_inverse_coeff_abs (i : ℕ) (hi : 1 ≤ i) (j : ℕ) :
    |coeff j ((1+X^i : ℝ⟦X⟧)⁻¹)| ≤ 1 := by
  have hc := one_add_X_constant i hi
  have he := PowerSeries.mul_inv_cancel (1+X^i : ℝ⟦X⟧) (by rw [hc]; norm_num)
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hh := congrArg (coeff j) he
    rw [add_mul,one_mul,map_add,coeff_X_pow_mul',coeff_one] at hh
    by_cases hj : j=0
    · subst j
      rw [ite_eq_right (show ¬i ≤ 0 by omega),add_zero,ite_eq_left rfl] at hh
      rw [hh]; norm_num
    · rw [ite_eq_right hj] at hh
      by_cases hij : i ≤ j
      · rw [ite_eq_left hij] at hh
        have ht := ih (j-i) (by omega)
        have hx : coeff j ((1+X^i : ℝ⟦X⟧)⁻¹) =
          -coeff (j-i) ((1+X^i : ℝ⟦X⟧)⁻¹) := by linarith
        simpa [hx] using ht
      · rw [ite_eq_right hij,add_zero] at hh
        rw [hh]; norm_num

lemma binomial_logD_coeff (i j : ℕ) (hi : 1 ≤ i) :
    coeff j (logD (1+X^i : ℝ⟦X⟧)) =
      if i ≤ j+1 then (i : ℝ)*coeff (j+1-i) ((1+X^i : ℝ⟦X⟧)⁻¹) else 0 := by
  rw [logD,map_add,PowerSeries.derivative_one,zero_add,PowerSeries.derivative_pow]
  simp only [PowerSeries.derivative_X,mul_one]
  rw [mul_assoc,show (i : ℝ⟦X⟧)=C (i : ℝ) by simp,coeff_C_mul,coeff_X_pow_mul']
  have hle : i-1 ≤ j  ↔  i ≤ j+1 := by omega
  simp only [hle]
  split_ifs with h
  · rw [show j-(i-1)=j+1-i by omega]
  · simp

lemma binomial_logD_coeff_abs (i j : ℕ) (hi : 1 ≤ i) :
    |coeff j (logD (1+X^i : ℝ⟦X⟧))| ≤ 
      if i ≤ j+1 then (i : ℝ) else 0 := by
  rw [binomial_logD_coeff i j hi]
  split_ifs with h
  · rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ i)]
    simpa using mul_le_mul_of_nonneg_left (binomial_inverse_coeff_abs i hi (j+1-i))
      (show (0 : ℝ) ≤ i by positivity)
  · simp

#print axioms binomial_inverse_coeff_abs
#print axioms binomial_logD_coeff_abs

def weightedSeries (m : ℕ → ℕ) (n : ℕ) : ℝ⟦X⟧ :=
  ∏ i ∈ range n, (1+X^(i+1))^(m (i+1))

lemma weightedSeries_constant (m : ℕ → ℕ) (n : ℕ) :
    constantCoeff (weightedSeries m n)=1 := by
  simp [weightedSeries,map_prod]

lemma weightedSeries_logD (m : ℕ → ℕ) (n : ℕ) :
    logD (weightedSeries m n) =
      ∑ i ∈ range n, C (m (i+1) : ℝ)*logD (1+X^(i+1)) := by
  rw [weightedSeries,logD_prod]
  · apply sum_congr rfl
    intro i hi
    rw [logD_pow _ (one_add_X_constant _ (by omega))]
    simp
  · intro i hi
    simp

lemma weightedSeries_logD_coeff_bound (m : ℕ → ℕ) (n j : ℕ)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ m 1) :
    |coeff j (logD (weightedSeries m n))| ≤ (m 1 : ℝ)*((j : ℝ)+1)^2 := by
  classical
  rw [weightedSeries_logD,map_sum]
  simp only [coeff_C_mul]
  let s := (range n).filter (fun i => i ≤ j)
  have hs : s ⊆ range (j+1) := by
    intro i hi
    simp only [s,mem_filter,mem_range] at hi ⊢
    omega
  have heq : (∑ i ∈ range n, (m (i+1) : ℝ)*coeff j (logD (1+X^(i+1)))) =
      ∑ i ∈ s, (m (i+1) : ℝ)*coeff j (logD (1+X^(i+1))) := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hin his
    have hij : ¬i ≤ j := by simpa [s,hin] using his
    rw [binomial_logD_coeff _ _ (by omega),ite_eq_right (by omega),mul_zero]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ s, |(m (i+1) : ℝ)*coeff j (logD (1+X^(i+1)))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (m 1 : ℝ)*((j : ℝ)+1) := by
      apply sum_le_sum
      intro i hi
      have hi' : i<n ∧ i ≤ j := by simpa [s] using hi
      have hb := binomial_logD_coeff_abs (i+1) j (by omega)
      rw [ite_eq_left (by omega)] at hb
      rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ m (i+1))]
      have hm' : (m (i+1) : ℝ) ≤ m 1 := by exact_mod_cast hm (i+1) (by omega) (by omega)
      have hiR : ((i+1 : ℕ) : ℝ) ≤ (j : ℝ)+1 := by exact_mod_cast (show i+1 ≤ j+1 by omega)
      exact mul_le_mul hm' (hb.trans hiR) (abs_nonneg _) (by positivity)
    _ = (#s : ℝ)*((m 1 : ℝ)*((j : ℝ)+1)) := by simp
    _ ≤ (m 1 : ℝ)*((j : ℝ)+1)^2 := by
      have hc : (#s : ℝ) ≤ (j : ℝ)+1 := by exact_mod_cast (card_le_card hs).trans_eq (card_range (j+1))
      nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ (m 1 : ℝ)*((j : ℝ)+1) by positivity)]

#print axioms weightedSeries_logD_coeff_bound

lemma weightedSeries_eq_coe (m : ℕ → ℕ) (n : ℕ) :
    weightedSeries m n=(DenominatorResearch.weightedProduct m n : ℝ⟦X⟧) := by
  rw [DenominatorResearch.weightedProduct,← Polynomial.coeToPowerSeries.ringHom_apply,map_prod]
  simp [weightedSeries]

lemma logD_recurrence (P : ℝ⟦X⟧) (hP : constantCoeff P=1) (j : ℕ) :
    ((j : ℝ)+1)*coeff (j+1) P =
      ∑ t ∈ range (j+1), coeff t (logD P)*coeff (j-t) P := by
  have he : derivative ℝ P=logD P*P := by
    rw [logD,mul_assoc,PowerSeries.inv_mul_cancel P (by rw [hP]; norm_num),mul_one]
  have hh := congrArg (coeff j) he
  rw [coeff_derivative,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hh
  push_cast at hh
  simpa [mul_comm] using hh

lemma weightedSeries_logD_zero (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    coeff 0 (logD (weightedSeries m n))=(m 1 : ℝ) := by
  rw [weightedSeries_logD,map_sum]
  simp only [coeff_C_mul]
  rw [sum_eq_single 0]
  · rw [binomial_logD_coeff _ _ (by omega)]
    norm_num [coeff_zero_eq_constantCoeff_apply,constantCoeff_inv]
  · intro i hin hi
    rw [binomial_logD_coeff _ _ (by omega),ite_eq_right (by omega),mul_zero]
  · intro h
    exact (h (by simp only [mem_range]; omega)).elim

theorem weightedProduct_log_recurrence (m : ℕ → ℕ) (n : ℕ) :
    ∃ b : ℕ → ℝ,
      (∀ j : ℕ, ((j : ℝ)+1)*(DenominatorResearch.weightedProduct m n).coeff (j+1) =
        ∑ t ∈ range (j+1), b t*(DenominatorResearch.weightedProduct m n).coeff (j-t)) ∧
      (1 ≤ n → b 0=(m 1 : ℝ)) ∧
      (∀ (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ m 1) (j : ℕ),
        |b j| ≤ (m 1 : ℝ)*((j : ℝ)+1)^2) := by
  refine ⟨fun j => coeff j (logD (weightedSeries m n)),?_,?_,?_⟩
  · intro j
    have hh := logD_recurrence _ (weightedSeries_constant m n) j
    simpa only [weightedSeries_eq_coe,Polynomial.coeff_coe] using hh
  · exact weightedSeries_logD_zero m n
  · intro hm j
    exact weightedSeries_logD_coeff_bound m n j hm

#print axioms weightedProduct_log_recurrence
end BBFMLinear
