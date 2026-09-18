import BBFM.Denominator.LinearLogDerivative
import Mathlib.NumberTheory.Divisors

/-! Exact signs in the logarithmic derivative, to support a source-specific
recurrence attack. These are auxiliary identities, not a proof of LC. -/
noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear
set_option maxHeartbeats 0

lemma inverse_binomial_multiple (i t : ℕ) (hi : 1 ≤ i) :
    coeff (i*t) ((1+X^i : ℝ⟦X⟧)⁻¹) = (-1 : ℝ)^t := by
  have hc := one_add_X_constant i hi
  have he := PowerSeries.mul_inv_cancel (1+X^i : ℝ⟦X⟧) (by rw [hc]; norm_num)
  induction t with
  | zero => simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_inv, hc]
  | succ t ih =>
    have hh := congrArg (coeff (i*(t+1))) he
    rw [add_mul,one_mul,map_add,coeff_X_pow_mul',coeff_one] at hh
    have hile : i ≤ i*(t+1) := by nlinarith
    have hzero : i*(t+1) ≠ 0 := by positivity
    rw [if_pos hile, if_neg hzero] at hh
    have hsub : i*(t+1)-i=i*t := by rw [Nat.mul_add]; simp
    rw [hsub, ih] at hh
    rw [pow_succ]
    linarith

lemma inverse_binomial_nondivisor (i j : ℕ) (hi : 1 ≤ i) (hd : ¬ i ∣ j) :
    coeff j ((1+X^i : ℝ⟦X⟧)⁻¹) = 0 := by
  have hc := one_add_X_constant i hi
  have he := PowerSeries.mul_inv_cancel (1+X^i : ℝ⟦X⟧) (by rw [hc]; norm_num)
  induction j using Nat.strong_induction_on with
  | h j ih =>
    have hj0 : j ≠ 0 := by intro h; subst j; exact hd (dvd_zero i)
    have hh := congrArg (coeff j) he
    rw [add_mul,one_mul,map_add,coeff_X_pow_mul',coeff_one,if_neg hj0] at hh
    by_cases hij : i ≤ j
    · rw [if_pos hij] at hh
      have hnot : ¬ i ∣ j-i := by
        intro hh
        have hadd := dvd_add hh (dvd_refl i)
        rw [Nat.sub_add_cancel hij] at hadd
        exact hd hadd
      rw [ih (j-i) (by omega) hnot] at hh
      simpa using hh
    · simpa [if_neg hij] using hh

lemma binomial_logD_divisor (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j) :
    coeff (j-1) (logD (1+X^i : ℝ⟦X⟧)) =
      if i ∣ j then (i : ℝ)*(-1 : ℝ)^(j/i-1) else 0 := by
  rw [binomial_logD_coeff i (j-1) hi, show j-1+1=j by omega]
  by_cases hd : i ∣ j
  · have hij := Nat.le_of_dvd (by omega : 0<j) hd
    rw [if_pos hij,if_pos hd]
    obtain ⟨t,rfl⟩ := hd
    have hit : i*t-i=i*(t-1) := by rw [Nat.mul_sub]; simp
    rw [hit,inverse_binomial_multiple i (t-1) hi]
    simp [Nat.mul_div_cancel_left t (by omega : 0 < i)]
  · rw [if_neg hd]
    by_cases hij : i ≤ j
    · rw [if_pos hij]
      have hnot : ¬i ∣ j-i := by
        intro h
        have hh := dvd_add h (dvd_refl i)
        rw [Nat.sub_add_cancel hij] at hh
        exact hd hh
      rw [inverse_binomial_nondivisor i (j-i) hi hnot,mul_zero]
    · rw [if_neg hij]

/-- Exact finite divisor sum for the logarithmic derivative kernel. -/
theorem weighted_logD_divisor_sum (m : ℕ → ℕ) (n j : ℕ) (hj : 1 ≤ j) :
    coeff (j-1) (logD (weightedSeries m n)) =
      ∑ i ∈ range n, if i+1 ∣ j then
        (m (i+1) : ℝ)*(i+1)*(-1 : ℝ)^(j/(i+1)-1) else 0 := by
  rw [weightedSeries_logD,map_sum]
  simp only [coeff_C_mul]
  apply sum_congr rfl
  intro i hi
  rw [binomial_logD_divisor (i+1) j (by omega) hj]
  split_ifs <;> simp [mul_assoc]

/-- Odd kernel indices are nonnegative for every nonnegative multiplicity profile. -/
theorem weighted_logD_odd_nonnegative (m : ℕ → ℕ) (n j : ℕ) (hj : Odd j) :
    0 ≤ coeff (j-1) (logD (weightedSeries m n)) := by
  rw [weighted_logD_divisor_sum m n j (by have := hj.pos; omega)]
  apply sum_nonneg
  intro i hi
  split_ifs with hd
  · have ht : Odd (j/(i+1)) := hj.of_dvd_nat (Nat.div_dvd_of_dvd hd)
    obtain ⟨a,ha⟩ := ht
    rw [ha]
    have he : 2*a+1-1=2*a := by omega
    rw [he,pow_mul]
    norm_num
    positivity
  · exact le_rfl

#print axioms weighted_logD_divisor_sum
#print axioms weighted_logD_odd_nonnegative
end BBFMKernel
