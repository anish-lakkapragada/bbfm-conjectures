import BBFM.Denominator.Analytic.SmallSaddle
import BBFM.Denominator.Analytic.Parameters
import BBFM.Denominator.Analytic.Symmetry

noncomputable section
namespace DenominatorResearch
open Finset Polynomial Real

lemma tiltedMean_unit_lower (m : ℕ → ℕ) (n : ℕ) (r : ℝ) (hn : 0 < n) (hr : 0 ≤ r) :
    (m 1 : ℝ) * r / (1 + r) ≤ tiltedMean m n r := by
  have h := Finset.single_le_sum (s := range n)
    (f := fun i : ℕ => (m (i + 1) : ℝ) * ((i : ℝ) + 1) * r ^ (i + 1) / (1 + r ^ (i + 1)))
    (fun i _ => by positivity) (show 0 ∈ range n by simpa using hn)
  simpa only [Nat.cast_zero, zero_add, mul_one, pow_one] using! h

lemma den_degree_ge_log (n : ℕ) (hn : 0 < n) : Nat.log 2 n + 1 ≤ (den n).natDegree := by
  rw [den, weightedProduct_natDegree]
  have h := Finset.single_le_sum (s := range n)
    (f := fun i : ℕ => (Nat.log 2 (n / (i + 1)) + 1) * (i + 1))
    (fun i _ => Nat.zero_le _) (show 0 ∈ range n by simpa using hn)
  simpa only [zero_add, Nat.div_one, mul_one] using h

/-- A coefficient no larger than one third of the unit multiplicity has a radius <=1/2. -/
theorem den_exists_small_saddle (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hsize : 3 * k ≤ Nat.log 2 n + 1) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧
      tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ) := by
  let m := fun i => Nat.log 2 (n / i) + 1
  have hcont : ContinuousOn (tiltedMean m n) (Set.Icc 0 (1 / 2)) :=
    (tiltedMean_continuousOn m n).mono (by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)
  have hhalf := tiltedMean_unit_lower m n (1 / 2) hn (by norm_num)
  have hm1 : m 1 = Nat.log 2 n + 1 := by simp [m]
  rw [hm1] at hhalf
  have hs : 3 * (k : ℝ) ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by exact_mod_cast hsize
  have hmid : (k : ℝ) ≤ tiltedMean m n (1 / 2) := by norm_num at hhalf; push_cast at hs; linarith
  have hzero : tiltedMean m n 0 ≤ (k : ℝ) := by rw [tiltedMean_zero]; positivity
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1 / 2) hcont ⟨hzero, hmid⟩
  refine ⟨r, ?_, hr.2, heq⟩
  by_contra h
  have hr0 : r = 0 := le_antisymm (le_of_not_gt h) hr.1
  subst r
  rw [tiltedMean_zero] at heq
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  linarith

/-- An unconditional linear logarithmic edge range for the true denominator at an explicit
very large cutoff. Every analytic hypothesis has been discharged; no shape interface remains. -/
theorem den_linear_edge_logconcave (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hsize : 3 * k ≤ Nat.log 2 n + 1)
    (hlarge : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ Nat.log 2 n + 1) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  by_cases he : 6 * k ^ 2 ≤ Nat.log 2 n + 1
  · exact den_edge_logconcave n k hn hk he
  have htR : 100 * ((10 : ℝ) ^ 100) ^ 2 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by exact_mod_cast hlarge
  have heR : ((Nat.log 2 n + 1 : ℕ) : ℝ) < 6 * (k : ℝ) ^ 2 := by
    exact_mod_cast (Nat.lt_of_not_ge he)
  have hklarge := effective_parameter_coverage ((Nat.log 2 n + 1 : ℕ) : ℝ) (k : ℝ)
    ((10 : ℝ) ^ 100) (by positivity) htR heR (by positivity)
  obtain ⟨r, hr, hrhalf, hmean⟩ := den_exists_small_saddle n k hn hk hsize
  have hpar := den_small_radius_parameters n r hn hr.le hrhalf
  dsimp only at hpar
  rw [hmean] at hpar
  have hN : (10 : ℝ) ^ 100 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * r := by linarith [hpar.1]
  have hD := den_degree_ge_log n hn
  have hkd : k + 1 ≤ (den n).natDegree := by omega
  exact (den_logconcave_of_small_saddle n k r hn hk hkd hr hrhalf hmean hN).le

/-- Exponent-parameter form of the direct threshold. Keeping E as a parameter avoids asking
Lean to evaluate the gigantic closed numeral 2^(10^202). -/
theorem den_linear_edge_logconcave_of_pow_le (n k E : ℕ)
    (hk : 1 ≤ k) (hsize : 3 * k ≤ Nat.log 2 n + 1)
    (hE : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ E) (hlarge : 2 ^ E ≤ n) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) E) hlarge
  apply den_linear_edge_logconcave n k hn hk hsize
  have hh := Nat.le_log_of_pow_le (by decide : 1 < 2) hlarge
  exact hE.trans (hh.trans (Nat.le_succ _))

/-- The stronger compiled edge range also holds at the upper end of the actual polynomial. -/
theorem den_upper_linear_edge_logconcave (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hsize : 3 * k ≤ Nat.log 2 n + 1)
    (hlarge : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ Nat.log 2 n + 1) :
    (den n).coeff ((den n).natDegree - k - 1) *
      (den n).coeff ((den n).natDegree - k + 1) ≤
      (den n).coeff ((den n).natDegree - k) ^ 2 := by
  have hD := den_degree_ge_log n hn
  have hkd : k + 1 ≤ (den n).natDegree := by omega
  have hleft := den_coeff_reflect n (k + 1) hkd
  have hright := den_coeff_reflect n (k - 1) (by omega)
  have hcenter := den_coeff_reflect n k (by omega)
  have heq : (den n).natDegree - (k - 1) = (den n).natDegree - k + 1 := by omega
  rw [heq] at hright
  rw [← Nat.sub_add_eq, hleft, hright, hcenter, mul_comm]
  exact den_linear_edge_logconcave n k hn hk hsize hlarge

end DenominatorResearch
