import BBFM.Denominator.EdgeTwentyEight
import BBFM.Denominator.MomentSaddles
import BBFM.Denominator.Analytic.LinearEdge

/-! Strict eventual denominator log-concavity at logarithmic cutoff 10^8. -/

noncomputable section
namespace BBFMMoment
open Polynomial Real DenominatorResearch BBFMRelative
set_option maxRecDepth 10000

/-- The entire lower half is log-concave at the explicit logarithmic cutoff. -/
theorem den_lower_half_strict (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hmid : 2 * k ≤ (den n).natDegree)
    (hlarge : (10 : ℕ) ^ 8 ≤ Nat.log 2 n + 1) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) < (den n).coeff k ^ 2 := by
  have hn2 : 2 ≤ n := by
    by_contra hh
    have heq : n=1 := by omega
    subst n
    norm_num at hlarge
  by_cases he : 28*k ≤ Nat.log 2 n+1
  · exact BBFM28.den_linear_edge_strict n k (by omega) hk he
  have htR : (10 : ℝ)^8 ≤ ((Nat.log 2 n+1 : ℕ) : ℝ) := by exact_mod_cast hlarge
  have heR : ((Nat.log 2 n+1 : ℕ) : ℝ) < 28*(k : ℝ) := by
    exact_mod_cast (Nat.lt_of_not_ge he)
  have hmidR : (k : ℝ) ≤ ((den n).natDegree : ℝ) / 2 := by
    have hh : 2 * (k : ℝ) ≤ ((den n).natDegree : ℝ) := by exact_mod_cast hmid
    linarith
  obtain ⟨r, hr, hrone, hmean⟩ := den_exists_saddle_radius n k
    (by exact_mod_cast (show 0 < k by omega)) hmidR
  have hkd : k + 1 ≤ (den n).natDegree := by omega
  by_cases hrhalf : r ≤ 1 / 2
  · have hpar := den_small_radius_parameters n r hn hr.le hrhalf
    dsimp only at hpar
    rw [hmean] at hpar
    have hN : 12*(10 : ℝ)^6 ≤ 14*(((Nat.log 2 n+1 : ℕ) : ℝ)*r) := by
      have hh := hpar.1
      push_cast at heR htR
      nlinarith only [heR,htR,hh]
    exact (BBFMMoment.den_logconcave_of_small_saddle n k r hn hk hkd hr hrhalf hmean hN)
  · have hrlarge : 1 / 2 < r := lt_of_not_ge hrhalf
    obtain ⟨hL, hLn, _⟩ := effectiveScale_bounds n r hn hrlarge hrone
    have hcover := effective_size_covers_unit n (effectiveScale n r) hn hL hLn
    have hN : 12*(10 : ℝ)^6 ≤
        (1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) * effectiveScale n r := by
      have hc : 12*(10 : ℝ)^6 ≤ (10 : ℝ)^8 / 2 := by norm_num
      linarith
    exact (BBFMMoment.den_logconcave_of_large_saddle n k r hn hk hkd hrlarge hrone hmean hN)

/-- Every internal index is strictly log-concave at the new explicit cutoff10^8. -/
theorem den_strict (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hkd : k < (den n).natDegree)
    (hlarge : (10 : ℕ)^8 ≤ Nat.log 2 n+1) :
    (den n).coeff (k-1)*(den n).coeff (k+1) < (den n).coeff k^2 := by
  by_cases hmid : 2*k ≤ (den n).natDegree
  · exact den_lower_half_strict n k hn hk hmid hlarge
  · let j := (den n).natDegree-k
    have hj : 1 ≤ j := by dsimp [j]; omega
    have hjmid : 2*j ≤ (den n).natDegree := by dsimp [j]; omega
    have hh := den_lower_half_strict n j hn hj hjmid hlarge
    have hl := den_coeff_reflect n (k+1) (by omega)
    have hc := den_coeff_reflect n k (by omega)
    have hr := den_coeff_reflect n (k-1) (by omega)
    have hej : j-1 = (den n).natDegree-(k+1) := by dsimp [j]; omega
    have her : j+1 = (den n).natDegree-(k-1) := by dsimp [j]; omega
    rw [hej,her,hl,hr] at hh
    change _ < (den n).coeff ((den n).natDegree-k)^2 at hh
    rw [hc] at hh
    simpa only [mul_comm] using hh

#print axioms BBFMMoment.den_strict
end BBFMMoment
