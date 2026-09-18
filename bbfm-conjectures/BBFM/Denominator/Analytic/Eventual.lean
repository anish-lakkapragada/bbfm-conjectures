import BBFM.Denominator.Analytic.LargeSaddle
import BBFM.Denominator.Analytic.LinearEdge

noncomputable section
namespace DenominatorResearch
open Polynomial Real

/-- The entire lower half is log-concave at the explicit logarithmic cutoff. -/
theorem den_lower_half_logconcave (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hmid : 2 * k ≤ (den n).natDegree)
    (hlarge : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ Nat.log 2 n + 1) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  by_cases he : 6 * k ^ 2 ≤ Nat.log 2 n + 1
  · exact den_edge_logconcave n k hn hk he
  have htR : 100 * ((10 : ℝ) ^ 100) ^ 2 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) := by exact_mod_cast hlarge
  have heR : ((Nat.log 2 n + 1 : ℕ) : ℝ) < 6 * (k : ℝ) ^ 2 := by
    exact_mod_cast (Nat.lt_of_not_ge he)
  have hklarge := effective_parameter_coverage ((Nat.log 2 n + 1 : ℕ) : ℝ) (k : ℝ)
    ((10 : ℝ) ^ 100) (by positivity) htR heR (by positivity)
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
    have hN : (10 : ℝ) ^ 100 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * r := by linarith [hpar.1]
    exact (den_logconcave_of_small_saddle n k r hn hk hkd hr hrhalf hmean hN).le
  · have hrlarge : 1 / 2 < r := lt_of_not_ge hrhalf
    obtain ⟨hL, hLn, _⟩ := effectiveScale_bounds n r hn hrlarge hrone
    have hcover := effective_size_covers_unit n (effectiveScale n r) hn hL hLn
    have hN : (10 : ℝ) ^ 100 ≤
        (1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) * effectiveScale n r := by
      have hc : (10 : ℝ) ^ 100 ≤ 100 * ((10 : ℝ) ^ 100) ^ 2 / 2 := by norm_num
      linarith
    exact (den_logconcave_of_large_saddle n k r hn hk hkd hrlarge hrone hmean hN).le

/-- Full coefficientwise log-concavity of the actual denominator at an explicit cutoff.
No analytic, coefficient-shape, or log-concavity hypothesis remains. -/
theorem den_logconcave (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hlarge : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ Nat.log 2 n + 1) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  by_cases hkd : k + 1 ≤ (den n).natDegree
  · by_cases hmid : 2 * k ≤ (den n).natDegree
    · exact den_lower_half_logconcave n k hn hk hmid hlarge
    · let j := (den n).natDegree - k
      have hj : 1 ≤ j := by dsimp [j]; omega
      have hjmid : 2 * j ≤ (den n).natDegree := by dsimp [j]; omega
      have hh := den_lower_half_logconcave n j hn hj hjmid hlarge
      have hl := den_coeff_reflect n (k + 1) hkd
      have hc := den_coeff_reflect n k (by omega)
      have hr := den_coeff_reflect n (k - 1) (by omega)
      have hej : j - 1 = (den n).natDegree - (k + 1) := by dsimp [j]; omega
      have her : j + 1 = (den n).natDegree - (k - 1) := by dsimp [j]; omega
      rw [hej, her, hl, hr] at hh
      change _ ≤ (den n).coeff ((den n).natDegree - k) ^ 2 at hh
      rw [hc] at hh
      simpa only [mul_comm] using hh
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (den n).natDegree < k + 1), mul_zero]
    exact sq_nonneg _

/-- Exponent form: every n >= 2^E has its entire coefficient sequence log-concave,
provided E >= 10^202. E is symbolic so the closed power of two is never evaluated. -/
theorem den_logconcave_of_pow_le (n k E : ℕ) (hk : 1 ≤ k)
    (hE : 100 * ((10 : ℕ) ^ 100) ^ 2 ≤ E) (hlarge : 2 ^ E ≤ n) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) E) hlarge
  apply den_logconcave n k hn hk
  have hh := Nat.le_log_of_pow_le (by decide : 1 < 2) hlarge
  exact hE.trans (hh.trans (Nat.le_succ _))

/-- A full infinite-family theorem, with a single cutoff valid for every coefficient. -/
theorem den_eventually_logconcave :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
      (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  refine ⟨2 ^ (100 * ((10 : ℕ) ^ 100) ^ 2), ?_⟩
  intro n hn k hk
  exact den_logconcave_of_pow_le n k _ hk le_rfl hn

end DenominatorResearch
