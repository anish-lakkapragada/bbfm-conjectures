import BBFM.Denominator.MomentEventual
import BBFM.Denominator.RelativeSourceInterior

/-! Strict log-concavity is asserted only at internal indices, and only at the
explicit eventual cutoff10^8. This does not prove the four-exception classification. -/
noncomputable section
namespace BBFMMoment
open Polynomial DenominatorBridge BBFMRelative

theorem source_den_strict (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hkd : k < (denReduced n).natDegree)
    (hlarge : (10 : ℕ)^8 ≤ Nat.log 2 n+1) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) <
      (denReduced n).coeff k^2 := by
  have hh := den_strict n k (by omega) hk
    (by rwa [source_degree_eq_product n hn] at hkd) hlarge
  change (productR n).coeff (k-1)*(productR n).coeff (k+1) <
    (productR n).coeff k^2 at hh
  rw [← denReduced_coeff_real n (k-1) hn, ← denReduced_coeff_real n (k+1) hn,
    ← denReduced_coeff_real n k hn] at hh
  exact_mod_cast hh

/-- Above n≥2^E, E≥10^8, all internal source coefficients are strictly log-concave. -/
theorem source_den_strict_of_pow_le (n k E : ℕ) (hk : 1 ≤ k)
    (hkd : k < (denReduced n).natDegree)
    (hE : (10 : ℕ)^8 ≤ E) (hlarge : 2^E ≤ n) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) <
      (denReduced n).coeff k^2 := by
  have hn : 0 < n := lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) E) hlarge
  apply source_den_strict n k (by omega) hk hkd
  have hh := Nat.le_log_of_pow_le (by decide : 1 < 2) hlarge
  exact hE.trans (hh.trans (Nat.le_succ _))

theorem source_den_eventually_strict :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
      k < (denReduced n).natDegree →
      (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) <
        (denReduced n).coeff k^2 := by
  refine ⟨2^((10 : ℕ)^8), ?_⟩
  intro n hn k hk hkd
  exact source_den_strict_of_pow_le n k _ hk hkd le_rfl hn

/-- The exact source inequality at every positive index, including beyond support. -/
theorem source_den_logconcave_of_pow_le (n k E : ℕ) (hk : 1 ≤ k)
    (hE : (10 : ℕ)^8 ≤ E) (hlarge : 2^E ≤ n) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) ≤
      (denReduced n).coeff k^2 := by
  by_cases hkd : k < (denReduced n).natDegree
  · exact (source_den_strict_of_pow_le n k E hk hkd hE hlarge).le
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (denReduced n).natDegree < k+1),mul_zero]
    positivity

#print axioms BBFMMoment.source_den_logconcave_of_pow_le
#print axioms BBFMMoment.source_den_strict
#print axioms BBFMMoment.source_den_strict_of_pow_le
#print axioms BBFMMoment.source_den_eventually_strict
end BBFMMoment
