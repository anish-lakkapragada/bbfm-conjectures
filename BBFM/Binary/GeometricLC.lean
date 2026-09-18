import BBFM.Binary.GeometricBoundary

open Polynomial Finset BinaryShape BinaryLC
namespace BinaryResearch

def CoeffLogConcave (P : ℤ[X]) : Prop :=
  ∀ k : ℕ, 1 ≤ k → P.coeff (k - 1) * P.coeff (k + 1) ≤ P.coeff k ^ 2

lemma logconcave_of_symmetric_lower (P : ℤ[X]) (c : ℕ)
    (hsupport : ∀ k, 2 * c < k → P.coeff k = 0)
    (hsymm : ∀ k, k ≤ 2 * c → P.coeff k = P.coeff (2 * c - k))
    (hlower : ∀ k, 1 ≤ k → k ≤ c → P.coeff (k - 1) * P.coeff (k + 1) ≤ P.coeff k ^ 2) :
    CoeffLogConcave P := by
  intro k hk
  by_cases htail : 2 * c ≤ k
  · rw [hsupport (k + 1) (by omega), mul_zero]
    positivity
  · by_cases hlow : k ≤ c
    · exact hlower k hk hlow
    · have h := hlower (2 * c - k) (by omega) (by omega)
      rw [hsymm (k - 1) (by omega), hsymm (k + 1) (by omega), hsymm k (by omega),
        show 2 * c - (k - 1) = 2 * c - k + 1 by omega,
        show 2 * c - (k + 1) = 2 * c - k - 1 by omega, mul_comm]
      exact h

lemma geometric_source_degree_le (m : ℕ) :
    (jump m * numB (2 * m)).natDegree ≤ 2 * center (2 * m + 2) := by
  have hc := center_step m
  have hq := jumpLength_two_le m
  calc
    _ ≤ (jump m).natDegree + (numB (2 * m)).natDegree := natDegree_mul_le
    _ ≤ (2 * jumpLength m - 2) + 2 * center (2 * m) := by
      rw [jump_natDegree]
      exact Nat.add_le_add_left (numB_natDegree_le _) _
    _ = _ := by omega

lemma geometric_source_support (m k : ℕ) (hk : 2 * center (2 * m + 2) < k) :
    (jump m * numB (2 * m)).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((geometric_source_degree_le m).trans_lt hk)

lemma geometric_source_symmetry (m k : ℕ) (hk : k ≤ 2 * center (2 * m + 2)) :
    (jump m * numB (2 * m)).coeff k =
      (jump m * numB (2 * m)).coeff (2 * center (2 * m + 2) - k) := by
  have hj : (jump m).reflect (2 * jumpLength m - 2) = jump m := by
    simpa only [reverse, jump_natDegree] using jump_reverse m
  have hr := reflect_mul (jump m) (numB (2 * m))
    (show (jump m).natDegree ≤ 2 * jumpLength m - 2 by rw [jump_natDegree])
    (numB_natDegree_le _)
  rw [hj, numB_reflect] at hr
  have he : (2 * jumpLength m - 2) + 2 * center (2 * m) = 2 * center (2 * m + 2) := by
    have hc := center_step m
    have hq := jumpLength_two_le m
    omega
  rw [he] at hr
  have hh := congrArg (fun P : ℤ[X] => P.coeff k) hr
  rw [coeff_reflect, revAt_le hk] at hh
  exact hh.symm

/-- The geometric recurrence summand is fully log-concave once the previous
odd residual is log-concave. The signed central perturbation is absorbed by
the unconditional quantitative unimodality invariant. -/
theorem geometric_source_logconcave (m : ℕ) (hm : 49 ≤ m)
    (hR : CoeffLogConcave (residual (2 * m))) :
    CoeffLogConcave (jump m * numB (2 * m)) := by
  apply logconcave_of_symmetric_lower _ (center (2 * m + 2))
    (geometric_source_support m) (geometric_source_symmetry m)
  intro k hk0 hkhi
  have hc := center_window (2 * m) (by omega)
  by_cases hlow : k < center (2 * m) - 1
  · have hcore := logconcave_uniform_mul (residual (2 * m)) (2 * center (2 * m) - 1)
      (2 * jumpLength m) (residual_support _) (residual_coeff_pos_even m (by omega)) hR k hk0
    have heq (j : ℕ) (hj : j < center (2 * m)) :
        (jump m * numB (2 * m)).coeff j =
          (uniform (2 * jumpLength m) * residual (2 * m)).coeff j := by
      rw [geometric_source_coeff_decomposition, geometricCorrection_coeff_low _ _ hj, add_zero]
    rw [heq (k - 1) (by omega), heq (k + 1) (by omega), heq k (by omega)]
    exact hcore
  · by_cases he : k = center (2 * m) - 1
    · rw [he, show center (2 * m) - 1 - 1 = center (2 * m) - 2 by omega,
        show center (2 * m) - 1 + 1 = center (2 * m) by omega]
      exact geometric_source_lower_boundary_lc m hm hR
    · have halign := center_step m
      have hq := jumpLength_two_le m
      exact source_geometric_central_logconcavity m hm k (by omega) (by omega)

#print axioms geometric_source_logconcave
end BinaryResearch
