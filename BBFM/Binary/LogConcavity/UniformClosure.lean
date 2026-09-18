import BBFM.Binary.LogConcavity.LocalToTP2
import BBFM.Binary.Unimodality.BinomialSmoothing

open Polynomial Finset BinaryShape BBFMCombinatorics
namespace BinaryLC

theorem shape_positive (P : ℤ[X]) (d : ℕ) (h : HasShape P d)
    (hzero : 0 < P.coeff 0) (k : ℕ) (hk : k ≤ d) : 0 < P.coeff k := by
  have hlo : ∀ j, 2 * j ≤ d → 0 < P.coeff j := by
    intro j hj
    induction j with
    | zero => exact hzero
    | succ j ih => exact lt_of_lt_of_le (ih (by omega)) (h.mono j (by omega))
  by_cases hhalf : 2 * k ≤ d
  · exact hlo k hhalf
  · rw [h.symm k hk]
    exact hlo _ (by omega)

theorem real_polynomial_TP2 (P : ℝ[X]) (d : ℕ)
    (hsupport : ∀ k, d < k → P.coeff k = 0)
    (hpos : ∀ k, k ≤ d → 0 < P.coeff k)
    (hlc : ∀ k, 1 ≤ k → P.coeff (k - 1) * P.coeff (k + 1) ≤ P.coeff k ^ 2) :
    TP2 (coeffZ P) := by
  apply TP2_of_positive_interval (coeffZ P) d
  · intro z
    by_cases hz : 0 ≤ z
    · rw [coeffZ, if_pos hz]
      by_cases hzd : z.toNat ≤ d
      · exact (hpos _ hzd).le
      · rw [hsupport _ (by omega)]
    · rw [coeffZ_neg P (by omega)]
  · intro z hz
    rcases hz with hz | hz
    · exact coeffZ_neg P hz
    · have hz0 : 0 ≤ z := by omega
      rw [coeffZ, if_pos hz0, hsupport _ (by omega)]
  · intro k hk
    rw [coeffZ_nat]
    exact hpos k hk
  · intro k hk
    simp only [coeffZ_nat]
    exact hlc k hk

/-- Ordinary uniform convolution preserves adjacent log-concavity on a
positive finite support interval. The LC premise is explicit. -/
theorem logconcave_mul_uniform (P : ℤ[X]) (d L : ℕ)
    (hsupport : ∀ k, d < k → P.coeff k = 0)
    (hpos : ∀ k, k ≤ d → 0 < P.coeff k)
    (hlc : ∀ k, 1 ≤ k → P.coeff (k - 1) * P.coeff (k + 1) ≤ P.coeff k ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (P * uniform L).coeff (k - 1) * (P * uniform L).coeff (k + 1) ≤
      (P * uniform L).coeff k ^ 2 := by
  let Pr := P.map (Int.castRingHom ℝ)
  have hc (j : ℕ) : Pr.coeff j = (P.coeff j : ℝ) := by simp [Pr]
  have hTP : TP2 (coeffZ Pr) := by
    apply real_polynomial_TP2 Pr d
    · intro j hj
      rw [hc, hsupport j hj]
      norm_num
    · intro j hj
      rw [hc]
      exact_mod_cast hpos j hj
    · intro j hj
      rw [hc, hc, hc]
      exact_mod_cast hlc j hj
  have hprod := coeffZ_TP2_mul hTP (intervalPoly_TP2 L)
  have h := TP2_logConcave hprod (k : ℤ)
  have hkm : (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) := by omega
  have hkp : (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) := by omega
  rw [hkm, hkp, coeffZ_nat, coeffZ_nat, coeffZ_nat] at h
  have hm : (P * uniform L).map (Int.castRingHom ℝ) = Pr * intervalPoly L := by
    simp [Pr, uniform, intervalPoly, Polynomial.map_mul, Polynomial.map_sum]
  rw [← hm] at h
  simp only [Polynomial.coeff_map] at h
  change ((P * uniform L).coeff (k - 1) : ℝ) * ((P * uniform L).coeff (k + 1) : ℝ) ≤
    ((P * uniform L).coeff k : ℝ) ^ 2 at h
  exact_mod_cast h

theorem logconcave_uniform_mul (P : ℤ[X]) (d L : ℕ)
    (hsupport : ∀ k, d < k → P.coeff k = 0)
    (hpos : ∀ k, k ≤ d → 0 < P.coeff k)
    (hlc : ∀ k, 1 ≤ k → P.coeff (k - 1) * P.coeff (k + 1) ≤ P.coeff k ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (uniform L * P).coeff (k - 1) * (uniform L * P).coeff (k + 1) ≤
      (uniform L * P).coeff k ^ 2 := by
  simpa only [mul_comm] using logconcave_mul_uniform P d L hsupport hpos hlc k hk

end BinaryLC

#print axioms BinaryLC.logconcave_mul_uniform
