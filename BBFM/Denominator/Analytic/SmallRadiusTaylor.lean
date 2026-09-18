import BBFM.Denominator.Analytic.LogProductTaylor
import BBFM.Denominator.Analytic.CenteredFourier

noncomputable section
namespace DenominatorResearch
open Finset Polynomial Complex Real

lemma logProductDeriv_zero (m : ℕ → ℕ) (n : ℕ) (r : ℝ) :
    logProductDeriv m n r 0 = Complex.I * (tiltedMean m n r : ℂ) := by
  unfold logProductDeriv tiltedMean
  push_cast
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  simp only [factorLogDeriv, factorPhase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Nat.cast_add, Nat.cast_one]
  ring

lemma logProductDerivTwo_zero (m : ℕ → ℕ) (n : ℕ) (r : ℝ) :
    logProductDerivTwo m n r 0 = -(tiltedVariance m n r : ℂ) := by
  unfold logProductDerivTwo tiltedVariance
  push_cast
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  simp only [factorLogDerivTwo, factorPhase, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, mul_one, mul_pow, Complex.I_sq, Nat.cast_add, Nat.cast_one]
  ring

lemma factorPhase_eq_pow (r θ : ℝ) (i : ℕ) :
    factorPhase r θ i = ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ i := by
  unfold factorPhase
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

lemma logProduct_exp (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (h : ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r θ i ≠ 0) :
    Complex.exp (logProduct m n r θ) =
      (weightedProduct m n).eval₂ Complex.ofRealHom
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  unfold logProduct weightedProduct
  rw [Complex.exp_sum, Polynomial.eval₂_finsetProd]
  apply prod_congr rfl
  intro i hi
  rw [Complex.exp_nat_mul]
  simp only [factorLog, Complex.exp_log (h (i + 1) (by omega) (by have := mem_range.mp hi; omega)),
    Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X]
  rw [factorPhase_eq_pow]

lemma weightedBernoulliChar_eq_exp_logProduct (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) :
    weightedBernoulliChar m (tiltedProbability r) n θ =
      Complex.exp (logProduct m n r θ - logProduct m n r 0) := by
  have hne : ∀ u i, 1 ≤ i → i ≤ n → 1 + factorPhase r u i ≠ 0 :=
    fun u i hi _ => Complex.slitPlane_ne_zero (factorPhase_slitPlane_small r u i hr hrhalf hi)
  rw [Complex.exp_sub, logProduct_exp m n r θ (hne θ), logProduct_exp m n r 0 (hne 0),
    weightedBernoulliChar_eq_eval m n r θ hr]
  congr 1
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
  push_cast
  rfl

/-- The local exponential/Taylor hypothesis is fully discharged for the actual denominator
at every radius up to one half. -/
theorem den_small_radius_local_taylor (n k : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hθ : 0 ≤ θ)
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ)) :
    ∃ R : ℂ,
      centeredDenChar n k r θ = Complex.exp
        (-((tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r * θ ^ 2 / 2 : ℝ) : ℂ) + R) ∧
      ‖R‖ ≤ 10000 * (((Nat.log 2 n + 1 : ℕ) : ℝ) * r) * θ ^ 3 := by
  let m := fun i => Nat.log 2 (n / i) + 1
  let R := logProduct m n r θ - logProduct m n r 0 -
    (θ : ℂ) * logProductDeriv m n r 0 - ((θ : ℂ) ^ 2 / 2) * logProductDerivTwo m n r 0
  refine ⟨R, ?_, ?_⟩
  · unfold centeredDenChar denChar
    rw [weightedBernoulliChar_eq_exp_logProduct _ n r θ hr hrhalf, ← Complex.exp_add]
    congr 1
    dsimp [R]
    rw [logProductDeriv_zero, logProductDerivTwo_zero]
    change logProduct m n r θ - logProduct m n r 0 + -(k : ℂ) * (θ : ℂ) * Complex.I = _
    have hm : tiltedMean m n r = (k : ℝ) := hmean
    rw [hm]
    push_cast
    ring
  · have hbound := logProduct_small_radius_taylor m n (Nat.log 2 n + 1) r θ hr hrhalf hθ (by
      intro i hi hin
      exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1)
    change ‖R‖ ≤ _ at hbound
    have hp : 0 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) * r * θ ^ 3 := by positivity
    nlinarith

end DenominatorResearch
