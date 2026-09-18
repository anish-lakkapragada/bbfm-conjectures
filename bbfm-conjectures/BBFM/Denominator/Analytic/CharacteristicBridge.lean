import BBFM.Denominator.Analytic.FourierDecay

noncomputable section
namespace DenominatorResearch
open Finset Polynomial Complex

/-- One tilted Bernoulli factor is its normalized polynomial evaluation on a circle. -/
lemma bernoulliChar_tilt (r θ : ℝ) (i : ℕ) (hr : 0 ≤ r) :
    bernoulliChar (tiltedProbability r i) ((i : ℝ) * θ) =
      (1 + ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ i) /
        (1 + (r : ℂ) ^ i) := by
  have hdR : 1 + r ^ i ≠ 0 := by positivity
  have hd : 1 + (r : ℂ) ^ i ≠ 0 := by exact_mod_cast hdR
  have hphase : Complex.exp ((((i : ℝ) * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) ^ i := by
    push_cast
    rw [mul_assoc, Complex.exp_nat_mul]
  push_cast at hphase
  unfold bernoulliChar tiltedProbability
  push_cast
  rw [← Complex.exp_mul_I, hphase]
  field_simp
  <;> ring

/-- Formal bridge from the finite factor characteristic function to the actual polynomial.
No probabilistic interface or coefficient identity is assumed. -/
theorem weightedBernoulliChar_eq_eval (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    weightedBernoulliChar m (tiltedProbability r) n θ =
      (weightedProduct m n).eval₂ Complex.ofRealHom
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
      (((weightedProduct m n).eval r : ℝ) : ℂ) := by
  unfold weightedBernoulliChar weightedProduct
  simp only [Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X, Complex.ofReal_prod,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one]
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← div_pow]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using bernoulliChar_tilt r θ (i + 1) hr

/-- The Fourier decay proved in this development belongs to the concrete BBFM denominator. -/
theorem denChar_eq_eval (n : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    denChar n r θ =
      (den n).eval₂ Complex.ofRealHom ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) /
        (((den n).eval r : ℝ) : ℂ) := weightedBernoulliChar_eq_eval _ _ _ _ hr

end DenominatorResearch
