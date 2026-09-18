import BBFM.Denominator.Analytic.FourierCoefficient
import BBFM.Denominator.Analytic.SaddleRadius

noncomputable section
namespace DenominatorResearch
open Finset Polynomial Real Complex intervalIntegral

lemma weightedProduct_eval_pos (m : ℕ → ℕ) (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    0 < (weightedProduct m n).eval r := by
  unfold weightedProduct
  rw [Polynomial.eval_prod]
  apply prod_pos
  intro i hi
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X]
  positivity

lemma eval_centered_re (P : ℝ[X]) (r θ : ℝ) (k : ℕ) :
    (P.eval₂ Complex.ofRealHom ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I)).re =
    cosineSum (fun i => P.coeff i * r ^ i) P.natDegree k θ := by
  rw [Polynomial.eval₂_eq_sum_range, sum_mul, Complex.re_sum]
  unfold cosineSum
  apply sum_congr rfl
  intro i hi
  have he : Complex.exp ((θ : ℂ) * Complex.I) ^ i *
      Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I) =
      Complex.exp ((((i : ℝ) - k) * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [mul_pow]
  push_cast at he
  have heq : Complex.ofRealHom (P.coeff i) *
      ((r : ℂ) ^ i * Complex.exp ((θ : ℂ) * Complex.I) ^ i) *
        Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I) =
      ((P.coeff i * r ^ i : ℝ) : ℂ) *
        Complex.exp ((((i : ℝ) - k) * θ : ℝ) * Complex.I) := by
    change (P.coeff i : ℂ) * ((r : ℂ) ^ i * Complex.exp ((θ : ℂ) * Complex.I) ^ i) *
      Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I) = _
    push_cast
    rw [show (P.coeff i : ℂ) * ((r : ℂ) ^ i * Complex.exp ((θ : ℂ) * Complex.I) ^ i) *
        Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I) =
        (P.coeff i : ℂ) * (r : ℂ) ^ i * (Complex.exp ((θ : ℂ) * Complex.I) ^ i *
          Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I)) by ring]
    rw [he]
  rw [heq, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hexpre : (Complex.exp ((((i : ℝ) - k) * θ : ℝ) * Complex.I)).re =
      Real.cos (((i : ℝ) - k) * θ) := by simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  rw [hexpre]

/-- Explicit centered characteristic function of the concrete denominator. -/
def centeredDenChar (n k : ℕ) (r θ : ℝ) : ℂ :=
  denChar n r θ * Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I)

/-- Exact bridge to the finite cosine coefficient sum. -/
theorem centeredDenChar_re (n k : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    (centeredDenChar n k r θ).re =
      cosineSum (fun i => (den n).coeff i * r ^ i) (den n).natDegree k θ / (den n).eval r := by
  unfold centeredDenChar
  rw [denChar_eq_eval n r θ hr]
  rw [div_mul_eq_mul_div, Complex.div_ofReal_re, eval_centered_re]

lemma centeredDenChar_even_re (n k : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    (centeredDenChar n k r (-θ)).re = (centeredDenChar n k r θ).re := by
  rw [centeredDenChar_re n k r (-θ) hr, centeredDenChar_re n k r θ hr]
  congr 1
  unfold cosineSum
  simp only [mul_neg, Real.cos_neg]

/-- The actual coefficient inequality follows from the sign of its centered Fourier integral.
This reduction has a genuine analytic hypothesis; it is not the eventual-family theorem. -/
theorem den_turan_of_centered_fourier_positive (n k : ℕ) (r : ℝ) (hr : 0 < r)
    (hk : 1 ≤ k) (hkd : k + 1 ≤ (den n).natDegree)
    (hI : 0 < ∫ θ in -Real.pi..Real.pi,
      (centeredDenChar n k r θ).re * (1 - Real.cos θ)) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) < (den n).coeff k ^ 2 := by
  let a : ℕ → ℝ := fun i => (den n).coeff i * r ^ i
  have hP : 0 < (den n).eval r := weightedProduct_eval_pos _ _ r hr.le
  have hI' : 0 < ∫ θ in -Real.pi..Real.pi,
      cosineSum a (den n).natDegree k θ * (1 - Real.cos θ) := by
    simp_rw [centeredDenChar_re n k r _ hr.le, div_mul_eq_mul_div] at hI
    rw [integral_div] at hI
    exact (div_pos_iff_of_pos_right hP).mp hI
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    exact mul_nonneg (weightedProduct_nonneg _ _ i) (pow_nonneg hr.le i)
  have ht := turan_of_positive_fourier_second_difference a (den n).natDegree k ha hk hkd hI'
  have hl : a (k - 1) * a (k + 1) =
      ((den n).coeff (k - 1) * (den n).coeff (k + 1)) * r ^ (2 * k) := by
    dsimp [a]
    rw [show (den n).coeff (k - 1) * r ^ (k - 1) * ((den n).coeff (k + 1) * r ^ (k + 1)) =
      ((den n).coeff (k - 1) * (den n).coeff (k + 1)) * (r ^ (k - 1) * r ^ (k + 1)) by ring]
    rw [← pow_add, show k - 1 + (k + 1) = 2 * k by omega]
  have hc : a k ^ 2 = (den n).coeff k ^ 2 * r ^ (2 * k) := by
    dsimp [a]
    rw [mul_pow, ← pow_mul]
    congr 2
    omega
  rw [hl, hc] at ht
  exact (mul_lt_mul_iff_of_pos_right (pow_pos hr _)).mp ht

end DenominatorResearch
