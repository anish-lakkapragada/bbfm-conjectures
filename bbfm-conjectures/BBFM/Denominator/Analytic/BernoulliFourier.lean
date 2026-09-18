import BBFM.Denominator.Analytic.FourierEnergy

noncomputable section
namespace DenominatorResearch
open Finset Real Complex

/-- Characteristic factor of a Bernoulli variable, written in real trigonometric coordinates. -/
def bernoulliChar (p θ : ℝ) : ℂ :=
  (1 - p : ℝ) + (p : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)

lemma bernoulliChar_norm_sq (p θ : ℝ) :
    ‖bernoulliChar p θ‖ ^ 2 = 1 - 4 * p * (1 - p) * Real.sin (θ / 2) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [bernoulliChar, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have h1 := Real.sin_sq_add_cos_sq θ
  have h2 := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at h2
  linear_combination p ^ 2 * h1 + 4 * p * (1 - p) * h2

/-- The elementary exponential bound used in the global Fourier tail estimate. -/
theorem bernoulliChar_norm_le (p θ : ℝ) :
    ‖bernoulliChar p θ‖ ≤ Real.exp (-2 * p * (1 - p) * Real.sin (θ / 2) ^ 2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).mp
  rw [bernoulliChar_norm_sq, ← Real.exp_nat_mul]
  have h := Real.add_one_le_exp (((2 : ℕ) : ℝ) * (-2 * p * (1 - p) * Real.sin (θ / 2) ^ 2))
  nlinarith [h]

/-- Norm decay for an arbitrary finite collection of weighted Bernoulli factors. -/
theorem bernoulliProduct_norm_le {α : Type*} (s : Finset α) (m : α → ℕ) (p w : α → ℝ) (θ : ℝ) :
    ‖∏ i ∈ s, (bernoulliChar (p i) (w i * θ)) ^ m i‖ ≤
      Real.exp (-2 * ∑ i ∈ s, (m i : ℝ) * p i * (1 - p i) * Real.sin (w i * θ / 2) ^ 2) := by
  rw [norm_prod]
  have h : (∏ i ∈ s, ‖bernoulliChar (p i) (w i * θ) ^ m i‖) ≤
      ∏ i ∈ s, Real.exp (-2 * (m i : ℝ) * p i * (1 - p i) * Real.sin (w i * θ / 2) ^ 2) := by
    apply prod_le_prod
    · intro i hi; positivity
    · intro i hi
      rw [norm_pow]
      have hh := pow_le_pow_left₀ (norm_nonneg _) (bernoulliChar_norm_le (p i) (w i * θ)) (m i)
      rw [← Real.exp_nat_mul] at hh
      convert hh using 1
      congr 1
      ring
  refine h.trans_eq ?_
  rw [← Real.exp_sum]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  ring

end DenominatorResearch
