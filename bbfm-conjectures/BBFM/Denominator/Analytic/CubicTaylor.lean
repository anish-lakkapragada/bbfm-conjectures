import Mathlib

noncomputable section
namespace DenominatorResearch
open Set Complex

/-- A deliberately loose cubic Taylor estimate, sufficient for the quantitative Fourier bound.
It is proved by three applications of the vector-valued mean-value inequality. -/
theorem cubic_taylor_bound (f₀ f₁ f₂ f₃ : ℝ → ℂ) (T M : ℝ) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (h₀ : ∀ u ∈ Icc 0 T, HasDerivAt f₀ (f₁ u) u)
    (h₁ : ∀ u ∈ Icc 0 T, HasDerivAt f₁ (f₂ u) u)
    (h₂ : ∀ u ∈ Icc 0 T, HasDerivAt f₂ (f₃ u) u)
    (h₃ : ∀ u ∈ Icc 0 T, ‖f₃ u‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 T) :
    ‖f₀ θ - f₀ 0 - (θ : ℂ) * f₁ 0 - ((θ : ℂ) ^ 2 / 2) * f₂ 0‖ ≤ M * θ ^ 3 := by
  have hsub : ∀ u ∈ Icc (0 : ℝ) θ, u ∈ Icc (0 : ℝ) T :=
    fun u hu => ⟨hu.1, hu.2.trans hθ.2⟩
  have hb₂ : ∀ u ∈ Icc (0 : ℝ) θ, ‖f₂ u - f₂ 0‖ ≤ M * u := by
    intro u hu
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x (hx : x ∈ Icc (0 : ℝ) θ) => (h₂ x (hsub x hx)).hasDerivWithinAt)
      (fun x (hx : x ∈ Ico (0 : ℝ) θ) => h₃ x (hsub x ⟨hx.1, hx.2.le⟩)) u hu
    simpa only [sub_zero] using hh
  let F₁ : ℝ → ℂ := fun u => f₁ u - f₁ 0 - (u : ℂ) * f₂ 0
  have hF₁ : ∀ u ∈ Icc (0 : ℝ) θ, HasDerivAt F₁ (f₂ u - f₂ 0) u := by
    intro u hu
    have hh := ((h₁ u (hsub u hu)).sub_const (f₁ 0)).sub
      (((hasDerivAt_id u).ofReal_comp).mul_const (f₂ 0))
    simpa only [Complex.ofReal_one, one_mul] using! hh
  have hb₁ : ∀ u ∈ Icc (0 : ℝ) θ, ‖F₁ u‖ ≤ M * θ * u := by
    intro u hu
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun x (hx : x ∈ Icc (0 : ℝ) θ) => (hF₁ x hx).hasDerivWithinAt)
      (fun x (hx : x ∈ Ico (0 : ℝ) θ) => (hb₂ x ⟨hx.1, hx.2.le⟩).trans
        (mul_le_mul_of_nonneg_left hx.2.le hM)) u hu
    simpa [F₁] using hh
  let F₀ : ℝ → ℂ := fun u => f₀ u - f₀ 0 - (u : ℂ) * f₁ 0 - ((u : ℂ) ^ 2 / 2) * f₂ 0
  have hF₀ : ∀ u ∈ Icc (0 : ℝ) θ, HasDerivAt F₀ (F₁ u) u := by
    intro u hu
    have hcast := (hasDerivAt_id u).ofReal_comp
    have hh := (((h₀ u (hsub u hu)).sub_const (f₀ 0)).sub (hcast.mul_const (f₁ 0))).sub
      (((hcast.pow 2).div_const 2).mul_const (f₂ 0))
    dsimp [F₀, F₁]
    convert! hh using 1 <;> simp only [id_eq, Complex.ofReal_one] <;> ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (hx : x ∈ Icc (0 : ℝ) θ) => (hF₀ x hx).hasDerivWithinAt)
    (fun x (hx : x ∈ Ico (0 : ℝ) θ) => (hb₁ x ⟨hx.1, hx.2.le⟩).trans
      (mul_le_mul_of_nonneg_left hx.2.le (mul_nonneg hM hθ.1))) θ ⟨hθ.1, le_rfl⟩
  simpa [F₀, pow_succ, mul_assoc] using hh

end DenominatorResearch
