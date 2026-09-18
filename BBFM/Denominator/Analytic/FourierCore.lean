import BBFM.Denominator.Analytic.GaussianTail

noncomputable section
namespace DenominatorResearch
open Real intervalIntegral

lemma cosine_weight_bounds (θ : ℝ) (hθ : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    θ ^ 2 / 8 ≤ 1 - Real.cos θ ∧ 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
  have hs0 : 0 ≤ Real.sin (θ / 2) := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hj := Real.mul_le_sin (by linarith : 0 ≤ θ / 2) (by linarith : θ / 2 ≤ Real.pi / 2)
  have hjm := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  have hpne : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at hjm
  have hj2 : θ ^ 2 ≤ Real.pi ^ 2 * Real.sin (θ / 2) ^ 2 := by
    have hh := (sq_le_sq₀ hθ (mul_nonneg Real.pi_pos.le hs0)).mpr (by nlinarith : θ ≤ Real.pi * Real.sin (θ / 2))
    nlinarith
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
  have hh := mul_le_mul_of_nonneg_right hpi2 (sq_nonneg (Real.sin (θ / 2)))
  have hsupper := Real.sin_sq_le_sq (x := θ / 2)
  have hhalf := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hhalf
  constructor <;> nlinarith

lemma scaled_gaussian_second_moment_tail (a c : ℝ) (ha : 0 < a)
    (hc : 100000000 * a ≤ c) :
    (∫ θ in (100000000 * a)..c, θ ^ 2 * Real.exp (-(θ / a) ^ 2 / 10000000000)) < a ^ 3 / 100 := by
  have hu : 100000000 ≤ c / a := (le_div_iff₀ ha).2 hc
  have ht := gaussian_second_moment_tail (c / a) hu
  have hscale := integral_comp_div (fun u : ℝ => u ^ 2 * Real.exp (-u ^ 2 / 10000000000))
    (a := 100000000 * a) (b := c) ha.ne'
  simp only [smul_eq_mul, mul_div_cancel_right₀ _ ha.ne'] at hscale
  have heq : (fun θ : ℝ => θ ^ 2 * Real.exp (-(θ / a) ^ 2 / 10000000000)) =
      fun θ : ℝ => a ^ 2 * ((θ / a) ^ 2 * Real.exp (-(θ / a) ^ 2 / 10000000000)) := by
    funext θ
    field_simp
    <;> ring
  rw [heq, integral_const_mul, hscale]
  have hh := mul_lt_mul_of_pos_left ht (pow_pos ha 3)
  nlinarith

/-- Quantitative Fourier sign criterion from explicit pointwise bounds.
This is a conditional analytic lemma; its local central bounds are not assumed proved for den_n. -/
theorem positive_fourier_core (f : ℝ → ℝ) (hf : Continuous f) (a c δ : ℝ)
    (ha : 0 < a) (hc : 100000000 * a ≤ c) (hcπ : c ≤ Real.pi)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ a ^ 3 / 10000)
    (hinner : ∀ θ ∈ Set.Icc 0 a, 1 / 4 ≤ f θ)
    (hcentral : ∀ θ ∈ Set.Icc 0 (100000000 * a), 0 ≤ f θ)
    (hmiddle : ∀ θ ∈ Set.Icc (100000000 * a) c,
      |f θ| ≤ Real.exp (-(θ / a) ^ 2 / 10000000000))
    (hfar : ∀ θ ∈ Set.Icc c Real.pi, |f θ| ≤ δ) :
    0 < ∫ θ in (0 : ℝ)..Real.pi, f θ * (1 - Real.cos θ) := by
  let g : ℝ → ℝ := fun θ => f θ * (1 - Real.cos θ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hac : a ≤ 100000000 * a := by linarith
  have haπ : a ≤ Real.pi := hac.trans (hc.trans hcπ)
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hi : a ^ 3 / 96 ≤ ∫ θ in (0 : ℝ)..a, g θ := by
    have hh := integral_mono_on (μ := MeasureTheory.volume) ha.le
      ((by fun_prop : Continuous (fun θ : ℝ => θ ^ 2 / 32)).intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
      (fun θ (hθ : θ ∈ Set.Icc (0 : ℝ) a) => ?_)
    · have he : (∫ θ in (0 : ℝ)..a, θ ^ 2 / 32) = a ^ 3 / 96 := by
        rw [integral_div, integral_pow]
        norm_num
        ring
      rwa [he] at hh
    · dsimp [g]
      have hw := cosine_weight_bounds θ hθ.1 (hθ.2.trans haπ)
      have hw0 : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      have hprod := mul_le_mul_of_nonneg_right (hinner θ hθ) hw0
      nlinarith
  have hcentralI : 0 ≤ ∫ θ in a..(100000000 * a), g θ := by
    apply integral_nonneg hac
    intro θ hθ
    exact mul_nonneg (hcentral θ ⟨ha.le.trans hθ.1, hθ.2⟩)
      (sub_nonneg.mpr (Real.cos_le_one θ))
  have hm : -(a ^ 3 / 200) < ∫ θ in (100000000 * a)..c, g θ := by
    have hh := integral_mono_on (μ := MeasureTheory.volume) hc
      ((by fun_prop : Continuous (fun θ : ℝ => -(1 / 2 : ℝ) *
        (θ ^ 2 * Real.exp (-(θ / a) ^ 2 / 10000000000)))).intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
      (fun θ (hθ : θ ∈ Set.Icc (100000000 * a) c) => ?_)
    · rw [integral_const_mul] at hh
      have ht := scaled_gaussian_second_moment_tail a c ha hc
      nlinarith
    · dsimp [g]
      have hθ0 : 0 ≤ θ := le_trans (by positivity) hθ.1
      have hw := cosine_weight_bounds θ hθ0 (hθ.2.trans hcπ)
      have hw0 : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      have hlow := neg_le_of_abs_le (hmiddle θ hθ)
      have hp := mul_le_mul_of_nonneg_right hlow hw0
      have he := mul_le_mul_of_nonneg_left hw.2
        (Real.exp_pos (-(θ / a) ^ 2 / 10000000000)).le
      nlinarith
  have hfarI : -8 * δ ≤ ∫ θ in c..Real.pi, g θ := by
    have hh := integral_mono_on (μ := MeasureTheory.volume) hcπ
      ((continuous_const : Continuous (fun _ : ℝ => -2 * δ)).intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
      (fun θ (hθ : θ ∈ Set.Icc c Real.pi) => ?_)
    · rw [integral_const, smul_eq_mul] at hh
      have h1 := mul_nonneg hc0 hδ
      have h2 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hδ
      nlinarith
    · dsimp [g]
      have hw0 : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      have hw2 : 1 - Real.cos θ ≤ 2 := by linarith [Real.neg_one_le_cos θ]
      have hlow := neg_le_of_abs_le (hfar θ hθ)
      have h1 := mul_le_mul_of_nonneg_right hlow hw0
      have h2 := mul_le_mul_of_nonneg_left hw2 hδ
      nlinarith
  have hs1 := integral_add_adjacent_intervals (μ := MeasureTheory.volume) (hg.intervalIntegrable 0 a)
    (hg.intervalIntegrable a (100000000 * a))
  have hs2 := integral_add_adjacent_intervals (μ := MeasureTheory.volume) (hg.intervalIntegrable 0 (100000000 * a))
    (hg.intervalIntegrable (100000000 * a) c)
  have hs3 := integral_add_adjacent_intervals (μ := MeasureTheory.volume) (hg.intervalIntegrable 0 c)
    (hg.intervalIntegrable c Real.pi)
  change 0 < ∫ θ in (0 : ℝ)..Real.pi, g θ
  nlinarith [pow_pos ha 3]

end DenominatorResearch
