import BBFM.Denominator.RefinedScale

noncomputable section
namespace BBFMRefined
open Real intervalIntegral

/-- A Gaussian eighth-moment bound controls the local negative contribution to the Fourier integral. -/
theorem positive_fourier_core (f : ℝ → ℝ) (hf : Continuous f) (a c δ M : ℝ)
    (ha : 0 < a) (hac : a ≤ c) (hcπ : c ≤ Real.pi)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ a^3/10000)
    (hsmall : M^2*a^6 ≤ 1/(10 : ℝ)^10)
    (hinner : ∀ θ ∈ Set.Icc 0 a, 1/4 ≤ f θ)
    (hlocal : ∀ θ ∈ Set.Icc 0 c,
      -(M^2*θ^6*Real.exp (-(θ/a)^2/4)) ≤ f θ)
    (hfar : ∀ θ ∈ Set.Icc c Real.pi, |f θ| ≤ δ) :
    0 < ∫ θ in (0 : ℝ)..Real.pi, f θ*(1-Real.cos θ) := by
  let g : ℝ → ℝ := fun θ => f θ*(1-Real.cos θ)
  let e : ℝ → ℝ := fun θ => θ^8*Real.exp (-(θ/a)^2/4)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have he : Continuous e := by dsimp [e]; fun_prop
  have hc0 : 0 ≤ c := ha.le.trans hac
  have haπ : a ≤ Real.pi := hac.trans hcπ
  have hi : a^3/96 ≤ ∫ θ in (0 : ℝ)..a, g θ := by
    have hh := integral_mono_on (μ := MeasureTheory.volume) ha.le
      ((by fun_prop : Continuous (fun θ : ℝ => θ^2/32)).intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
      (fun θ (hθ : θ ∈ Set.Icc (0 : ℝ) a) => ?_)
    · have hei : (∫ θ in (0 : ℝ)..a, θ^2/32) = a^3/96 := by
        rw [integral_div, integral_pow]
        norm_num
        ring
      rwa [hei] at hh
    · dsimp [g]
      have hw := DenominatorResearch.cosine_weight_bounds θ hθ.1 (hθ.2.trans haπ)
      have hw0 : 0 ≤ 1-Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      have hp := mul_le_mul_of_nonneg_right (hinner θ hθ) hw0
      nlinarith
  have hm : -(a^3/10000) ≤ ∫ θ in a..c, g θ := by
    have hh := integral_mono_on (μ := MeasureTheory.volume) hac
      ((by fun_prop : Continuous (fun θ : ℝ => -M^2*e θ)).intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
      (fun θ (hθ : θ ∈ Set.Icc a c) => ?_)
    · rw [integral_const_mul] at hh
      have hs := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (he.intervalIntegrable 0 a) (he.intervalIntegrable a c)
      have hz : 0 ≤ ∫ θ in (0 : ℝ)..a, e θ := by
        apply integral_nonneg ha.le
        intro θ hθ
        dsimp [e]
        positivity
      have hb := scaled_gaussian_eighth_moment a c ha hc0
      change (∫ θ in (0 : ℝ)..c, e θ) ≤ 1000000*a^9 at hb
      have hb' : (∫ θ in a..c, e θ) ≤ 1000000*a^9 := by linarith
      have hp := mul_le_mul_of_nonneg_left hb' (sq_nonneg M)
      have hq := mul_le_mul_of_nonneg_right hsmall (pow_pos ha 3).le
      nlinarith
    · dsimp [g, e]
      have hθ0 : 0 ≤ θ := ha.le.trans hθ.1
      have hw := DenominatorResearch.cosine_weight_bounds θ hθ0 (hθ.2.trans hcπ)
      have hw0 : 0 ≤ 1-Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      have hp := mul_le_mul_of_nonneg_right (hlocal θ ⟨hθ0,hθ.2⟩) hw0
      have hcoef : 0 ≤ M^2*θ^6*Real.exp (-(θ/a)^2/4) := by positivity
      have hq := mul_le_mul_of_nonneg_left hw.2 hcoef
      have hz : 0 ≤ M^2*θ^8*Real.exp (-(θ/a)^2/4) := by positivity
      nlinarith
  have hfarI : -8*δ ≤ ∫ θ in c..Real.pi, g θ := by
    have hh := integral_mono_on (μ := MeasureTheory.volume) hcπ
      ((continuous_const : Continuous (fun _ : ℝ => -2*δ)).intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)
      (fun θ (hθ : θ ∈ Set.Icc c Real.pi) => ?_)
    · rw [integral_const, smul_eq_mul] at hh
      have h1 := mul_nonneg hc0 hδ
      have h2 := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hδ
      nlinarith
    · dsimp [g]
      have hw0 : 0 ≤ 1-Real.cos θ := sub_nonneg.mpr (Real.cos_le_one θ)
      have hw2 : 1-Real.cos θ ≤ 2 := by linarith [Real.neg_one_le_cos θ]
      have hl := neg_le_of_abs_le (hfar θ hθ)
      have hp := mul_le_mul_of_nonneg_right hl hw0
      have hq := mul_le_mul_of_nonneg_left hw2 hδ
      nlinarith
  have hs1 := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hg.intervalIntegrable 0 a) (hg.intervalIntegrable a c)
  have hs2 := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hg.intervalIntegrable 0 c) (hg.intervalIntegrable c Real.pi)
  change 0 < ∫ θ in (0 : ℝ)..Real.pi, g θ
  nlinarith [pow_pos ha 3]

#print axioms positive_fourier_core
end BBFMRefined
