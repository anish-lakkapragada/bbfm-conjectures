import BBFM.Denominator.LocalCore
import BBFM.Denominator.MomentScale
import BBFM.Denominator.Analytic.LocalCentral

noncomputable section
namespace BBFMMoment
open Real Complex intervalIntegral BBFMRelative

/-- Variance-relative Taylor control and consecutive-block Fourier decay
force positivity at effective size 12 * 10^6. -/
theorem quantitative_fourier_positive_half (φ : ℝ → ℂ) (hφ : Continuous φ) (N L V : ℝ)
    (hN : 12*(10 : ℝ)^6 ≤ N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hVlo : N*L^2/100 ≤ V) (hVhi : V ≤ 100*N*L^2)
    (hFourier : ∀ θ ∈ Set.Icc 0 Real.pi,
      ‖φ θ‖ ≤ Real.exp (-N/5000 * min 1 (L^2*θ^2)))
    (hTaylor : ∀ θ ∈ Set.Icc 0 (1/(4*L)), ∃ R : ℂ,
      φ θ = Complex.exp (-((V*θ^2/2 : ℝ) : ℂ)+R) ∧
      ‖R‖ ≤ V*L*θ^3) :
    0 < ∫ θ in (0 : ℝ)..Real.pi, (φ θ).re*(1-Real.cos θ) := by
  let a : ℝ := 1/Real.sqrt V
  let c : ℝ := 1/(4*L)
  let M : ℝ := V*L
  have hV0 := variance_positive N L V hN hL hVlo
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hL0 : 0 < L := by linarith
  have hN0 : 0 ≤ N := le_trans (by positivity) hN
  have ha : 0 < a := by dsimp [a]; positivity
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hac : a ≤ c := by
    dsimp [a,c]
    apply (div_le_div_iff₀ hs0 (by positivity)).2
    simpa using variance_sqrt_large N L V hN hL hVlo
  have hclocal : c ≤ 1/(4*L) := by
    dsimp [c]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hcπ : c ≤ Real.pi := by
    have hc1 : c ≤ 1 := by
      dsimp [c]
      apply (div_le_one (by positivity)).2
      linarith
    linarith [Real.two_le_pi]
  have hVcube : V ≤ 100*N^3 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0.le hLN 2)
      (show 0 ≤ 100*N by positivity)
    nlinarith
  have hsmall : M^2*a^6 ≤ 1/(10 : ℝ)^5 := by
    simpa [a,M] using normalized_cubic_small N L V hN hL hVlo
  have hMa : M*a^3 ≤ 1/10 := by
    apply (sq_le_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 1/10)).mp
    nlinarith only [hsmall]
  have heq (θ : ℝ) : (θ/a)^2 = V*θ^2 := by
    dsimp [a]
    have hd : θ/(1/Real.sqrt V) = θ*Real.sqrt V := by field_simp
    rw [hd, mul_pow, Real.sq_sqrt hV0.le]
    ring
  have ha1 : a ≤ 1 := by
    have hc1 : c ≤ 1 := by
      dsimp [c]
      apply (div_le_one (by positivity)).mpr
      linarith
    exact hac.trans hc1
  apply BBFMLocal.positive_fourier_core (fun θ => (φ θ).re) (Complex.continuous_re.comp hφ)
    a c (Real.exp (-N/(80000 : ℝ))) M ha ha1 hac hcπ (Real.exp_pos _).le
    (by simpa [a] using far_tail_small N V hN hV0 hVcube) hsmall
  · intro θ hθ
    obtain ⟨R, hR, hb⟩ := hTaylor θ ⟨hθ.1,hθ.2.trans (hac.trans hclocal)⟩
    have hb' : ‖R‖ ≤ M*θ^3 := by simpa [M,mul_assoc] using hb
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hθ.1 hθ.2 3) hM
    have hrsmall : ‖R‖ ≤ 1/10 := hb'.trans (hp.trans hMa)
    have ht : θ*Real.sqrt V ≤ 1 := (le_div_iff₀ hs0).1 hθ.2
    have ht2 := pow_le_pow_left₀ (mul_nonneg hθ.1 hs0.le) ht 2
    rw [mul_pow,Real.sq_sqrt hV0.le] at ht2
    have hs : V*θ^2/2 ≤ 1/2 := by nlinarith
    rw [hR]
    exact DenominatorResearch.local_exponential_real_lower _ _ hs hrsmall
  · intro θ hθ
    obtain ⟨R, hR, hb⟩ := hTaylor θ ⟨hθ.1,hθ.2.trans hclocal⟩
    have hb' : ‖R‖ ≤ M*θ^3 := by simpa [M,mul_assoc] using hb
    have hrel : ‖R‖ ≤ (V*θ^2/2)/2 := by
      have hh := local_cubic_relative L V θ hL hV0.le hθ.1 hθ.2
      linarith
    have hh := BBFMRefined.local_exponential_real_lower_error (V*θ^2/2) M θ R hM hθ.1 hb' hrel
    rw [hR,heq]
    convert hh using 1 <;> congr 2 <;> ring
  · intro θ hθ
    have hθ0 : 0 ≤ θ := hc0.trans hθ.1
    have ht : 1 ≤ θ*(4*L) :=
      (div_le_iff₀ (show 0 < 4*L by positivity)).1 hθ.1
    have ht2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht 2
    have hmin : 1/16 ≤ min 1 (L^2*θ^2) := by
      apply le_min
      · norm_num
      · nlinarith only [ht2]
    have hf := (Complex.abs_re_le_norm (φ θ)).trans (hFourier θ ⟨hθ0,hθ.2⟩)
    apply hf.trans
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hmin (show 0 ≤ N/5000 by positivity)
    nlinarith only [hp]

theorem quantitative_fourier_positive (φ : ℝ → ℂ) (hφ : Continuous φ) (N L V : ℝ)
    (hN : 12*(10 : ℝ)^6 ≤ N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hVlo : N*L^2/100 ≤ V) (hVhi : V ≤ 100*N*L^2)
    (hEven : ∀ θ, (φ (-θ)).re = (φ θ).re)
    (hFourier : ∀ θ ∈ Set.Icc 0 Real.pi,
      ‖φ θ‖ ≤ Real.exp (-N/5000 * min 1 (L^2*θ^2)))
    (hTaylor : ∀ θ ∈ Set.Icc 0 (1/(4*L)), ∃ R : ℂ,
      φ θ = Complex.exp (-((V*θ^2/2 : ℝ) : ℂ)+R) ∧
      ‖R‖ ≤ V*L*θ^3) :
    0 < ∫ θ in -Real.pi..Real.pi, (φ θ).re*(1-Real.cos θ) := by
  have hp := quantitative_fourier_positive_half φ hφ N L V hN hL hLN hVlo hVhi hFourier hTaylor
  let g : ℝ → ℝ := fun θ => (φ θ).re*(1-Real.cos θ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hn := integral_comp_neg g (a := (0 : ℝ)) (b := Real.pi)
  simp only [neg_zero] at hn
  have heq : (fun θ => g (-θ)) = g := by
    funext θ
    dsimp [g]
    rw [hEven,Real.cos_neg]
  rw [heq] at hn
  have hsum := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hg.intervalIntegrable (-Real.pi) 0) (hg.intervalIntegrable 0 Real.pi)
  change 0 < ∫ θ in -Real.pi..Real.pi, g θ
  change 0 < ∫ θ in (0 : ℝ)..Real.pi, g θ at hp
  linarith

#print axioms BBFMMoment.quantitative_fourier_positive
end BBFMMoment
