import BBFM.Denominator.Analytic.FourierCore
import BBFM.Denominator.Analytic.GaussianScale

noncomputable section
namespace DenominatorResearch
open Real Complex intervalIntegral

/-- The quantitative Fourier criterion used in the written eventual proof.
The global norm bound and local exponential/Taylor representation are explicit hypotheses;
this theorem does not claim they have all been discharged for the denominator family. -/
theorem quantitative_fourier_positive_half (φ : ℝ → ℂ) (hφ : Continuous φ) (N L V : ℝ)
    (hN : (10 : ℝ) ^ 100 ≤ N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hVlo : N * L ^ 2 / 1000 ≤ V) (hVhi : V ≤ 100 * N * L ^ 2)
    (hFourier : ∀ θ ∈ Set.Icc 0 Real.pi,
      ‖φ θ‖ ≤ Real.exp (-N / 100000000 * min 1 (L ^ 2 * θ ^ 2)))
    (hTaylor : ∀ θ ∈ Set.Icc 0 (1 / (4 * L)), ∃ R : ℂ,
      φ θ = Complex.exp (-((V * θ ^ 2 / 2 : ℝ) : ℂ) + R) ∧
      ‖R‖ ≤ 10000 * N * L ^ 3 * θ ^ 3) :
    0 < ∫ θ in (0 : ℝ)..Real.pi, (φ θ).re * (1 - Real.cos θ) := by
  have hV0 := variance_positive N L V hN hL hVlo
  have hs0 : 0 < Real.sqrt V := Real.sqrt_pos.2 hV0
  have hL0 : 0 < L := by linarith
  have hN0 : 0 ≤ N := le_trans (by positivity) hN
  have hstrong := variance_sqrt_large N L V hN hL hVlo
  have hloc : 100000000 / Real.sqrt V ≤ 1 / (4 * L) := by
    apply (div_le_div_iff₀ hs0 (by positivity)).2
    nlinarith
  have hca : 100000000 * (1 / Real.sqrt V) ≤ 1 / L := by
    calc
      100000000 * (1 / Real.sqrt V) ≤ 1 / (4 * L) := by simpa only [mul_one_div] using hloc
      _ ≤ 1 / L := by
        apply (div_le_div_iff₀ (by positivity) hL0).2
        nlinarith
  have hcπ : 1 / L ≤ Real.pi := by
    have hh : 1 / L ≤ 1 := (div_le_one hL0).2 hL
    linarith [Real.two_le_pi]
  have hVcube : V ≤ 100 * N ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0.le hLN 2)
      (show 0 ≤ 100 * N by positivity)
    nlinarith
  have hlocal : ∀ θ ∈ Set.Icc 0 (100000000 / Real.sqrt V), ∃ R : ℂ,
      φ θ = Complex.exp (-((V * θ ^ 2 / 2 : ℝ) : ℂ) + R) ∧ ‖R‖ ≤ 1 / 10 := by
    intro θ hθ
    obtain ⟨R, heq, hR⟩ := hTaylor θ ⟨hθ.1, hθ.2.trans hloc⟩
    exact ⟨R, heq, hR.trans (cubic_remainder_small N L V θ hN hL hVlo hθ.1 hθ.2)⟩
  apply positive_fourier_core (fun θ => (φ θ).re) (Complex.continuous_re.comp hφ)
    (1 / Real.sqrt V) (1 / L) (Real.exp (-N / 100000000))
    (by positivity) hca hcπ (Real.exp_pos _).le (far_tail_small N V hN hV0 hVcube)
  · intro θ hθ
    have hθmax : θ ≤ 100000000 / Real.sqrt V := by
      apply hθ.2.trans
      exact (div_le_div_iff_of_pos_right hs0).2 (by norm_num)
    obtain ⟨R, heq, hR⟩ := hlocal θ ⟨hθ.1, hθmax⟩
    have ht := (le_div_iff₀ hs0).1 hθ.2
    have ht2 := pow_le_pow_left₀ (mul_nonneg hθ.1 hs0.le) ht 2
    rw [mul_pow, Real.sq_sqrt hV0.le] at ht2
    have hs : V * θ ^ 2 / 2 ≤ 1 / 2 := by nlinarith
    rw [heq]
    exact local_exponential_real_lower _ _ hs hR
  · intro θ hθ
    have hθmax : θ ≤ 100000000 / Real.sqrt V := by simpa only [mul_one_div] using hθ.2
    obtain ⟨R, heq, hR⟩ := hlocal θ ⟨hθ.1, hθmax⟩
    rw [heq]
    exact (local_exponential_real_pos _ _ hR).le
  · intro θ hθ
    have hθ0 : 0 ≤ θ := le_trans (by positivity) hθ.1
    have ht := (le_div_iff₀ hL0).1 hθ.2
    have ht2 := pow_le_pow_left₀ (mul_nonneg hθ0 hL0.le) ht 2
    have hmin : L ^ 2 * θ ^ 2 ≤ 1 := by nlinarith
    have hF := (Complex.abs_re_le_norm (φ θ)).trans (hFourier θ ⟨hθ0, hθ.2.trans hcπ⟩)
    rw [min_eq_right hmin] at hF
    apply hF.trans
    apply Real.exp_le_exp.mpr
    have hVθ := mul_le_mul_of_nonneg_right hVhi (sq_nonneg θ)
    have heq : (θ / (1 / Real.sqrt V)) ^ 2 = V * θ ^ 2 := by
      have hd : θ / (1 / Real.sqrt V) = θ * Real.sqrt V := by field_simp
      rw [hd, mul_pow, Real.sq_sqrt hV0.le]
      ring
    rw [heq]
    nlinarith
  · intro θ hθ
    have hθ0 : 0 ≤ θ := le_trans (by positivity) hθ.1
    have ht := (div_le_iff₀ hL0).1 hθ.1
    have ht2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ht 2
    have hmin : 1 ≤ L ^ 2 * θ ^ 2 := by nlinarith
    have hF := (Complex.abs_re_le_norm (φ θ)).trans (hFourier θ ⟨hθ0, hθ.2⟩)
    simpa only [min_eq_left hmin, mul_one] using hF

/-- Full symmetric-interval form. The conjugation symmetry of a characteristic function
supplies the explicit even-real-part hypothesis. -/
theorem quantitative_fourier_positive (φ : ℝ → ℂ) (hφ : Continuous φ) (N L V : ℝ)
    (hN : (10 : ℝ) ^ 100 ≤ N) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hVlo : N * L ^ 2 / 1000 ≤ V) (hVhi : V ≤ 100 * N * L ^ 2)
    (hEven : ∀ θ, (φ (-θ)).re = (φ θ).re)
    (hFourier : ∀ θ ∈ Set.Icc 0 Real.pi,
      ‖φ θ‖ ≤ Real.exp (-N / 100000000 * min 1 (L ^ 2 * θ ^ 2)))
    (hTaylor : ∀ θ ∈ Set.Icc 0 (1 / (4 * L)), ∃ R : ℂ,
      φ θ = Complex.exp (-((V * θ ^ 2 / 2 : ℝ) : ℂ) + R) ∧
      ‖R‖ ≤ 10000 * N * L ^ 3 * θ ^ 3) :
    0 < ∫ θ in -Real.pi..Real.pi, (φ θ).re * (1 - Real.cos θ) := by
  have hp := quantitative_fourier_positive_half φ hφ N L V hN hL hLN hVlo hVhi hFourier hTaylor
  let g : ℝ → ℝ := fun θ => (φ θ).re * (1 - Real.cos θ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hn := integral_comp_neg g (a := (0 : ℝ)) (b := Real.pi)
  simp only [neg_zero] at hn
  have heq : (fun θ => g (-θ)) = g := by
    funext θ
    dsimp [g]
    rw [hEven, Real.cos_neg]
  rw [heq] at hn
  have hsum := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hg.intervalIntegrable (-Real.pi) 0) (hg.intervalIntegrable 0 Real.pi)
  change 0 < ∫ θ in -Real.pi..Real.pi, g θ
  change 0 < ∫ θ in (0 : ℝ)..Real.pi, g θ at hp
  linarith

end DenominatorResearch
