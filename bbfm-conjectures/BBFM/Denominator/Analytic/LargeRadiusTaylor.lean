import BBFM.Denominator.Analytic.EffectiveMoment
import BBFM.Denominator.Analytic.SmallRadiusTaylor

noncomputable section
namespace DenominatorResearch
open Finset Complex Real

lemma effectiveScale_far_pow (n i : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) (hin : i ≤ n)
    (hfar : effectiveScale n r < (i : ℝ)) : r ^ i ≤ 1 / 2 := by
  have hne : effectiveScale n r ≠ (n : ℝ) := by
    have hinR : (i : ℝ) ≤ n := by exact_mod_cast hin
    linarith
  obtain ⟨hrlt, hrec⟩ := effectiveScale_unsaturated n r hr hrone hne
  have hr0 : 0 < r := by linarith
  have hh : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hrlt)
  have hscale : (-Real.log r) * effectiveScale n r = 1 := by
    rw [hrec, mul_one_div, div_self hh.ne']
  have hprod := mul_le_mul_of_nonneg_left hfar.le hh.le
  have hexp : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 1)).2 (by linarith [Real.exp_one_gt_two])
  calc
    r ^ i = Real.exp ((i : ℝ) * Real.log r) := by rw [Real.exp_nat_mul, Real.exp_log hr0]
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ 1 / 2 := hexp

lemma factorPhase_re (r θ : ℝ) (i : ℕ) :
    (factorPhase r θ i).re = r ^ i * Real.cos ((i : ℝ) * θ) := by
  unfold factorPhase
  have heq : (i : ℂ) * (θ : ℂ) * Complex.I = (((i : ℝ) * θ : ℝ) : ℂ) * Complex.I := by
    push_cast
    rfl
  rw [heq]
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_re, ← Complex.ofReal_pow]

/-- The genuine local factor has positive real part and a uniform denominator bound. -/
lemma factorPhase_large_local (n i : ℕ) (r θ : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) (hi : 1 ≤ i) (hin : i ≤ n)
    (hθ : |θ| ≤ 1 / (4 * effectiveScale n r)) :
    1 + factorPhase r θ i ∈ Complex.slitPlane ∧
      1 / 2 ≤ ‖1 + factorPhase r θ i‖ := by
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨hL, _, _⟩ := effectiveScale_bounds n r hn hr hrone
  have hL0 : 0 < effectiveScale n r := by linarith
  by_cases hnear : (i : ℝ) ≤ effectiveScale n r
  · have hi0 : (0 : ℝ) ≤ i := by positivity
    have hangle : |(i : ℝ) * θ| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_nonneg hi0]
      have hh := mul_le_mul hnear hθ (abs_nonneg θ) hL0.le
      have heq : effectiveScale n r * (1 / (4 * effectiveScale n r)) = 1 / 4 := by field_simp
      exact hh.trans_eq heq
    have hcos : 0 ≤ Real.cos ((i : ℝ) * θ) := by
      apply Real.cos_nonneg_of_mem_Icc
      have hp := Real.pi_gt_three
      exact ⟨by linarith [(abs_le.mp hangle).1], by linarith [(abs_le.mp hangle).2]⟩
    have hre : 1 ≤ (1 + factorPhase r θ i).re := by
      simp only [Complex.add_re, Complex.one_re, factorPhase_re]
      exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg hr0 i) hcos)
    constructor
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith))
    · have hh := Complex.re_le_norm (1 + factorPhase r θ i)
      linarith
  · have hp := effectiveScale_far_pow n i r hn hr hrone hin (lt_of_not_ge hnear)
    have hz : ‖factorPhase r θ i‖ ≤ 1 / 2 := by rw [factorPhase_norm r θ i hr0]; exact hp
    have hre := (Complex.abs_re_le_norm (factorPhase r θ i)).trans hz
    constructor
    · apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.add_re, Complex.one_re]
      linarith [(abs_le.mp hre).1]
    · have hh := norm_sub_norm_le (1 : ℂ) (-factorPhase r θ i)
      simp only [norm_one, norm_neg, sub_neg_eq_add] at hh
      linarith

lemma thirdLogSum_large_radius_bound (n : ℕ) (r θ : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1)
    (hθ : |θ| ≤ 1 / (4 * effectiveScale n r)) :
    ‖thirdLogSum (fun i => Nat.log 2 (n / i) + 1) n r θ‖ ≤
      1792 * (1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) *
        (effectiveScale n r) ^ 4 := by
  have hr0 : 0 ≤ r := by linarith
  have hs : ‖thirdLogSum (fun i => Nat.log 2 (n / i) + 1) n r θ‖ ≤
      16 * weightedMoment (fun i => Nat.log 2 (n / i) + 1) n 3 r := by
    unfold thirdLogSum weightedMoment
    apply (norm_sum_le _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hlocal := factorPhase_large_local n (i + 1) r θ hn hr hrone (by omega)
      (by have := mem_range.mp hi; omega) hθ
    have hratio := thirdLogRatio_norm_bound (factorPhase r θ (i + 1))
      (by rw [factorPhase_norm r θ (i + 1) hr0]; exact pow_le_one₀ hr0 hrone) hlocal.2
    rw [factorPhase_norm r θ (i + 1) hr0] at hratio
    simp only [norm_mul, norm_pow, Complex.norm_I, one_mul, Complex.norm_natCast]
    have hh := mul_le_mul_of_nonneg_left hratio
      (show 0 ≤ ((Nat.log 2 (n / (i + 1)) + 1 : ℕ) : ℝ) * ((i + 1 : ℕ) : ℝ) ^ 3 by positivity)
    push_cast at hh ⊢
    nlinarith
  have hm := (den_large_radius_moments n r hn hr hrone).2
  linarith

lemma weightedBernoulliChar_eq_exp_logProduct_local (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r)
    (hne : ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r θ i ≠ 0) :
    weightedBernoulliChar m (tiltedProbability r) n θ =
      Complex.exp (logProduct m n r θ - logProduct m n r 0) := by
  have hzero : ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r 0 i ≠ 0 := by
    intro i _ _
    have hp : 0 < 1 + r ^ i := by positivity
    simp only [factorPhase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact_mod_cast hp.ne'
  rw [Complex.exp_sub, logProduct_exp m n r θ hne, logProduct_exp m n r 0 hzero,
    weightedBernoulliChar_eq_eval m n r θ hr]
  congr 1
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.eval_eq_sum_range]
  push_cast
  rfl

/-- All local Taylor hypotheses are discharged for the actual large-radius product. -/
theorem den_large_radius_local_taylor (n k : ℕ) (r θ : ℝ) (hn : 0 < n)
    (hr : 1 / 2 < r) (hrone : r ≤ 1) (hθ : 0 ≤ θ)
    (hθL : θ ≤ 1 / (4 * effectiveScale n r))
    (hmean : tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = (k : ℝ)) :
    ∃ R : ℂ,
      centeredDenChar n k r θ = Complex.exp
        (-((tiltedVariance (fun i => Nat.log 2 (n / i) + 1) n r * θ ^ 2 / 2 : ℝ) : ℂ) + R) ∧
      ‖R‖ ≤ 10000 * ((1 + Real.logb 2 ((n : ℝ) / effectiveScale n r)) * effectiveScale n r) *
        (effectiveScale n r) ^ 3 * θ ^ 3 := by
  let m := fun i => Nat.log 2 (n / i) + 1
  let L := effectiveScale n r
  let M := 1 + Real.logb 2 ((n : ℝ) / L)
  have hL := (effectiveScale_bounds n r hn hr hrone).1
  have hLn := (effectiveScale_bounds n r hn hr hrone).2.1
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hM : 0 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ) / L := (le_div_iff₀ hL0).2 (by simpa using hLn)
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  have hlocal (u : ℝ) (hu : u ∈ Set.Icc 0 θ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :=
    factorPhase_large_local n i r u hn hr hrone hi hin
      (by rw [abs_of_nonneg hu.1]; exact hu.2.trans hθL)
  have hslit (u : ℝ) (hu : u ∈ Set.Icc 0 θ) :
      ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r u i ∈ Complex.slitPlane :=
    fun i hi hin => (hlocal u hu i hi hin).1
  have hne (u : ℝ) (hu : u ∈ Set.Icc 0 θ) :
      ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r u i ≠ 0 :=
    fun i hi hin => Complex.slitPlane_ne_zero (hslit u hu i hi hin)
  have ht := cubic_taylor_bound (logProduct m n r) (logProductDeriv m n r)
    (logProductDerivTwo m n r) (thirdLogSum m n r) θ (1792 * M * L ^ 4)
    hθ (by positivity)
    (fun u hu => logProduct_hasDerivAt m n r u (hslit u hu))
    (fun u hu => logProductDeriv_hasDerivAt m n r u (hne u hu))
    (fun u hu => logProductDerivTwo_hasDerivAt m n r u (hne u hu))
    (fun u hu => thirdLogSum_large_radius_bound n r u hn hr hrone
      (by rw [abs_of_nonneg hu.1]; exact hu.2.trans hθL)) θ ⟨hθ, le_rfl⟩
  let R := logProduct m n r θ - logProduct m n r 0 -
    (θ : ℂ) * logProductDeriv m n r 0 - ((θ : ℂ) ^ 2 / 2) * logProductDerivTwo m n r 0
  refine ⟨R, ?_, ?_⟩
  · unfold centeredDenChar denChar
    rw [weightedBernoulliChar_eq_exp_logProduct_local _ n r θ (by linarith) (hne θ ⟨hθ, le_rfl⟩),
      ← Complex.exp_add]
    congr 1
    dsimp [R]
    rw [logProductDeriv_zero, logProductDerivTwo_zero]
    change logProduct m n r θ - logProduct m n r 0 + -(k : ℂ) * (θ : ℂ) * Complex.I = _
    have hm : tiltedMean m n r = (k : ℝ) := hmean
    rw [hm]
    push_cast
    ring
  · change ‖R‖ ≤ _ at ht
    change ‖R‖ ≤ 10000 * (M * L) * L ^ 3 * θ ^ 3
    have hp : 0 ≤ M * L ^ 4 * θ ^ 3 := by positivity
    nlinarith

end DenominatorResearch
