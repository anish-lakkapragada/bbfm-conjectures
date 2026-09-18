import BBFM.Denominator.RelativeDerivatives

/-! Local phase geometry gives a sharper third-logarithmic-derivative bound.
All inherited definitions remain unchanged. -/
noncomputable section
namespace BBFMLocal
open Complex Real Finset DenominatorResearch BBFMRelative
set_option maxHeartbeats 0

lemma thirdLogRatio_nonnegative_real (z : ℂ) (hz : 0≤z.re) :
    ‖thirdLogRatio z‖ ≤ ‖z‖ := by
  have hden : 1≤‖1+z‖ := by
    have hh := Complex.re_le_norm (1+z)
    simp only [Complex.add_re,Complex.one_re] at hh
    linarith
  have hnum : ‖1-z‖ ≤ ‖1+z‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.one_re,Complex.sub_im,
      Complex.one_im,Complex.add_re,Complex.add_im,zero_add,zero_sub,neg_sq]
    nlinarith
  unfold thirdLogRatio
  rw [norm_div,norm_mul,norm_pow]
  apply (div_le_iff₀ (pow_pos (by linarith : 0<‖1+z‖) 3)).mpr
  have hcube : ‖1+z‖ ≤ ‖1+z‖^3 := by
    nlinarith [sq_nonneg (‖1+z‖-1)]
  exact mul_le_mul_of_nonneg_left (hnum.trans hcube) (norm_nonneg z)

lemma thirdLogRatio_sixteenth (z : ℂ) (hz : ‖z‖ ≤ 1/16) :
    ‖thirdLogRatio z‖ ≤ (4/3 : ℝ)*‖z‖ := by
  have hden : (15/16 : ℝ) ≤ ‖1+z‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (-z)
    simp only [norm_one,norm_neg,sub_neg_eq_add] at hh
    linarith
  have hnum : ‖1-z‖ ≤ 17/16 := by
    have hh := norm_sub_le (1 : ℂ) z
    simp only [norm_one] at hh
    linarith
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤15/16) hden 3
  norm_num at hcube
  have hfactor : ‖1-z‖ ≤ (4/3 : ℝ)*‖1+z‖^3 := by linarith
  unfold thirdLogRatio
  rw [norm_div,norm_mul,norm_pow]
  apply (div_le_iff₀ (pow_pos (by linarith : 0<‖1+z‖) 3)).mpr
  have hh := mul_le_mul_of_nonneg_left hfactor (norm_nonneg z)
  nlinarith only [hh]

lemma factorPhase_nonnegative_real (r θ : ℝ) (i : ℕ) (hr : 0≤r)
    (hangle : |(i : ℝ)*θ| ≤ 1) : 0 ≤ (factorPhase r θ i).re := by
  rw [factorPhase_re]
  apply mul_nonneg (pow_nonneg hr i)
  apply Real.cos_nonneg_of_mem_Icc
  have hp := Real.pi_gt_three
  exact ⟨by linarith [(abs_le.mp hangle).1],by linarith [(abs_le.mp hangle).2]⟩

lemma effectiveScale_far_four (n i : ℕ) (r : ℝ) (hn : 0<n)
    (hr : 1/2<r) (hrone : r≤1) (hin : i≤n)
    (hfar : 4*effectiveScale n r < (i : ℝ)) : r^i≤1/16 := by
  obtain ⟨hL,hLn,_⟩ := effectiveScale_bounds n r hn hr hrone
  have hne : effectiveScale n r ≠ (n : ℝ) := by
    have hinR : (i : ℝ) ≤ n := by exact_mod_cast hin
    intro he; rw [he] at hfar hL; linarith
  obtain ⟨hrlt,hrec⟩ := effectiveScale_unsaturated n r hr hrone hne
  have hr0 : 0<r := by linarith
  have hlog : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hrlt)
  have hscale : (-Real.log r)*effectiveScale n r=1 := by
    rw [hrec,mul_one_div,div_self hlog.ne']
  have hprod := mul_le_mul_of_nonneg_left hfar.le hlog.le
  have hexp1 : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg,inv_eq_one_div]
    exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith [Real.exp_one_gt_two])
  have hexp4 : Real.exp (-4) ≤ 1/16 := by
    have hh := pow_le_pow_left₀ (Real.exp_pos (-1)).le hexp1 4
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh ⊢
    exact hh
  calc
    r^i = Real.exp ((i : ℝ)*Real.log r) := by rw [Real.exp_nat_mul,Real.exp_log hr0]
    _ ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by nlinarith)
    _ ≤ 1/16 := hexp4

lemma factorPhase_third_large (n i : ℕ) (r θ : ℝ) (hn : 0<n)
    (hr : 1/2<r) (hrone : r≤1) (hin : i≤n)
    (hθ : |θ|≤1/(4*effectiveScale n r)) :
    ‖thirdLogRatio (factorPhase r θ i)‖ ≤ (4/3 : ℝ)*r^i := by
  have hr0 : 0≤r := by linarith
  obtain ⟨hL,_,_⟩ := effectiveScale_bounds n r hn hr hrone
  by_cases hnear : (i : ℝ) ≤ 4*effectiveScale n r
  · have hangle : |(i : ℝ)*θ|≤1 := by
      rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤ i)]
      have hh := mul_le_mul hnear hθ (abs_nonneg θ) (by positivity)
      have he : 4*effectiveScale n r*(1/(4*effectiveScale n r))=1 := by
        field_simp
      exact hh.trans_eq he
    have hh := thirdLogRatio_nonnegative_real _
      (factorPhase_nonnegative_real r θ i hr0 hangle)
    rw [factorPhase_norm r θ i hr0] at hh
    nlinarith [pow_nonneg hr0 i]
  · apply thirdLogRatio_sixteenth _ (by
      rw [factorPhase_norm r θ i hr0]
      exact effectiveScale_far_four n i r hn hr hrone hin (lt_of_not_ge hnear)) |>.trans_eq
    rw [factorPhase_norm r θ i hr0]

lemma factorPhase_third_small (r θ : ℝ) (i : ℕ) (hr : 0≤r) (hrhalf : r≤1/2)
    (hθ : |θ|≤1/4) :
    ‖thirdLogRatio (factorPhase r θ i)‖ ≤ (4/3 : ℝ)*r^i := by
  by_cases hnear : i≤4
  · have hangle : |(i : ℝ)*θ|≤1 := by
      rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ)≤ i)]
      have hiR : (i : ℝ)≤4 := by exact_mod_cast hnear
      nlinarith [mul_le_mul_of_nonneg_left hθ (show (0 : ℝ)≤ i by positivity)]
    have hh := thirdLogRatio_nonnegative_real _ (factorPhase_nonnegative_real r θ i hr hangle)
    rw [factorPhase_norm r θ i hr] at hh
    nlinarith [pow_nonneg hr i]
  · have hz : ‖factorPhase r θ i‖≤1/16 := by
      rw [factorPhase_norm r θ i hr]
      have hle := pow_le_pow_of_le_one hr (by linarith : r≤1) (by omega : 4≤ i)
      have hp := pow_le_pow_left₀ hr hrhalf 4
      norm_num at hp
      exact hle.trans hp
    simpa only [factorPhase_norm r θ i hr] using thirdLogRatio_sixteenth _ hz

#print axioms factorPhase_third_large
#print axioms factorPhase_third_small
end BBFMLocal
