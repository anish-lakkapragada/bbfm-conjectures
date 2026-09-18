import BBFM.Denominator.Analytic.LogDerivativeBound

noncomputable section
namespace DenominatorResearch
open Complex Real Finset

lemma factorPhase_hasDerivAt (r θ : ℝ) (i : ℕ) :
    HasDerivAt (fun u : ℝ => factorPhase r u i)
      ((Complex.I * (i : ℂ)) * factorPhase r θ i) θ := by
  have hcast := (hasDerivAt_id θ).ofReal_comp
  have hlinear := (hcast.const_mul (i : ℂ)).mul_const Complex.I
  have hh := hlinear.cexp.const_mul ((r : ℂ) ^ i)
  unfold factorPhase
  convert! hh using 1 <;> simp only [id_eq, Complex.ofReal_one] <;> ring

lemma factorPhase_slitPlane_small (r θ : ℝ) (i : ℕ) (hr : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (hi : 1 ≤ i) : 1 + factorPhase r θ i ∈ Complex.slitPlane := by
  have hz : ‖factorPhase r θ i‖ ≤ 1 / 2 := by
    rw [factorPhase_norm r θ i hr]
    exact (pow_le_of_le_one hr (by linarith) (by omega)).trans hrhalf
  have hre := (Complex.abs_re_le_norm (factorPhase r θ i)).trans hz
  have hlo := (abs_le.mp hre).1
  apply Complex.mem_slitPlane_iff.mpr
  left
  simp only [Complex.add_re, Complex.one_re]
  linarith

def factorLog (r : ℝ) (i : ℕ) (θ : ℝ) : ℂ := Complex.log (1 + factorPhase r θ i)

def factorLogDeriv (r : ℝ) (i : ℕ) (θ : ℝ) : ℂ :=
  (Complex.I * (i : ℂ)) * factorPhase r θ i / (1 + factorPhase r θ i)

def factorLogDerivTwo (r : ℝ) (i : ℕ) (θ : ℝ) : ℂ :=
  (Complex.I * (i : ℂ)) ^ 2 * factorPhase r θ i / (1 + factorPhase r θ i) ^ 2

lemma factorLog_hasDerivAt (r θ : ℝ) (i : ℕ)
    (hslit : 1 + factorPhase r θ i ∈ Complex.slitPlane) :
    HasDerivAt (factorLog r i) (factorLogDeriv r i θ) θ := by
  exact ((factorPhase_hasDerivAt r θ i).const_add 1).clog_real hslit

lemma factorLogDeriv_hasDerivAt (r θ : ℝ) (i : ℕ)
    (hd : 1 + factorPhase r θ i ≠ 0) :
    HasDerivAt (factorLogDeriv r i) (factorLogDerivTwo r i θ) θ := by
  have hp := factorPhase_hasDerivAt r θ i
  have hh := (hp.const_mul (Complex.I * (i : ℂ))).div (hp.const_add 1) hd
  unfold factorLogDeriv factorLogDerivTwo
  convert! hh using 1
  field_simp
  <;> ring

/-- The third logarithmic derivative formula is proved, not introduced as an interface. -/
lemma factorLogDerivTwo_hasDerivAt (r θ : ℝ) (i : ℕ)
    (hd : 1 + factorPhase r θ i ≠ 0) :
    HasDerivAt (factorLogDerivTwo r i)
      ((Complex.I * (i : ℂ)) ^ 3 * thirdLogRatio (factorPhase r θ i)) θ := by
  have hp := factorPhase_hasDerivAt r θ i
  have hh := (hp.const_mul ((Complex.I * (i : ℂ)) ^ 2)).div ((hp.const_add 1).pow 2)
    (pow_ne_zero 2 hd)
  unfold factorLogDerivTwo thirdLogRatio
  convert! hh using 1
  simp only [Pi.pow_apply]
  field_simp
  <;> ring

end DenominatorResearch
