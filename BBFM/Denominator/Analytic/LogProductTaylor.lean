import BBFM.Denominator.Analytic.FactorDerivatives
import BBFM.Denominator.Analytic.CubicTaylor

noncomputable section
namespace DenominatorResearch
open Finset Complex Real

def logProduct (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ) : ℂ :=
  ∑ i ∈ range n, (m (i + 1) : ℂ) * factorLog r (i + 1) θ

def logProductDeriv (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ) : ℂ :=
  ∑ i ∈ range n, (m (i + 1) : ℂ) * factorLogDeriv r (i + 1) θ

def logProductDerivTwo (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ) : ℂ :=
  ∑ i ∈ range n, (m (i + 1) : ℂ) * factorLogDerivTwo r (i + 1) θ

lemma logProduct_hasDerivAt (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (h : ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r θ i ∈ Complex.slitPlane) :
    HasDerivAt (logProduct m n r) (logProductDeriv m n r θ) θ := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact (factorLog_hasDerivAt r θ (i + 1)
    (h (i + 1) (by omega) (by have := mem_range.mp hi; omega))).const_mul _

lemma logProductDeriv_hasDerivAt (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (h : ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r θ i ≠ 0) :
    HasDerivAt (logProductDeriv m n r) (logProductDerivTwo m n r θ) θ := by
  apply HasDerivAt.fun_sum
  intro i hi
  exact (factorLogDeriv_hasDerivAt r θ (i + 1)
    (h (i + 1) (by omega) (by have := mem_range.mp hi; omega))).const_mul _

lemma logProductDerivTwo_hasDerivAt (m : ℕ → ℕ) (n : ℕ) (r θ : ℝ)
    (h : ∀ i, 1 ≤ i → i ≤ n → 1 + factorPhase r θ i ≠ 0) :
    HasDerivAt (logProductDerivTwo m n r) (thirdLogSum m n r θ) θ := by
  have hh := HasDerivAt.fun_sum (u := range n) (fun i hi =>
    (factorLogDerivTwo_hasDerivAt r θ (i + 1)
      (h (i + 1) (by omega) (by have := mem_range.mp hi; omega))).const_mul (m (i + 1) : ℂ))
  convert! hh using 1
  unfold thirdLogSum
  apply sum_congr rfl
  intro i hi
  ring

/-- A genuine Taylor bound for the sum of logarithms of the actual factors.
All derivative and norm hypotheses are discharged at every radius up to one half. -/
theorem logProduct_small_radius_taylor (m : ℕ → ℕ) (n t : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (hθ : 0 ≤ θ)
    (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ t) :
    ‖logProduct m n r θ - logProduct m n r 0 - (θ : ℂ) * logProductDeriv m n r 0 -
      ((θ : ℂ) ^ 2 / 2) * logProductDerivTwo m n r 0‖ ≤ 832 * (t : ℝ) * r * θ ^ 3 := by
  have hslit : ∀ u i, 1 ≤ i → i ≤ n → 1 + factorPhase r u i ∈ Complex.slitPlane :=
    fun u i hi _ => factorPhase_slitPlane_small r u i hr hrhalf hi
  have hne : ∀ u i, 1 ≤ i → i ≤ n → 1 + factorPhase r u i ≠ 0 :=
    fun u i hi hin => Complex.slitPlane_ne_zero (hslit u i hi hin)
  exact cubic_taylor_bound (logProduct m n r) (logProductDeriv m n r)
    (logProductDerivTwo m n r) (thirdLogSum m n r) θ (832 * (t : ℝ) * r)
    hθ (by positivity)
    (fun u _ => logProduct_hasDerivAt m n r u (hslit u))
    (fun u _ => logProductDeriv_hasDerivAt m n r u (hne u))
    (fun u _ => logProductDerivTwo_hasDerivAt m n r u (hne u))
    (fun u _ => thirdLogSum_small_radius_bound m n t r u hr hrhalf hm) θ ⟨hθ, le_rfl⟩

end DenominatorResearch
