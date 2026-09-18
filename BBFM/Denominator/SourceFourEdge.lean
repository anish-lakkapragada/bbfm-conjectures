import BBFM.Denominator.PositiveNewtonFour
import BBFM.Denominator.SourceKernelBudget
import BBFM.Denominator.Bridge.CoefficientAlignment

/-! A uniform source-specific linear edge proved from the exact signed
kernel and a one-sided Newton induction. No finite coefficient certificate
or assumed log-concavity is used. -/
noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear DenominatorResearch BBFMRefined
set_option maxHeartbeats 0

theorem den_four_edge (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hsize : 4*k≤Nat.log 2 n+1) :
    (den n).coeff (k-1)*(den n).coeff (k+1)≤(den n).coeff k^2 := by
  let m : ℕ → ℕ := fun i => Nat.log 2 (n/i)+1
  let a : ℕ → ℝ := fun j => (den n).coeff j
  let r : ℝ := Nat.log 2 n+1
  have hrK : 4*(k:ℝ)≤r := by dsimp [r]; exact_mod_cast hsize
  have hr : 0<r := by dsimp [r]; positivity
  have h8 : 8≤n := by
    have hlog : 3≤Nat.log 2 n := by omega
    simpa using Nat.pow_le_of_le_log (by omega : n≠0) hlog
  have ha0 : a 0=1 := weightedProduct_zero m n
  have hl : ∀ j, (r-j)*a j≤((j:ℝ)+1)*a (j+1) := by
    simpa [a,r,m,den] using weightedProduct_coeff_lower m n hn
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have ha : ∀ j≤k+1, 0<a j := initial_positive a r k ha0 (by linarith) hl
  have hb : ∀ t≤k, 0 ≤ sourceKernel n t := by
    intro t ht
    have hw : 2*(t+1)≤Nat.log 2 n+1 := by omega
    have htn : t+1≤n := by have hh := Nat.log_le_self 2 n; omega
    have hh := source_logD_positive_initial n (t+1) (by omega) htn hw
    simpa [sourceKernel] using hh.le
  have hb0 : sourceKernel n 0=r := by
    simpa [sourceKernel,m,r] using weightedSeries_logD_zero m n hn
  have hrec (j : ℕ) (hj : j≤k) :
      ((j:ℝ)+1)*a (j+1)=∑ t ∈ range (j+1), sourceKernel n t*a (j-t) := by
    have hh := logD_recurrence (weightedSeries m n) (weightedSeries_constant m n) j
    simpa only [a, den, m, sourceKernel, weightedSeries_eq_coe, Polynomial.coeff_coe] using hh
  have hs := source_kernel_weighted_budget n k h8
  have hs' : (∑ t ∈ range k, sourceKernel n (t+1)*((t:ℝ)+1)*(1/4)^t)≤4*r := by
    simpa [r] using hs
  exact BBFMPositiveNewton.logconcave_of_positive_kernel a (sourceKernel n) r k
    hr hrK ha hb hb0 hrec hs' k hk le_rfl

/-- The factor-four edge bound for the rational monic-gcd denominator. -/
theorem source_four_edge (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hsize : 4*k≤Nat.log 2 n+1) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1)≤(denReduced n).coeff k^2 := by
  apply (DenominatorBridge.source_logconcavity_iff_product n k hn).mpr
  exact den_four_edge n k hn hk hsize

#print axioms den_four_edge
#print axioms source_four_edge
end BBFMKernel
