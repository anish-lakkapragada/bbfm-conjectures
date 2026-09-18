import BBFM.Denominator.RelativeInterior
import BBFM.Denominator.Bridge.CoefficientAlignment

noncomputable section
namespace BBFMRelative
open Polynomial DenominatorBridge

theorem source_degree_eq_product (n : ℕ) (hn : 1 ≤ n) :
    (denReduced n).natDegree = (DenominatorResearch.den n).natDegree := by
  have h := congrArg Polynomial.natDegree (denReduced_map_real n hn)
  change (denReduced n).natDegree = (productR n).natDegree
  simpa only [Polynomial.natDegree_map] using h

/-- For every positive n, independently of its size, coefficients at distance
at least6·10^26 from both ends of the literal source polynomial satisfy a
strict Turan inequality. -/
theorem source_den_interior_strict (n k : ℕ) (hn : 1 ≤ n)
    (hleft : 6*((10 : ℕ)^13)^2 ≤ k)
    (hright : 6*((10 : ℕ)^13)^2 ≤ (denReduced n).natDegree-k) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) <
      (denReduced n).coeff k^2 := by
  have hh := BBFMRelative.den_interior_strict n k (by omega) hleft
    (by rwa [source_degree_eq_product n hn] at hright)
  change (productR n).coeff (k-1)*(productR n).coeff (k+1) <
    (productR n).coeff k^2 at hh
  rw [← denReduced_coeff_real n (k-1) hn, ← denReduced_coeff_real n (k+1) hn,
    ← denReduced_coeff_real n k hn] at hh
  exact_mod_cast hh

/-- Every possible failure is localized to a fixed finite edge width,
uniformly across all n. This does not assert that the remaining edges pass. -/
theorem source_den_failure_at_edge (n k : ℕ) (hn : 1 ≤ n)
    (hfail : (denReduced n).coeff k^2 <
      (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1)) :
    k < 6*((10 : ℕ)^13)^2 ∨
      (denReduced n).natDegree-k < 6*((10 : ℕ)^13)^2 := by
  by_contra h
  push Not at h
  have hh := source_den_interior_strict n k hn h.1 h.2
  linarith

#print axioms source_degree_eq_product
#print axioms source_den_interior_strict
#print axioms source_den_failure_at_edge
end BBFMRelative
