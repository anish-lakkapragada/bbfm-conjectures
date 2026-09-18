import BBFM.Denominator.MomentInterior
import BBFM.Denominator.RelativeSourceInterior
import BBFM.Denominator.Bridge.CoefficientAlignment

noncomputable section
namespace BBFMMoment
open Polynomial DenominatorBridge BBFMRelative

/-- For every positive n, independently of its size, coefficients at distance
at least8.64·10^14 from both ends of the literal source polynomial satisfy a
strict Turan inequality. -/
theorem source_den_interior_strict (n k : ℕ) (hn : 1 ≤ n)
    (hleft : 6*(12*(10 : ℕ)^6)^2 ≤ k)
    (hright : 6*(12*(10 : ℕ)^6)^2 ≤ (denReduced n).natDegree-k) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) <
      (denReduced n).coeff k^2 := by
  have hh := BBFMMoment.den_interior_strict n k (by omega) hleft
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
    k < 6*(12*(10 : ℕ)^6)^2 ∨
      (denReduced n).natDegree-k < 6*(12*(10 : ℕ)^6)^2 := by
  by_contra h
  push Not at h
  have hh := source_den_interior_strict n k hn h.1 h.2
  linarith

/-- A convenient rounded version: distance10^15 from both ends suffices. -/
theorem source_den_interior_strict_of_10pow15 (n k : ℕ) (hn : 1 ≤ n)
    (hleft : (10 : ℕ)^15 ≤ k)
    (hright : (10 : ℕ)^15 ≤ (denReduced n).natDegree-k) :
    (denReduced n).coeff (k-1)*(denReduced n).coeff (k+1) <
      (denReduced n).coeff k^2 := by
  apply source_den_interior_strict n k hn <;> norm_num at * <;> omega

#print axioms BBFMMoment.source_den_interior_strict_of_10pow15
#print axioms BBFMMoment.source_den_interior_strict
#print axioms BBFMMoment.source_den_failure_at_edge
end BBFMMoment
