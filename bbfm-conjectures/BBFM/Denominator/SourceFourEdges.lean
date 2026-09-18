import BBFM.Denominator.SourceFourEdge
import BBFM.Denominator.Analytic.Symmetry

/-! Reflection of the factor-four edge theorem using the rational
denominator degree and product symmetry. -/
noncomputable section
namespace BBFMKernel
open Polynomial DenominatorResearch DenominatorBridge

theorem source_degree_eq_product (n : ℕ) (hn : 1 ≤ n) :
    (denReduced n).natDegree = (den n).natDegree := by
  have h := congrArg Polynomial.natDegree (denReduced_map_real n hn)
  simpa only [Polynomial.natDegree_map, productR, den, weightedProduct] using h

theorem source_coeff_reflect (n k : ℕ) (hn : 1 ≤ n)
    (hk : k ≤ (denReduced n).natDegree) :
    (denReduced n).coeff ((denReduced n).natDegree - k) =
      (denReduced n).coeff k := by
  have hd := source_degree_eq_product n hn
  have h := den_coeff_reflect n k (by omega)
  have hcast :
      ((denReduced n).coeff ((denReduced n).natDegree - k) : ℝ) =
        ((denReduced n).coeff k : ℝ) := by
    rw [denReduced_coeff_real n _ hn, denReduced_coeff_real n _ hn, hd]
    exact h
  exact_mod_cast hcast

theorem source_four_upper_edge (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hD : k + 1 ≤ (denReduced n).natDegree)
    (hsize : 4 * k ≤ Nat.log 2 n + 1) :
    (denReduced n).coeff ((denReduced n).natDegree - k - 1) *
      (denReduced n).coeff ((denReduced n).natDegree - k + 1) ≤
      (denReduced n).coeff ((denReduced n).natDegree - k) ^ 2 := by
  have hl := source_coeff_reflect n (k + 1) hn hD
  have hr := source_coeff_reflect n (k - 1) hn (by omega)
  have hc := source_coeff_reflect n k hn (by omega)
  have heq : (denReduced n).natDegree - (k - 1) =
      (denReduced n).natDegree - k + 1 := by omega
  rw [heq] at hr
  rw [← Nat.sub_add_eq, hl, hr, hc, mul_comm]
  exact source_four_edge n k hn hk hsize

/-- Every internal coefficient within the factor-four bound of either
edge satisfies log-concavity, with the exact source degree in the bound. -/
theorem source_four_either_edge (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hD : k + 1 ≤ (denReduced n).natDegree)
    (hsize : 4 * min k ((denReduced n).natDegree - k) ≤ Nat.log 2 n + 1) :
    (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) ≤
      (denReduced n).coeff k ^ 2 := by
  by_cases hleft : k ≤ (denReduced n).natDegree - k
  · rw [min_eq_left hleft] at hsize
    exact source_four_edge n k hn hk hsize
  · rw [min_eq_right (by omega)] at hsize
    have h := source_four_upper_edge n ((denReduced n).natDegree - k) hn
      (by omega) (by omega) hsize
    have heq : (denReduced n).natDegree - ((denReduced n).natDegree - k) = k := by
      omega
    simpa only [heq] using h

#print axioms source_degree_eq_product
#print axioms source_coeff_reflect
#print axioms source_four_upper_edge
#print axioms source_four_either_edge
end BBFMKernel
