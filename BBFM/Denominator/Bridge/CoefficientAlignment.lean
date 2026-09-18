import BBFM.Denominator.Bridge.Identification

open Polynomial Finset
noncomputable section
namespace DenominatorBridge

lemma prod_Icc_one_eq_range {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    (∏ i ∈ Icc 1 n, f i) = ∏ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_range_succ, ih]

/-- The literal real-polynomial expression used in DenominatorResearch.Basic. -/
def productR (n : ℕ) : ℝ[X] :=
  ∏ i ∈ range n, (1 + X ^ (i + 1)) ^ (Nat.log 2 (n / (i + 1)) + 1)

theorem denReduced_map_real (n : ℕ) (hn : 1 ≤ n) :
    (denReduced n).map (algebraMap ℚ ℝ) = productR n := by
  rw [denReduced_eq_productQ n hn]
  unfold productQ productR
  simp only [Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X]
  exact prod_Icc_one_eq_range _ n

theorem denReduced_coeff_real (n k : ℕ) (hn : 1 ≤ n) :
    ((denReduced n).coeff k : ℝ) = (productR n).coeff k := by
  have h := congrArg (fun P : ℝ[X] => P.coeff k) (denReduced_map_real n hn)
  simpa only [Polynomial.coeff_map, eq_ratCast] using h

/-- Every coefficient inequality transfers to the exact rational denominator;
there is no unexplained normalization or gcd hypothesis. -/
theorem source_logconcavity_iff_product (n k : ℕ) (hn : 1 ≤ n) :
    (denReduced n).coeff (k - 1) * (denReduced n).coeff (k + 1) ≤
        (denReduced n).coeff k ^ 2 ↔
    (productR n).coeff (k - 1) * (productR n).coeff (k + 1) ≤
        (productR n).coeff k ^ 2 := by
  rw [← denReduced_coeff_real n (k - 1) hn,
    ← denReduced_coeff_real n (k + 1) hn, ← denReduced_coeff_real n k hn]
  norm_cast

end DenominatorBridge

#print axioms DenominatorBridge.denReduced_map_real
#print axioms DenominatorBridge.source_logconcavity_iff_product
