import BBFM.Binary.RefinementComparison
import BBFM.Binary.PowerConcavity
import Mathlib.Algebra.Polynomial.Expand

/-! Exact passage between the integer polynomial formulation and the real
formal-series comparison argument. -/
noncomputable section
namespace BinaryRealification
open Polynomial PowerSeries BinaryResearch BinaryPowerConcavity

def toRealSeries (P : ℤ[X]) : ℝ⟦X⟧ :=
  (P.map (Int.castRingHom ℝ) : ℝ[X])

@[simp] lemma coeff_toRealSeries (P : ℤ[X]) (k : ℕ) :
    PowerSeries.coeff k (toRealSeries P)=(P.coeff k : ℝ) := by
  simp [toRealSeries]

lemma expand_coe_square (P : ℝ[X]) :
    PowerSeries.expand 2 (by omega) (P : ℝ⟦X⟧)=
      (P.comp (Polynomial.X^2) : ℝ[X]) := by
  ext k
  rw [PowerSeries.coeff_expand,Polynomial.coeff_coe]
  have he := Polynomial.coeff_expand (by decide : 0 < 2) P k
  simpa only [Polynomial.coeff_coe,Polynomial.expand_eq_comp_X_pow] using he.symm

lemma refineSeries_toRealSeries (p : ℕ) (P : ℤ[X]) :
    BinaryResearch.refineSeries p (toRealSeries P)=
      toRealSeries (((1+Polynomial.X)^(p+1))*P.comp (Polynomial.X^2)) := by
  unfold BinaryResearch.refineSeries toRealSeries
  rw [expand_coe_square]
  simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,
    Polynomial.map_one,Polynomial.map_X,Polynomial.map_comp,
    Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_add,
    Polynomial.coe_one,Polynomial.coe_X]

lemma powerConcaveAt_iff_real (p a b c : ℤ) :
    BinaryResearch.PowerConcaveAt p a b c ↔
      BinaryPowerConcavity.PC (p:ℝ) (a:ℝ) (b:ℝ) (c:ℝ) := by
  rw [BinaryPowerConcavity.pc_iff_turan]
  unfold BinaryResearch.PowerConcaveAt
  norm_cast

lemma real_pc_to_integer (p a b c : ℤ)
    (h : BinaryPowerConcavity.PC (p:ℝ) (a:ℝ) (b:ℝ) (c:ℝ)) :
    BinaryResearch.PowerConcaveAt p a b c :=
  (powerConcaveAt_iff_real p a b c).mpr h

#print axioms refineSeries_toRealSeries
#print axioms powerConcaveAt_iff_real
end BinaryRealification
