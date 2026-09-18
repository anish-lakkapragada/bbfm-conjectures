import BBFM.Binary.LogConcavity.UniformPowerClosure
import BBFM.Binary.LogConcavity.UniformClosure
import BBFM.Binary.LogConcavity.RealificationBridge

open Polynomial Finset BinaryShape BinaryResearch
namespace BinaryUniformPower

lemma intCoeff_mul_uniform (P : ℤ[X]) (L : ℕ) (z : ℤ) :
    intCoeff (P * uniform L) z = ∑ j ∈ range L, intCoeff P (z - j) := by
  by_cases hz : 0 ≤ z
  · simp only [intCoeff, if_pos hz, uniform, mul_sum, finsetSum_coeff]
    apply sum_congr rfl
    intro j hj
    rw [coeff_mul_X_pow']
    by_cases hjz : j ≤ z.toNat
    · have hzj : 0 ≤ z - j := by omega
      have he : (z - j).toNat = z.toNat - j := by omega
      simp only [if_pos hjz, if_pos hzj, he]
    · have hzj : ¬ 0 ≤ z - j := by omega
      simp only [if_neg hjz, if_neg hzj]
  · rw [intCoeff, if_neg hz]
    symm
    apply sum_eq_zero
    intro j hj
    exact if_neg (by omega)

theorem shape_realification (P : ℤ[X]) (D : ℕ) (hP : HasShape P D)
    (hzero : 0 < P.coeff 0) :
    SymmetricPositive (fun z => (intCoeff P z : ℝ)) D := by
  constructor
  · intro z
    exact_mod_cast intCoeff_nonneg P hP.nonneg z
  · intro z hz hzD
    rw [intCoeff, if_pos hz]
    exact_mod_cast BinaryLC.shape_positive P D hP hzero z.toNat (by omega)
  · intro z hz
    simp only [intCoeff, if_neg (show ¬ 0 ≤ z by omega), Int.cast_zero]
  · intro z hz
    have hz0 : 0 ≤ z := by omega
    rw [intCoeff, if_pos hz0, hP.support z.toNat (by omega), Int.cast_zero]
  · intro z
    rw [intCoeff_reflection P D hP.support hP.symm]
  · intro z hz
    exact_mod_cast intCoeff_mono P D hP z hz

/-- A uniform polynomial of any positive length raises the quantitative
power-concavity parameter by one. This applies to every positive symmetric
unimodal integer polynomial satisfying the input PC inequality. -/
theorem uniform_preserves_powerConcave (P : ℤ[X]) (D L : ℕ) (p : ℤ)
    (hp : 1 ≤ p) (hL : 1 ≤ L) (hshape : HasShape P D)
    (hzero : 0 < P.coeff 0) (hpc : PowerConcave p P) :
    PowerConcave (p + 1) (P * uniform L) := by
  let f : ℤ → ℝ := fun z => (intCoeff P z : ℝ)
  have hfr : SymmetricPositive f D := shape_realification P D hshape hzero
  have hfpc : ∀ z : ℤ, BinaryPowerConcavity.PC (p : ℝ) (f (z - 1)) (f z) (f (z + 1)) := by
    intro z
    exact (BinaryRealification.powerConcaveAt_iff_real _ _ _ _).mp (hpc z)
  have hout := window_powerConcave (p : ℝ) f D L (by exact_mod_cast hp) hL hfr hfpc
  have he (z : ℤ) : window f L z = (intCoeff (P * uniform L) z : ℝ) := by
    rw [intCoeff_mul_uniform]
    simp [window, f]
  intro z
  apply BinaryRealification.real_pc_to_integer
  have hh := hout z
  rw [he, he, he] at hh
  simpa only [Int.cast_add, Int.cast_one] using hh

end BinaryUniformPower

#print axioms BinaryUniformPower.uniform_preserves_powerConcave
