import BBFM.Binary.GeometricCurvature
import BBFM.Binary.Positivity
import BBFM.Binary.LogConcavity.UniformClosure

open Polynomial Finset BinaryShape BinaryLC
namespace BinaryResearch

lemma geometric_source_nonneg (m k : ℕ) : 0 ≤ (jump m * numB (2 * m)).coeff k := by
  rw [coeff_mul]
  apply sum_nonneg
  intro x hx
  exact mul_nonneg (jump_coeff_bounded m _).1 (numB_nonneg _ _)

lemma geometricCorrection_coeff_low (m k : ℕ) (hk : k < center (2 * m)) :
    (geometricCorrection m).coeff k = 0 := by
  rw [geometricCorrection, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    if_neg (by omega : ¬ center (2 * m) ≤ k), mul_zero]

lemma geometric_source_coeff_decomposition (m k : ℕ) :
    (jump m * numB (2 * m)).coeff k =
      (uniform (2 * jumpLength m) * residual (2 * m)).coeff k +
        (geometricCorrection m).coeff k := by
  rw [geometric_source_decomposition, coeff_add]
  rfl

lemma center_sign_even_index (m : ℕ) : (-1 : ℤ) ^ center (2 * m) = (-1 : ℤ) ^ m := by
  rw [center_double, pow_add, pow_mul]
  norm_num

lemma jumpLength_of_even (m : ℕ) (hm : Even m) : jumpLength m = 2 := by
  have hn : ¬ 2 ∣ m + 1 := by
    obtain ⟨r, hr⟩ := hm
    omega
  rw [jumpLength, padicValNat.eq_zero_of_not_dvd hn]
  norm_num

lemma geometricCorrection_nonpos_of_odd (m k : ℕ) (hm : Odd m) :
    (geometricCorrection m).coeff k ≤ 0 := by
  rw [geometricCorrection, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    center_sign_even_index, hm.neg_one_pow]
  have ha := (amplitude_bounds (2 * m)).1.le
  split_ifs
  · have hj := (jump_coeff_bounded m (k - center (2 * m))).1
    nlinarith
  · simp

lemma residual_center_firstDifference (m : ℕ) (hm : 1 ≤ m) :
    firstDifference (residual (2 * m)) (center (2 * m)) = 0 := by
  have hc : 0 < center (2 * m) := by rw [center_double]; omega
  rw [firstDifference_nat _ _ (by omega)]
  have hr := residual_symmetry (2 * m) (center (2 * m)) hc (by omega)
  rw [show 2 * center (2 * m) - 1 - center (2 * m) = center (2 * m) - 1 by omega] at hr
  omega

lemma geometric_core_lower_boundary_curvature (m : ℕ) (hm : 49 ≤ m)
    (hq : jumpLength m = 2) :
    (3 : ℤ) ^ (2 * m) + 2 * 2 ^ (2 * m) ≤
      curvature (uniform (2 * jumpLength m) * residual (2 * m)) (center (2 * m) - 1 : ℕ) := by
  have hc := center_window (2 * m) (by omega)
  rw [uniform_curvature, hq]
  have he1 : ((center (2 * m) - 1 : ℕ) : ℤ) - (2 * 2 : ℕ) + 1 =
      ((center (2 * m) - 4 : ℕ) : ℤ) := by omega
  have he2 : ((center (2 * m) - 1 : ℕ) : ℤ) + 1 = (center (2 * m) : ℤ) := by omega
  rw [he1, he2, residual_center_firstDifference m (by omega), sub_zero,
    firstDifference_nat _ _ (by omega)]
  exact residual_central_slopes_even m hm _ (by omega) (by omega)

theorem geometric_source_lower_boundary_lc (m : ℕ) (hm : 49 ≤ m)
    (hR : ∀ k, 1 ≤ k → (residual (2 * m)).coeff (k - 1) *
      (residual (2 * m)).coeff (k + 1) ≤ ((residual (2 * m)).coeff k) ^ 2) :
    (jump m * numB (2 * m)).coeff (center (2 * m) - 2) *
      (jump m * numB (2 * m)).coeff (center (2 * m)) ≤
      ((jump m * numB (2 * m)).coeff (center (2 * m) - 1)) ^ 2 := by
  have hc := center_window (2 * m) (by omega)
  rcases Nat.even_or_odd m with heven | hodd
  · have hcore := geometric_core_lower_boundary_curvature m hm (jumpLength_of_even m heven)
    have he := geometricCorrection_curvature_lower m (center (2 * m) - 1 : ℕ)
    have ha := (amplitude_bounds (2 * m)).2
    have hp := three_power_twice_two (2 * m) (by omega)
    have hcurv : 0 ≤ curvature (jump m * numB (2 * m)) (center (2 * m) - 1 : ℕ) := by
      rw [geometric_source_decomposition]
      change 0 ≤ curvature (uniform (2 * jumpLength m) * residual (2 * m) + geometricCorrection m) _
      rw [curvature_add]
      linarith
    apply concavity_implies_turan _ _ _ (geometric_source_nonneg m _) (geometric_source_nonneg m _)
    dsimp only [curvature] at hcurv
    rw [show ((center (2 * m) - 1 : ℕ) : ℤ) - 1 = ((center (2 * m) - 2 : ℕ) : ℤ) by omega,
      show ((center (2 * m) - 1 : ℕ) : ℤ) + 1 = (center (2 * m) : ℤ) by omega,
      intCoeff_nat, intCoeff_nat, intCoeff_nat] at hcurv
    omega
  · have hcore := logconcave_uniform_mul (residual (2 * m)) (2 * center (2 * m) - 1)
      (2 * jumpLength m) (residual_support _) (residual_coeff_pos_even m (by omega)) hR
      (center (2 * m) - 1) (by omega)
    rw [show center (2 * m) - 1 - 1 = center (2 * m) - 2 by omega,
      show center (2 * m) - 1 + 1 = center (2 * m) by omega] at hcore
    have hlo : (jump m * numB (2 * m)).coeff (center (2 * m) - 2) =
        (uniform (2 * jumpLength m) * residual (2 * m)).coeff (center (2 * m) - 2) := by
      rw [geometric_source_coeff_decomposition, geometricCorrection_coeff_low _ _ (by omega), add_zero]
    have hmid : (jump m * numB (2 * m)).coeff (center (2 * m) - 1) =
        (uniform (2 * jumpLength m) * residual (2 * m)).coeff (center (2 * m) - 1) := by
      rw [geometric_source_coeff_decomposition, geometricCorrection_coeff_low _ _ (by omega), add_zero]
    have hhi : (jump m * numB (2 * m)).coeff (center (2 * m)) ≤
        (uniform (2 * jumpLength m) * residual (2 * m)).coeff (center (2 * m)) := by
      rw [geometric_source_coeff_decomposition]
      have h := geometricCorrection_nonpos_of_odd m (center (2 * m)) hodd
      omega
    have hh := mul_le_mul_of_nonneg_left hhi (geometric_source_nonneg m (center (2 * m) - 2))
    rw [hlo, hmid]
    rw [hlo] at hh
    exact hh.trans hcore

#print axioms geometric_source_lower_boundary_lc
end BinaryResearch
