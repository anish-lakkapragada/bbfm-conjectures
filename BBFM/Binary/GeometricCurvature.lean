import BBFM.Binary.GeometricCentral

open Polynomial Finset BinaryShape
namespace BinaryResearch

noncomputable def geometricCorrection (m : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ center (2 * m) * amplitude (2 * m)) * X ^ center (2 * m) * jump m

lemma geometricCorrection_coeff_bounds (m k : ℕ) :
    -amplitude (2 * m) ≤ (geometricCorrection m).coeff k ∧
      (geometricCorrection m).coeff k ≤ amplitude (2 * m) := by
  rw [geometricCorrection, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  have ha := (amplitude_bounds (2 * m)).1.le
  split_ifs with hk
  · have hb := jump_coeff_bounded m (k - center (2 * m))
    have hlo := mul_le_mul_of_nonneg_left hb.1 ha
    have hhi := mul_le_mul_of_nonneg_left hb.2 ha
    rcases neg_one_pow_eq_or ℤ (center (2 * m)) with hs | hs <;> rw [hs] <;>
      constructor <;> nlinarith
  · constructor <;> nlinarith

lemma geometricCorrection_intCoeff_bounds (m : ℕ) (z : ℤ) :
    -amplitude (2 * m) ≤ intCoeff (geometricCorrection m) z ∧
      intCoeff (geometricCorrection m) z ≤ amplitude (2 * m) := by
  unfold intCoeff
  split_ifs
  · exact geometricCorrection_coeff_bounds m _
  · have ha := (amplitude_bounds (2 * m)).1.le
    constructor <;> omega

lemma geometricCorrection_curvature_lower (m : ℕ) (z : ℤ) :
    -(4 * amplitude (2 * m)) ≤ curvature (geometricCorrection m) z := by
  have h := geometricCorrection_intCoeff_bounds m z
  have hl := geometricCorrection_intCoeff_bounds m (z - 1)
  have hr := geometricCorrection_intCoeff_bounds m (z + 1)
  dsimp only [curvature]
  omega

lemma intCoeff_add (P Q : ℤ[X]) (z : ℤ) :
    intCoeff (P + Q) z = intCoeff P z + intCoeff Q z := by
  unfold intCoeff
  split_ifs <;> simp [coeff_add]

lemma curvature_add (P Q : ℤ[X]) (z : ℤ) :
    curvature (P + Q) z = curvature P z + curvature Q z := by
  simp only [curvature, intCoeff_add]
  ring

lemma three_power_twice_two (n : ℕ) (hn : 2 ≤ n) : (2 : ℤ) * 2 ^ n ≤ 3 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ]
    have hp : 0 ≤ (2 : ℤ) ^ n := by positivity
    linarith

/-- Unconditional concavity of the source recurrence's geometric summand
throughout the interior of its possible perturbation interval. -/
theorem source_geometric_central_concavity (m : ℕ) (hm : 49 ≤ m)
    (k : ℕ) (hklo : center (2 * m) ≤ k)
    (hkhi : k ≤ center (2 * m) + 2 * jumpLength m - 2) :
    0 ≤ curvature (jump m * numB (2 * m)) k := by
  have hcore := source_geometric_core_curvature m hm k hklo hkhi
  have he := geometricCorrection_curvature_lower m k
  have ha := (amplitude_bounds (2 * m)).2
  have hp := three_power_twice_two (2 * m) (by omega)
  rw [geometric_source_decomposition]
  change 0 ≤ curvature (uniform (2 * jumpLength m) * residual (2 * m) + geometricCorrection m) k
  rw [curvature_add]
  linarith

/-- A full interval of actual geometric-source Turan inequalities, for every
even source index≥98. This is a local lemma, not the full LC endpoint. -/
theorem source_geometric_central_logconcavity (m : ℕ) (hm : 49 ≤ m)
    (k : ℕ) (hklo : center (2 * m) ≤ k)
    (hkhi : k ≤ center (2 * m) + 2 * jumpLength m - 2) :
    (jump m * numB (2 * m)).coeff (k - 1) * (jump m * numB (2 * m)).coeff (k + 1) ≤
      ((jump m * numB (2 * m)).coeff k) ^ 2 := by
  have hnn (j : ℕ) : 0 ≤ (jump m * numB (2 * m)).coeff j := by
    rw [coeff_mul]
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (jump_coeff_bounded m _).1 (numB_nonneg _ _)
  apply concavity_implies_turan _ _ _ (hnn _) (hnn _)
  have hc := source_geometric_central_concavity m hm k hklo hkhi
  have hcenter := center_window (2 * m) (by omega)
  dsimp only [curvature] at hc
  rw [show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega,
    show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega,
    intCoeff_nat, intCoeff_nat, intCoeff_nat] at hc
  omega

#print axioms source_geometric_central_logconcavity
end BinaryResearch
