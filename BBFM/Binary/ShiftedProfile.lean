import BBFM.Binary.NegativeBinomial
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Real.Basic

open Finset PowerSeries
namespace BinaryResearch
noncomputable section

/-- A shifted equality profile, scaled by `p!` to avoid division. -/
def shiftedProfile (p : ℕ) (h : ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ range p, (h + k + i + 1)

lemma shiftedProfile_positive (p : ℕ) (h : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    0 < shiftedProfile p h k := by
  apply prod_pos
  intro i hi
  positivity

lemma shiftedProfile_recurrence (p : ℕ) (h : ℝ) (k : ℕ) :
    (h + k + 1) * shiftedProfile p h (k + 1) =
      (h + k + p + 1) * shiftedProfile p h k := by
  induction p with
  | zero => simp [shiftedProfile]
  | succ p ih =>
    simp only [shiftedProfile, prod_range_succ] at ih ⊢
    push_cast at ih ⊢
    linear_combination (h + k + p + 2) * ih

lemma series_coeff_add (k : ℕ) (A B : ℝ⟦X⟧) :
    PowerSeries.coeff k (A + B) = PowerSeries.coeff k A + PowerSeries.coeff k B := map_add _ _ _

def shiftedSeries (p : ℕ) (h : ℝ) : ℝ⟦X⟧ := PowerSeries.mk (shiftedProfile p h)

@[simp] lemma shiftedSeries_coeff (p : ℕ) (h : ℝ) (k : ℕ) :
    PowerSeries.coeff k (shiftedSeries p h) = shiftedProfile p h k := by
  simp [shiftedSeries]

def eulerSeries (A : ℝ⟦X⟧) : ℝ⟦X⟧ := X * PowerSeries.derivative ℝ A

@[simp] lemma eulerSeries_coeff (A : ℝ⟦X⟧) (k : ℕ) :
    PowerSeries.coeff k (eulerSeries A) = k * PowerSeries.coeff k A := by
  cases k with
  | zero => simp [eulerSeries]
  | succ k => simp [eulerSeries, coeff_succ_X_mul, coeff_derivative, mul_comm]

theorem shiftedSeries_ode (p : ℕ) (h : ℝ) :
    eulerSeries (shiftedSeries p h) + C h * shiftedSeries p h =
      X * (eulerSeries (shiftedSeries p h) + C (p + h + 1) * shiftedSeries p h) +
        C (h * shiftedProfile p h 0) := by
  ext k
  cases k with
  | zero => simp [eulerSeries, shiftedSeries]
  | succ k =>
    simp only [series_coeff_add, coeff_C_mul, eulerSeries_coeff, shiftedSeries_coeff,
      coeff_succ_X_mul, coeff_C, Nat.succ_ne_zero, ite_false, add_zero]
    have he := shiftedProfile_recurrence p h k
    push_cast at he ⊢
    linear_combination he

lemma eulerSeries_expand_two (A : ℝ⟦X⟧) :
    eulerSeries (PowerSeries.expand 2 (by omega) A) =
      2 * PowerSeries.expand 2 (by omega) (eulerSeries A) := by
  unfold eulerSeries
  rw [PowerSeries.expand_apply, PowerSeries.derivative_subst (PowerSeries.HasSubst.X_pow (by omega))]
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_X]
  simp only [show 2 - 1 = 1 by omega, pow_one, mul_one]
  rw [map_mul, PowerSeries.expand_X, PowerSeries.expand_apply]
  ring

lemma eulerSeries_binomial_mul (p : ℕ) (A : ℝ⟦X⟧) :
    eulerSeries ((1 + X) ^ (p + 1) * A) =
      ((p + 1 : ℕ) : ℝ⟦X⟧) * X * (1 + X) ^ p * A + (1 + X) ^ (p + 1) * eulerSeries A := by
  unfold eulerSeries
  rw [Derivation.leibniz, PowerSeries.derivative_pow]
  simp only [Nat.add_sub_cancel, map_add, PowerSeries.derivative_one,
    PowerSeries.derivative_X, zero_add, mul_one]
  push_cast
  ring

def refinedShiftedSeries (p : ℕ) (h : ℝ) : ℝ⟦X⟧ :=
  (1 + X) ^ (p + 1) * PowerSeries.expand 2 (by omega) (shiftedSeries p h)

/-- The inhomogeneous first-order recurrence behind the boundary proof. -/
theorem refinedShiftedSeries_ode (p : ℕ) (h : ℝ) :
    eulerSeries (refinedShiftedSeries p h) + C (2 * h) * refinedShiftedSeries p h =
      X * (eulerSeries (refinedShiftedSeries p h) +
        C (p + 2 * h + 1) * refinedShiftedSeries p h) +
      C (2 * h * shiftedProfile p h 0) * (1 + X) ^ p := by
  have he := congrArg (PowerSeries.expand 2 (by omega)) (shiftedSeries_ode p h)
  simp only [map_add, map_mul, PowerSeries.expand_X, PowerSeries.expand_C] at he
  unfold refinedShiftedSeries
  rw [eulerSeries_binomial_mul, eulerSeries_expand_two]
  simp only [map_mul, map_add, map_natCast, map_one] at he ⊢
  rw [pow_succ]
  norm_num only [map_ofNat, Nat.cast_add, Nat.cast_one] at he ⊢
  linear_combination 2 * (1 + X) ^ p * he

theorem refinedShiftedSeries_recurrence (p k : ℕ) (h : ℝ) :
    (k + 1 + 2 * h) * PowerSeries.coeff (k + 1) (refinedShiftedSeries p h) =
      (k + p + 2 * h + 1) * PowerSeries.coeff k (refinedShiftedSeries p h) +
      2 * h * shiftedProfile p h 0 *
        PowerSeries.coeff (k + 1) ((1 + X : ℝ⟦X⟧) ^ p) := by
  have he := congrArg (PowerSeries.coeff (k + 1)) (refinedShiftedSeries_ode p h)
  simp only [series_coeff_add, coeff_C_mul, eulerSeries_coeff, coeff_succ_X_mul] at he
  push_cast at he ⊢
  linear_combination he

#print axioms shiftedProfile_recurrence
#print axioms refinedShiftedSeries_ode
#print axioms refinedShiftedSeries_recurrence
end
end BinaryResearch
