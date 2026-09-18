import BBFM.Binary.CentralSlope

open Polynomial Finset BinaryShape
namespace BinaryResearch

noncomputable def signedCorrection (m : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ center (2 * m) * amplitude (2 * m)) *
    X ^ center (2 * m) * correction m

lemma signedCorrection_coeff_bounds (m k : ℕ) :
    -amplitude (2 * m + 2) ≤ (signedCorrection m).coeff k ∧
      (signedCorrection m).coeff k ≤ amplitude (2 * m + 2) := by
  rw [signedCorrection, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  have ha := (amplitude_bounds (2 * m)).1.le
  have han := (amplitude_bounds (2 * m + 2)).1.le
  split_ifs with hk
  · have hb := correction_coeff_bounds m (k - center (2 * m))
    have hlo := mul_le_mul_of_nonneg_left hb.1 ha
    have hhi := mul_le_mul_of_nonneg_left hb.2 ha
    rw [amplitude_even]
    rcases neg_one_pow_eq_or ℤ (center (2 * m)) with hs | hs <;> rw [hs] <;>
      constructor <;> nlinarith
  · constructor <;> nlinarith

lemma signedCorrection_difference_bounds (m k : ℕ) :
    -(2 * amplitude (2 * m + 2)) ≤
      (signedCorrection m).coeff k - (signedCorrection m).coeff (k - 1) ∧
    (signedCorrection m).coeff k - (signedCorrection m).coeff (k - 1) ≤
      2 * amplitude (2 * m + 2) := by
  have h := signedCorrection_coeff_bounds m k
  have hp := signedCorrection_coeff_bounds m (k - 1)
  omega

lemma signedCorrection_coeff_low (m k : ℕ) (hk : k < center (2 * m)) :
    (signedCorrection m).coeff k = 0 := by
  rw [signedCorrection, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
    if_neg (by omega : ¬ center (2 * m) ≤ k), mul_zero]

noncomputable def smoothing (t : ℕ) : ℤ[X] :=
  (1 + X) ^ (2 * t - 1) * (numB t).comp (X ^ 2)

lemma residual_step (t : ℕ) (ht : 1 ≤ t) :
    residual (2 * t) = jump (t - 1) * residual (2 * (t - 1)) +
      smoothing t + signedCorrection (t - 1) := by
  have h := residual_recurrence (t - 1)
  simpa only [show 2 * (t - 1) + 2 = 2 * t by omega,
    show 2 * (t - 1) + 1 = 2 * t - 1 by omega,
    show t - 1 + 1 = t by omega, smoothing, signedCorrection] using h

lemma smoothing_shape (t : ℕ) (ht : 1 ≤ t)
    (hh : HasShape (numB (2 * (t / 2))) (2 * center (2 * (t / 2)))) :
    HasShape (smoothing t) (2 * center (2 * t) - 1) := by
  have he : 2 * (2 * center (2 * (t / 2))) + (2 * t - 1) =
      2 * center (2 * t) - 1 := by
    rw [center_double t, center_even_part t]
    omega
  have h := binomial_comp_square_shape _ _ (2 * t - 1) (by omega) hh
  rw [he, ← numB_even_part t] at h
  exact h

lemma geometric_residual_mono (t : ℕ) (ht : 1 ≤ t)
    (hcp : 0 < center (2 * (t - 1)))
    (hr : HasShape (residual (2 * (t - 1))) (2 * center (2 * (t - 1)) - 1))
    (k : ℕ) (hk : k < center (2 * t)) :
    (jump (t - 1) * residual (2 * (t - 1))).coeff k ≤
      (jump (t - 1) * residual (2 * (t - 1))).coeff (k + 1) := by
  have hc := center_step (t - 1)
  rw [show 2 * (t - 1) + 2 = 2 * t by omega] at hc
  have hd : 2 * (center (2 * (t - 1)) - 1) + 1 =
      2 * center (2 * (t - 1)) - 1 := by omega
  have hh := polynomial_odd_geometric_lower_mono (residual (2 * (t - 1)))
    (center (2 * (t - 1)) - 1) (jumpLength (t - 1))
    (by simpa only [hd] using hr.support)
    (by simpa only [hd] using hr.symm) hr.nonneg
    (by simpa only [hd] using hr.mono) k (by omega)
  simpa only [jump_geometric, evenGeometric, mul_comm] using hh

/-- The odd residual gains a large central slope; outside the central window,
the correction is zero and ordinary shape closure suffices. -/
theorem residual_step_differences (t : ℕ) (ht : 49 ≤ t)
    (hr : HasShape (residual (2 * (t - 1))) (2 * center (2 * (t - 1)) - 1))
    (hh : HasShape (numB (2 * (t / 2))) (2 * center (2 * (t / 2))))
    (hs : ∀ k, center (2 * (t / 2)) - (2 * (t / 2) + 2) ≤ k →
      k ≤ center (2 * (t / 2)) →
      (3 : ℤ) ^ (2 * (t / 2)) ≤
        (numB (2 * (t / 2))).coeff k - (numB (2 * (t / 2))).coeff (k - 1)) :
    (∀ k, 1 ≤ k → k < center (2 * t) →
      0 ≤ (residual (2 * t)).coeff k - (residual (2 * t)).coeff (k - 1)) ∧
    (∀ k, center (2 * t) - (2 * t + 2) ≤ k → k < center (2 * t) →
      (3 : ℤ) ^ (2 * t) + 2 * 2 ^ (2 * t) ≤
        (residual (2 * t)).coeff k - (residual (2 * t)).coeff (k - 1)) := by
  have hc := center_window (2 * t) (by omega)
  have hcp := center_window (2 * (t - 1)) (by omega)
  have hA := (amplitude_bounds (2 * t)).2
  have hgeom (k : ℕ) (hk0 : 1 ≤ k) (hkc : k < center (2 * t)) :
      0 ≤ (jump (t - 1) * residual (2 * (t - 1))).coeff k -
        (jump (t - 1) * residual (2 * (t - 1))).coeff (k - 1) := by
    have h := geometric_residual_mono t (by omega) (by omega) hr (k - 1) (by omega)
    simpa only [show k - 1 + 1 = k by omega, sub_nonneg] using h
  have hcentral (k : ℕ) (hklo : center (2 * t) - (2 * t + 2) ≤ k)
      (hkhi : k < center (2 * t)) :
      (3 : ℤ) ^ (2 * t) + 2 * 2 ^ (2 * t) ≤
        (residual (2 * t)).coeff k - (residual (2 * t)).coeff (k - 1) := by
    have hg := hgeom k (by omega) hkhi
    have hb := source_central_slope t (by omega) hh hs k hklo hkhi
    change (3 : ℤ) ^ (2 * t) + 2 ^ (2 * t + 2) ≤
      (smoothing t).coeff k - (smoothing t).coeff (k - 1) at hb
    have he := (signedCorrection_difference_bounds (t - 1) k).1
    rw [show 2 * (t - 1) + 2 = 2 * t by omega] at he
    rw [residual_step t (by omega), coeff_add, coeff_add, coeff_add, coeff_add]
    rw [pow_add] at hb
    norm_num at hb
    linarith
  refine ⟨?_, hcentral⟩
  intro k hk0 hkhi
  by_cases hklo : center (2 * t) - (2 * t + 2) ≤ k
  · have h := hcentral k hklo hkhi
    have hp : 0 ≤ (3 : ℤ) ^ (2 * t) + 2 * 2 ^ (2 * t) := by positivity
    omega
  · have halign := center_step (t - 1)
    rw [show 2 * (t - 1) + 2 = 2 * t by omega] at halign
    have hq := jumpLength_le (t - 1)
    have hklow : k < center (2 * (t - 1)) := by omega
    have hg := hgeom k hk0 hkhi
    have hb := (smoothing_shape t (by omega) hh).mono (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at hb
    rw [residual_step t (by omega), coeff_add, coeff_add, coeff_add, coeff_add,
      signedCorrection_coeff_low _ _ hklow, signedCorrection_coeff_low _ _ (by omega)]
    omega

#print axioms residual_step_differences
end BinaryResearch
