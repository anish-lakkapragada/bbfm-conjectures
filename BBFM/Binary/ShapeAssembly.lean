import BBFM.Binary.UnimodalStep

open Polynomial Finset BinaryShape
namespace BinaryResearch

lemma residual_shape_of_differences (n : ℕ) (hc : 0 < center n)
    (hm : ∀ k, 1 ≤ k → k < center n →
      0 ≤ (residual n).coeff k - (residual n).coeff (k - 1)) :
    HasShape (residual n) (2 * center n - 1) := by
  have hmono (k : ℕ) (hk : 2 * k < 2 * center n - 1) :
      (residual n).coeff k ≤ (residual n).coeff (k + 1) := by
    by_cases hkc : k + 1 < center n
    · have hh := hm (k + 1) (by omega) hkc
      simpa only [Nat.add_sub_cancel, sub_nonneg] using hh
    · have hs := residual_symmetry n k hc (by omega)
      rw [show 2 * center n - 1 - k = k + 1 by omega] at hs
      exact hs.le
  have hlow (k : ℕ) (hk : k < center n) : 0 ≤ (residual n).coeff k := by
    induction k with
    | zero => rw [residual_coeff_zero n hc]; exact b_nonneg n
    | succ k ih => exact le_trans (ih (by omega)) (hmono k (by omega))
  refine ⟨residual_support n, (fun k hk => residual_symmetry n k hc hk), ?_, hmono⟩
  intro k
  by_cases hk : 2 * center n - 1 < k
  · rw [residual_support n k hk]
  · by_cases hkc : k < center n
    · exact hlow k hkc
    · rw [residual_symmetry n k hc (by omega)]
      exact hlow _ (by omega)

lemma numB_reconstruction (n : ℕ) :
    numB n = (1 + X) * residual n + C ((-1 : ℤ) ^ center n * amplitude n) * X ^ center n := by
  rw [residual_identity]
  ring

lemma numB_coeff_off_center (n k : ℕ) (hk : k ≠ center n) :
    (numB n).coeff k = ((1 + X) * residual n).coeff k := by
  rw [numB_reconstruction, coeff_add, coeff_C_mul, coeff_X_pow, if_neg hk]
  ring

lemma smoothing_difference_ge (P : ℤ[X]) (d k : ℕ)
    (hP : HasShape P d) (hk0 : 1 ≤ k) (hkd : 2 * (k - 1) < d) :
    P.coeff k - P.coeff (k - 1) ≤
      ((1 + X) * P).coeff k - ((1 + X) * P).coeff (k - 1) := by
  have hc (j : ℕ) : ((1 + X) * P).coeff j = P.coeff j + intCoeff P ((j : ℤ) - 1) := by
    rw [← intCoeff_nat, intCoeff_one_add_X_mul, intCoeff_nat]
  rw [hc, hc]
  have he : ((k - 1 : ℕ) : ℤ) - 1 = (k : ℤ) - 2 := by omega
  rw [he]
  have hm := intCoeff_mono P d hP ((k : ℤ) - 2) (by omega)
  rw [show (k : ℤ) - 2 + 1 = (k : ℤ) - 1 by ring] at hm
  omega

lemma numB_center_difference (n : ℕ) (hc : 2 ≤ center n) :
    (numB n).coeff (center n) - (numB n).coeff (center n - 1) =
      (residual n).coeff (center n - 1) - (residual n).coeff (center n - 2) +
        (-1 : ℤ) ^ center n * amplitude n := by
  have hsym := residual_symmetry n (center n) (by omega) (by omega)
  rw [show 2 * center n - 1 - center n = center n - 1 by omega] at hsym
  have hcoeff (k : ℕ) (hk : 1 ≤ k) :
      ((1 + X) * residual n).coeff k = (residual n).coeff k + (residual n).coeff (k - 1) := by
    rw [add_mul, one_mul, coeff_add]
    have h := coeff_X_pow_mul' (residual n) 1 k
    rw [pow_one, if_pos hk] at h
    rw [h]
  rw [numB_coeff_off_center n (center n - 1) (by omega),
    numB_reconstruction n, coeff_add, coeff_C_mul, coeff_X_pow, if_pos rfl,
    mul_one, hcoeff _ (by omega), hcoeff _ (by omega), hsym,
    show center n - 1 - 1 = center n - 2 by omega]
  ring

lemma sign_amplitude_lower (n : ℕ) :
    -amplitude n ≤ (-1 : ℤ) ^ center n * amplitude n := by
  have ha := (amplitude_bounds n).1.le
  rcases neg_one_pow_eq_or ℤ (center n) with hs | hs <;> rw [hs] <;> nlinarith

/-- Recover the source shape and its central slope from the stronger odd residual. -/
theorem source_shape_of_residual (n : ℕ) (hn : 48 ≤ n)
    (hr : HasShape (residual n) (2 * center n - 1))
    (hs : ∀ k, center n - (n + 2) ≤ k → k < center n →
      (3 : ℤ) ^ n + 2 * 2 ^ n ≤ (residual n).coeff k - (residual n).coeff (k - 1)) :
    HasShape (numB n) (2 * center n) ∧
    (∀ k, center n - (n + 2) ≤ k → k ≤ center n →
      (3 : ℤ) ^ n ≤ (numB n).coeff k - (numB n).coeff (k - 1)) := by
  have hc := center_window n hn
  have hcenter : (3 : ℤ) ^ n ≤
      (numB n).coeff (center n) - (numB n).coeff (center n - 1) := by
    rw [numB_center_difference n (by omega)]
    have h := hs (center n - 1) (by omega) (by omega)
    rw [show center n - 1 - 1 = center n - 2 by omega] at h
    have ha := (amplitude_bounds n).2
    have hsign := sign_amplitude_lower n
    have hp : 0 ≤ (2 : ℤ) ^ n := by positivity
    linarith
  constructor
  · refine ⟨numB_support n, numB_symmetry n, numB_nonneg n, ?_⟩
    intro k hk
    by_cases he : k + 1 = center n
    · have hp : 0 ≤ (3 : ℤ) ^ n := by positivity
      rw [← he, Nat.add_sub_cancel] at hcenter
      omega
    · rw [numB_coeff_off_center n k (by omega), numB_coeff_off_center n (k + 1) he]
      have h := one_add_X_mul_shape _ _ hr
      exact h.mono k (by omega)
  · intro k hklo hkhi
    by_cases he : k = center n
    · simpa only [he] using hcenter
    · have h := hs k hklo (by omega)
      have hb := smoothing_difference_ge _ _ k hr (by omega) (by omega)
      rw [numB_coeff_off_center n k he, numB_coeff_off_center n (k - 1) (by omega)]
      have hp : 0 ≤ (2 : ℤ) ^ n := by positivity
      linarith

/-- The simultaneous invariant used by strong induction on the even index. -/
structure Strong (n : ℕ) : Prop where
  sourceShape : HasShape (numB n) (2 * center n)
  residualShape : HasShape (residual n) (2 * center n - 1)
  slopes : ∀ k, center n - (n + 2) ≤ k → k ≤ center n →
    (3 : ℤ) ^ n ≤ (numB n).coeff k - (numB n).coeff (k - 1)

/-- Exact all-range induction step; only finitely many source bases remain. -/
theorem strong_step (t : ℕ) (ht : 49 ≤ t)
    (hprev : Strong (2 * (t - 1))) (hhalf : Strong (2 * (t / 2))) :
    Strong (2 * t) := by
  have hd := residual_step_differences t ht hprev.residualShape hhalf.sourceShape hhalf.slopes
  have hr := residual_shape_of_differences (2 * t)
    (by have := center_window (2 * t) (by omega); omega) hd.1
  have hn := source_shape_of_residual (2 * t) (by omega) hr hd.2
  exact ⟨hn.1, hr, hn.2⟩

#print axioms strong_step
end BinaryResearch
