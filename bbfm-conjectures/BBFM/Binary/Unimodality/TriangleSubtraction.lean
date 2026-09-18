import BBFM.Binary.Unimodality.TriangleBinomial

open Finset Polynomial
namespace BinaryShape

lemma uniform_coeff (L k : ℕ) : (uniform L).coeff k = if k < L then 1 else 0 := by
  simp [uniform, finsetSum_coeff, Polynomial.coeff_X_pow]

lemma uniform_square_coeff_low (W k : ℕ) (hk : k ≤ W) :
    ((uniform (W + 1)) ^ 2).coeff k = (k + 1 : ℕ) := by
  rw [pow_two, coeff_mul_uniform_low _ _ _ (by omega)]
  have he : ∀ i ∈ range (k + 1), (uniform (W + 1)).coeff i = 1 := by
    intro i hi
    rw [uniform_coeff, if_pos (by have := mem_range.mp hi; omega)]
  simp only [sum_congr rfl he, sum_const, card_range, nsmul_eq_mul, mul_one]

lemma uniform_square_coeff_high (W k : ℕ) (hk : W < k) :
    ((uniform (W + 1)) ^ 2).coeff k = (2 * W + 1 - k : ℕ) := by
  rw [pow_two, coeff_mul_uniform_high _ _ _ (by omega)]
  simp only [uniform_coeff]
  rw [← sum_filter]
  have he : {i ∈ Ico (k + 1 - (W + 1)) (k + 1) | i < W + 1} =
      Ico (k - W) (W + 1) := by
    ext i
    simp only [mem_filter, mem_Ico]
    omega
  rw [he]
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  congr 1
  omega

noncomputable def centeredTriangle (c W : ℕ) : ℤ[X] :=
  X ^ (c - W) * (uniform (W + 1)) ^ 2

lemma centeredTriangle_coeff (c W k : ℕ) (hW : W ≤ c) :
    (centeredTriangle c W).coeff k =
      if k < c - W then 0 else
        if k ≤ c then (k + 1 - (c - W) : ℕ) else (c + W + 1 - k : ℕ) := by
  unfold centeredTriangle
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hk : k < c - W
  · simp only [if_neg (by omega : ¬ c - W ≤ k), if_pos hk, Nat.cast_zero]
  · rw [if_pos (by omega : c - W ≤ k), if_neg hk]
    by_cases hkc : k ≤ c
    · rw [if_pos hkc, uniform_square_coeff_low W (k - (c - W)) (by omega)]
      congr 1
      omega
    · rw [if_neg hkc, uniform_square_coeff_high W (k - (c - W)) (by omega)]
      congr 1
      omega

lemma centeredTriangle_support (c W k : ℕ) (hW : W ≤ c) (hk : 2 * c < k) :
    (centeredTriangle c W).coeff k = 0 := by
  rw [centeredTriangle_coeff c W k hW, if_neg (by omega : ¬ k < c - W),
    if_neg (by omega : ¬ k ≤ c)]
  have he : c + W + 1 - k = 0 := by omega
  simp only [he, Nat.cast_zero]

lemma centeredTriangle_symm (c W k : ℕ) (hW : W ≤ c) (hk : k ≤ 2 * c) :
    (centeredTriangle c W).coeff k = (centeredTriangle c W).coeff (2 * c - k) := by
  rw [centeredTriangle_coeff c W k hW, centeredTriangle_coeff c W (2 * c - k) hW]
  split_ifs <;> congr 1 <;> omega

lemma centeredTriangle_difference (c W k : ℕ) (hW : W < c)
    (hk : 1 ≤ k) (hkc : k ≤ c) :
    (centeredTriangle c W).coeff k - (centeredTriangle c W).coeff (k - 1) =
      if c - W ≤ k then 1 else 0 := by
  rw [centeredTriangle_coeff c W k hW.le, centeredTriangle_coeff c W (k - 1) hW.le]
  split_ifs <;> push_cast <;> omega

/-- Removing a centered triangle with slopes bounded by the input slopes
preserves the full symmetric nonnegative unimodal shape. -/
theorem centeredTriangle_subtract (P : ℤ[X]) (c W : ℕ) (K : ℤ)
    (hW : W < c) (hK : 0 ≤ K)
    (hsupport : ∀ k, 2 * c < k → P.coeff k = 0)
    (hsymm : ∀ k, k ≤ 2 * c → P.coeff k = P.coeff (2 * c - k))
    (hnonneg : ∀ k, 0 ≤ P.coeff k)
    (hmono : ∀ k, k < c → P.coeff k ≤ P.coeff (k + 1))
    (hslope : ∀ k, c - W ≤ k → k ≤ c → K ≤ P.coeff k - P.coeff (k - 1)) :
    let Q := P - C K * centeredTriangle c W
    (∀ k, 2 * c < k → Q.coeff k = 0) ∧
    (∀ k, k ≤ 2 * c → Q.coeff k = Q.coeff (2 * c - k)) ∧
    (∀ k, 0 ≤ Q.coeff k) ∧
    (∀ k, k < c → Q.coeff k ≤ Q.coeff (k + 1)) := by
  dsimp only
  let Q := P - C K * centeredTriangle c W
  have hc (k : ℕ) : Q.coeff k = P.coeff k - K * (centeredTriangle c W).coeff k := by
    simp only [Q, coeff_sub, coeff_C_mul]
  have hQs : ∀ k, 2 * c < k → Q.coeff k = 0 := by
    intro k hk
    rw [hc, hsupport k hk, centeredTriangle_support c W k hW.le hk]
    ring
  have hQr : ∀ k, k ≤ 2 * c → Q.coeff k = Q.coeff (2 * c - k) := by
    intro k hk
    rw [hc, hc, hsymm k hk, centeredTriangle_symm c W k hW.le hk]
  have hQm : ∀ k, k < c → Q.coeff k ≤ Q.coeff (k + 1) := by
    intro k hk
    rw [hc, hc]
    have hd := centeredTriangle_difference c W (k + 1) hW (by omega) (by omega)
    simp only [Nat.add_sub_cancel] at hd
    by_cases ha : c - W ≤ k + 1
    · rw [if_pos ha] at hd
      have hp := hslope (k + 1) ha (by omega)
      simp only [Nat.add_sub_cancel] at hp
      nlinarith
    · rw [if_neg ha] at hd
      have hp := hmono k hk
      nlinarith
  have hQ0 : 0 ≤ Q.coeff 0 := by
    rw [hc, centeredTriangle_coeff c W 0 hW.le, if_pos (by omega : 0 < c - W)]
    simpa using hnonneg 0
  have hQlo : ∀ k, k ≤ c → 0 ≤ Q.coeff k := by
    intro k hk
    induction k with
    | zero => exact hQ0
    | succ k ih => exact le_trans (ih (by omega)) (hQm k (by omega))
  refine ⟨hQs, hQr, ?_, hQm⟩
  intro k
  by_cases hk : 2 * c < k
  · rw [hQs k hk]
  · by_cases hkc : k ≤ c
    · exact hQlo k hkc
    · rw [hQr k (by omega)]
      exact hQlo _ (by omega)

end BinaryShape

#print axioms BinaryShape.centeredTriangle_subtract
