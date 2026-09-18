import BBFM.Binary.CorrectionBounds
import BBFM.Binary.GrowthFour
import BBFM.Binary.Unimodality.BinomialSmoothing

open Polynomial Finset BinaryShape
namespace BinaryResearch

lemma uniform_double (L : ℕ) :
    (1 + X) * (uniform L).comp (X ^ 2) = uniform (2 * L) := by
  ext k
  rw [duplicated_coeff, uniform_coeff, uniform_coeff]
  by_cases hk : k < 2 * L
  · rw [if_pos hk, if_pos (by omega : k / 2 < L)]
  · rw [if_neg hk, if_neg (by omega : ¬ k / 2 < L)]

lemma triangle_smoothing (c W t : ℕ) (ht : 2 ≤ t) :
    (1 + X) ^ (2 * t - 1) * (centeredTriangle c W).comp (X ^ 2) =
      X ^ (2 * (c - W)) *
        ((1 + X) ^ (2 * t - 3) * (uniform (2 * W + 2)) ^ 2) := by
  rw [show 2 * W + 2 = 2 * (W + 1) by omega, ← uniform_double]
  simp only [centeredTriangle, mul_comp, pow_comp, X_comp, ← pow_mul]
  rw [show 2 * t - 1 = (2 * t - 3) + 2 by omega, pow_add]
  ring

/-- A wide triangular component gives a uniform lower bound on every central
first difference after binary composition and binomial smoothing. -/
theorem central_slope_transfer (P : ℤ[X]) (c W t : ℕ) (K : ℤ)
    (ht : 3 ≤ t) (hW : W < c) (htW : t + 1 ≤ W) (hK : 0 ≤ K)
    (hP : HasShape P (2 * c))
    (hslope : ∀ k, c - W ≤ k → k ≤ c → K ≤ P.coeff k - P.coeff (k - 1))
    (k : ℕ) (hklo : t + 2 * c - (2 * t + 2) ≤ k) (hkhi : k < t + 2 * c) :
    K * ((2 * t - 3).choose (t - 2) : ℤ) ≤
      (((1 + X) ^ (2 * t - 1)) * P.comp (X ^ 2)).coeff k -
      (((1 + X) ^ (2 * t - 1)) * P.comp (X ^ 2)).coeff (k - 1) := by
  let Q := P - C K * centeredTriangle c W
  have hQdata := centeredTriangle_subtract P c W K hW hK hP.support hP.symm
    hP.nonneg (fun j hj => hP.mono j (by omega)) hslope
  have hQ : HasShape Q (2 * c) :=
    ⟨hQdata.1, hQdata.2.1, hQdata.2.2.1, fun j hj => hQdata.2.2.2 j (by omega)⟩
  let B := ((1 + X) ^ (2 * t - 1)) * Q.comp (X ^ 2)
  have hB := binomial_comp_square_shape Q (2 * c) (2 * t - 1) (by omega) hQ
  have hk0 : 1 ≤ k := by omega
  have hBdiff : 0 ≤ B.coeff k - B.coeff (k - 1) := by
    have hh := hB.mono (k - 1) (by omega)
    simpa only [show k - 1 + 1 = k by omega, sub_nonneg] using hh
  let u := 2 * (c - W)
  let T : ℤ[X] := (1 + X) ^ (2 * t - 3) * (uniform (2 * W + 2)) ^ 2
  have hdecomp : ((1 + X) ^ (2 * t - 1)) * P.comp (X ^ 2) =
      B + C K * (X ^ u * T) := by
    dsimp only [B, Q, u, T]
    rw [← triangle_smoothing c W t (by omega)]
    simp only [sub_comp, mul_comp, C_comp]
    ring
  have hku : u + 1 ≤ k := by dsimp only [u]; omega
  have hcoeff (j : ℕ) (hj : u ≤ j) :
      (((1 + X) ^ (2 * t - 1)) * P.comp (X ^ 2)).coeff j =
        B.coeff j + K * T.coeff (j - u) := by
    rw [hdecomp, coeff_add, coeff_C_mul, coeff_X_pow_mul', if_pos hj]
  have hT := triangle_binomial_difference (t - 2) (2 * W + 2) (k - u)
    (by omega) (by omega) (by dsimp only [u]; omega) (by dsimp only [u]; omega)
  have he : 2 * (t - 2) + 1 = 2 * t - 3 := by omega
  rw [he] at hT
  change ((2 * t - 3).choose (t - 2) : ℤ) ≤
    T.coeff (k - u) - T.coeff (k - u - 1) at hT
  rw [hcoeff k (by omega), hcoeff (k - 1) (by omega),
    show k - 1 - u = k - u - 1 by omega]
  nlinarith [mul_le_mul_of_nonneg_left hT hK]

lemma numB_even_part (n : ℕ) : numB n = numB (2 * (n / 2)) := by
  have hmod := Nat.mod_two_eq_zero_or_one n
  rcases hmod with he | ho
  · congr 1; omega
  · rw [show n = 2 * (n / 2) + 1 by omega, numB_odd]
    congr 2
    omega

lemma center_even_part (n : ℕ) : center n = center (2 * (n / 2)) := by
  have hmod := Nat.mod_two_eq_zero_or_one n
  rcases hmod with he | ho
  · congr 1; omega
  · rw [show n = 2 * (n / 2) + 1 by omega, center_odd]
    congr 2
    omega

/-- Source-level quantitative step: the half-index numerator pays the next
central slope and all signed residual corrections. -/
theorem source_central_slope (t : ℕ) (ht : 48 ≤ t)
    (hshape : HasShape (numB (2 * (t / 2))) (2 * center (2 * (t / 2))))
    (hslope : ∀ k, center (2 * (t / 2)) - (2 * (t / 2) + 2) ≤ k →
      k ≤ center (2 * (t / 2)) →
      (3 : ℤ) ^ (2 * (t / 2)) ≤
        (numB (2 * (t / 2))).coeff k - (numB (2 * (t / 2))).coeff (k - 1))
    (k : ℕ) (hklo : center (2 * t) - (2 * t + 2) ≤ k) (hkhi : k < center (2 * t)) :
    (3 : ℤ) ^ (2 * t) + 2 ^ (2 * t + 2) ≤
      (((1 + X) ^ (2 * t - 1)) * (numB t).comp (X ^ 2)).coeff k -
      (((1 + X) ^ (2 * t - 1)) * (numB t).comp (X ^ 2)).coeff (k - 1) := by
  have hhalf : 48 ≤ 2 * (t / 2) := by omega
  have hc : center (2 * t) = t + 2 * center (2 * (t / 2)) := by
    rw [center_double, center_even_part t]
  have hbound := central_slope_transfer (numB (2 * (t / 2)))
    (center (2 * (t / 2))) (2 * (t / 2) + 2) t ((3 : ℤ) ^ (2 * (t / 2)))
    (by omega) (center_window _ hhalf) (by omega) (by positivity) hshape hslope k
    (by rwa [← hc]) (by rwa [← hc])
  rw [← numB_even_part t] at hbound
  have hg : (3 : ℤ) ^ (2 * t) + 2 ^ (2 * t + 2) ≤
      3 ^ (t - 1) * ((2 * t - 3).choose (t - 2) : ℤ) := by
    exact_mod_cast central_smoothing_budget_four t ht
  have hp : (3 : ℤ) ^ (t - 1) ≤ 3 ^ (2 * (t / 2)) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  exact le_trans (le_trans hg (mul_le_mul_of_nonneg_right hp (by positivity))) hbound

#print axioms source_central_slope
end BinaryResearch
