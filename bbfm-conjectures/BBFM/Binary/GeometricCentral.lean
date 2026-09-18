import BBFM.Binary.LCLocalization

open Polynomial Finset BinaryShape
namespace BinaryResearch

lemma firstDifference_nat (P : ℤ[X]) (k : ℕ) (hk : 1 ≤ k) :
    firstDifference P k = P.coeff k - P.coeff (k - 1) := by
  rw [firstDifference, show (k : ℤ) - 1 = ((k - 1 : ℕ) : ℤ) by omega,
    intCoeff_nat, intCoeff_nat]

lemma firstDifference_reflect (P : ℤ[X]) (d : ℕ) (h : HasShape P d) (z : ℤ) :
    firstDifference P ((d : ℤ) - z + 1) = -firstDifference P z := by
  have hr := intCoeff_reflection P d h.support h.symm
  rw [firstDifference, firstDifference,
    show (d : ℤ) - z + 1 = (d : ℤ) - (z - 1) by ring,
    show (d : ℤ) - (z - 1) - 1 = (d : ℤ) - z by ring, hr, hr]
  ring

lemma firstDifference_lower_nonneg (P : ℤ[X]) (c : ℕ) (hc : 0 < c)
    (h : HasShape P (2 * c - 1)) (z : ℤ) (hz : z ≤ c) :
    0 ≤ firstDifference P z := by
  have hm := intCoeff_mono P (2 * c - 1) h (z - 1) (by omega)
  rw [show z - 1 + 1 = z by ring] at hm
  exact sub_nonneg.mpr hm

/-- Existing central first-difference bounds quantitatively control curvature
throughout the short interval where the binary geometric correction lives. -/
theorem odd_uniform_curvature_lower (P : ℤ[X]) (c q : ℕ) (K : ℤ)
    (hq : 1 ≤ q) (hqc : q < c) (h : HasShape P (2 * c - 1))
    (hs : ∀ k, c - q ≤ k → k < c → K ≤ P.coeff k - P.coeff (k - 1))
    (k : ℕ) (hklo : c ≤ k) (hkhi : k ≤ c + 2 * q - 2) :
    K ≤ curvature (uniform (2 * q) * P) k := by
  have hc : 0 < c := by omega
  let a : ℤ := (k : ℤ) - 2 * q + 1
  let b : ℤ := 2 * c - k - 1
  have hab : a + b = 2 * ((c : ℤ) - q) := by dsimp [a,b]; ring
  have ha : a < c := by dsimp [a]; omega
  have hb : b < c := by dsimp [b]; omega
  have han := firstDifference_lower_nonneg P c hc h a ha.le
  have hbn := firstDifference_lower_nonneg P c hc h b hb.le
  have hstrong (z : ℤ) (hzlo : (c : ℤ) - q ≤ z) (hzhi : z < c) :
      K ≤ firstDifference P z := by
    have hz : 1 ≤ z := by omega
    have he : z = (z.toNat : ℤ) := by omega
    rw [he, firstDifference_nat P z.toNat (by omega)]
    exact hs z.toNat (by omega) (by omega)
  have hr := firstDifference_reflect P (2 * c - 1) h ((k : ℤ) + 1)
  have he : ((2 * c - 1 : ℕ) : ℤ) - ((k : ℤ) + 1) + 1 = b := by dsimp [b]; omega
  rw [he] at hr
  rw [uniform_curvature]
  have harg : (k : ℤ) - (2 * q : ℕ) + 1 = a := by dsimp [a]
  rw [harg]
  by_cases haz : (c : ℤ) - q ≤ a
  · have hh := hstrong a haz ha
    omega
  · have hbz : (c : ℤ) - q ≤ b := by omega
    have hh := hstrong b hbz hb
    omega

theorem residual_central_slopes_even (m : ℕ) (hm : 49 ≤ m)
    (k : ℕ) (hklo : center (2 * m) - (2 * m + 2) ≤ k) (hkhi : k < center (2 * m)) :
    (3 : ℤ) ^ (2 * m) + 2 * 2 ^ (2 * m) ≤
      (residual (2 * m)).coeff k - (residual (2 * m)).coeff (k - 1) := by
  exact (residual_step_differences m hm (strong_even (m - 1) (by omega)).residualShape
    (strong_even (m / 2) (by omega)).sourceShape
    (strong_even (m / 2) (by omega)).slopes).2 k hklo hkhi

/-- An unconditional quantitative estimate on the unperturbed geometric core. -/
theorem source_geometric_core_curvature (m : ℕ) (hm : 49 ≤ m)
    (k : ℕ) (hklo : center (2 * m) ≤ k)
    (hkhi : k ≤ center (2 * m) + 2 * jumpLength m - 2) :
    (3 : ℤ) ^ (2 * m) + 2 * 2 ^ (2 * m) ≤
      curvature (uniform (2 * jumpLength m) * residual (2 * m)) k := by
  have hc := center_window (2 * m) (by omega)
  have hq := jumpLength_le m
  apply odd_uniform_curvature_lower _ (center (2 * m)) (jumpLength m) _
    (jumpLength_pos m) (by omega) (strong_even m (by omega)).residualShape _ k hklo hkhi
  intro j hjlo hjhi
  exact residual_central_slopes_even m hm j (by omega) hjhi

#print axioms source_geometric_core_curvature
end BinaryResearch
