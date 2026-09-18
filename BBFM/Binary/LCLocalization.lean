import BBFM.Binary.AllUnimodal

open Polynomial Finset BinaryShape
namespace BinaryResearch

lemma intCoeff_X_pow_mul (P : ℤ[X]) (L : ℕ) (z : ℤ) :
    intCoeff (X ^ L * P) z = intCoeff P (z - L) := by
  by_cases hz : 0 ≤ z
  · rw [intCoeff, if_pos hz, coeff_X_pow_mul']
    by_cases hL : (L : ℤ) ≤ z
    · rw [if_pos (by omega : L ≤ z.toNat), intCoeff, if_pos (by omega : 0 ≤ z - L)]
      congr 1
      omega
    · rw [if_neg (by omega : ¬ L ≤ z.toNat), intCoeff, if_neg (by omega : ¬ 0 ≤ z - L)]
  · rw [intCoeff, if_neg hz, intCoeff, if_neg (by omega : ¬ 0 ≤ z - L)]

lemma intCoeff_sub (P Q : ℤ[X]) (z : ℤ) :
    intCoeff (P - Q) z = intCoeff P z - intCoeff Q z := by
  unfold intCoeff
  split_ifs <;> simp [coeff_sub]

lemma intCoeff_one_sub_X_mul (P : ℤ[X]) (z : ℤ) :
    intCoeff ((1 - X) * P) z = intCoeff P z - intCoeff P (z - 1) := by
  rw [sub_mul, one_mul, intCoeff_sub, ← pow_one X, intCoeff_X_pow_mul]
  rfl

def firstDifference (P : ℤ[X]) (z : ℤ) : ℤ := intCoeff P z - intCoeff P (z - 1)

def curvature (P : ℤ[X]) (z : ℤ) : ℤ :=
  2 * intCoeff P z - intCoeff P (z - 1) - intCoeff P (z + 1)

lemma uniform_difference (P : ℤ[X]) (L : ℕ) (z : ℤ) :
    firstDifference (uniform L * P) z = intCoeff P z - intCoeff P (z - L) := by
  rw [firstDifference, ← intCoeff_one_sub_X_mul, ← mul_assoc, one_sub_X_mul_uniform,
    sub_mul, one_mul, intCoeff_sub, intCoeff_X_pow_mul]

lemma uniform_curvature (P : ℤ[X]) (L : ℕ) (z : ℤ) :
    curvature (uniform L * P) z =
      firstDifference P (z - L + 1) - firstDifference P (z + 1) := by
  have he : curvature (uniform L * P) z =
      firstDifference (uniform L * P) z - firstDifference (uniform L * P) (z + 1) := by
    simp only [curvature, firstDifference]
    rw [show z + 1 - 1 = z by ring]
    ring
  rw [he, uniform_difference, uniform_difference]
  simp only [firstDifference]
  rw [show z - L + 1 - 1 = z - L by ring, show z + 1 - 1 = z by ring,
    show z + 1 - L = z - L + 1 by ring]
  ring

lemma intCoeff_upper_mono (P : ℤ[X]) (d : ℕ) (h : HasShape P d)
    (z : ℤ) (hz : (d : ℤ) ≤ 2 * z + 1) : intCoeff P (z + 1) ≤ intCoeff P z := by
  have hm := intCoeff_mono P d h ((d : ℤ) - z - 1) (by omega)
  have hr := intCoeff_reflection P d h.support h.symm
  rw [show (d : ℤ) - z - 1 = (d : ℤ) - (z + 1) by ring,
    show (d : ℤ) - (z + 1) + 1 = (d : ℤ) - z by ring, hr, hr] at hm
  exact hm

/-- A uniform convolution is discretely concave wherever the sliding window
straddles the center of its symmetric unimodal input. -/
theorem uniform_central_concavity (P : ℤ[X]) (d L : ℕ) (h : HasShape P d)
    (z : ℤ) (hlo : (d : ℤ) ≤ 2 * z + 1) (hhi : 2 * (z - L) < d) :
    0 ≤ curvature (uniform L * P) z := by
  rw [uniform_curvature, firstDifference, firstDifference]
  have hl := intCoeff_mono P d h (z - L) hhi
  have hu := intCoeff_upper_mono P d h z hlo
  rw [show z - L + 1 - 1 = z - L by ring, show z + 1 - 1 = z by ring]
  omega

lemma concavity_implies_turan (a b c : ℤ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hconc : b + c ≤ 2 * a) : b * c ≤ a ^ 2 := by
  nlinarith [sq_nonneg (b - c)]

/-- This local LC statement needs only source shape, not an LC hypothesis. -/
theorem uniform_central_logconcavity (P : ℤ[X]) (d L : ℕ) (h : HasShape P d)
    (z : ℤ) (hlo : (d : ℤ) ≤ 2 * z + 1) (hhi : 2 * (z - L) < d) :
    intCoeff (uniform L * P) (z - 1) * intCoeff (uniform L * P) (z + 1) ≤
      intCoeff (uniform L * P) z ^ 2 := by
  have hnn : ∀ k, 0 ≤ (uniform L * P).coeff k := by
    intro k
    rw [coeff_mul]
    apply sum_nonneg
    intro x hx
    exact mul_nonneg (by rw [uniform_coeff]; split_ifs <;> norm_num) (h.nonneg _)
  apply concavity_implies_turan _ _ _ (intCoeff_nonneg _ hnn _) (intCoeff_nonneg _ hnn _)
  have hc := uniform_central_concavity P d L h z hlo hhi
  dsimp only [curvature] at hc
  omega

lemma geometric_source_decomposition (m : ℕ) :
    jump m * numB (2 * m) = uniform (2 * jumpLength m) * residual (2 * m) +
      C ((-1 : ℤ) ^ center (2 * m) * amplitude (2 * m)) * X ^ center (2 * m) * jump m := by
  have hu : (1 + X) * jump m = uniform (2 * jumpLength m) := by
    rw [jump_geometric]
    have hgeom : (∑ r ∈ range (jumpLength m), (X : ℤ[X]) ^ (2 * r)) =
        (uniform (jumpLength m)).comp (X ^ 2) := by
      simp only [uniform, Polynomial.sum_comp, pow_comp, X_comp, ← pow_mul]
    rw [hgeom, uniform_double]
  rw [numB_reconstruction, ← hu]
  ring

#print axioms uniform_central_logconcavity
#print axioms geometric_source_decomposition
end BinaryResearch
