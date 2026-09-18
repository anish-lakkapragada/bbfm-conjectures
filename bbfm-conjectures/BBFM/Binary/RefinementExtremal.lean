import BBFM.Binary.PowerConcavity

open Polynomial Finset
namespace BinaryResearch

def powerDefect (p a b c : ℤ) : ℤ :=
  p * (b ^ 2 - a * c) - (b - a) * (c - b)

lemma powerConcaveAt_iff_defect (p a b c : ℤ) :
    PowerConcaveAt p a b c ↔ 0 ≤ powerDefect p a b c := by
  simp only [PowerConcaveAt, powerDefect, sub_nonneg]

/-- At an even coefficient of the minimal binomial refinement mask, the
quadratic dependence on the last input coefficient cancels exactly. -/
lemma even_refinement_defect_difference (r A B C x y : ℤ) :
    powerDefect (r - 1) A (B + y) (C + r * y) -
      powerDefect (r - 1) A (B + x) (C + r * x) =
      (y - x) * (r * B - C - (r - 1) ^ 2 * A) := by
  unfold powerDefect
  ring

lemma even_refinement_defect_antitone (r A B C x y : ℤ)
    (hAB : r * B ≤ (r - 1) ^ 2 * A) (hC : 0 ≤ C) (hxy : x ≤ y) :
    powerDefect (r - 1) A (B + y) (C + r * y) ≤
      powerDefect (r - 1) A (B + x) (C + r * x) := by
  have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxy)
    (show r * B - C - (r - 1) ^ 2 * A ≤ 0 by omega)
  rw [← even_refinement_defect_difference] at h
  omega

lemma odd_refinement_defect_antitone (r A B C x y : ℤ)
    (hr : 2 ≤ r) (hA : 0 ≤ A) (hB : 0 ≤ B) (hxy : x ≤ y) :
    powerDefect (r - 1) A B (C + y) ≤ powerDefect (r - 1) A B (C + x) := by
  have h := mul_nonneg (sub_nonneg.mpr hxy)
    (show 0 ≤ B + (r - 2) * A by positivity)
  unfold powerDefect
  nlinarith

lemma choose_refinement_bound (r t : ℕ) (hr : 2 ≤ r) (ht : 2 ≤ t) :
    (r : ℤ) * r.choose t ≤ ((r : ℤ) - 1) ^ 2 * r.choose (t - 1) := by
  have he := Nat.choose_succ_right_eq r (t - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at he
  have hs : 2 * r.choose t ≤ (r - 1) * r.choose (t - 1) := by
    calc
      _ ≤ t * r.choose t := Nat.mul_le_mul_right _ ht
      _ = (r - (t - 1)) * r.choose (t - 1) := by nlinarith [he]
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hsZ : (2 : ℤ) * r.choose t ≤ (r - 1 : ℕ) * r.choose (t - 1) := by
    exact_mod_cast hs
  rw [Nat.cast_sub (by omega : 1 ≤ r)] at hsZ
  norm_num only [Nat.cast_one] at hsZ
  have hrZ : (2 : ℤ) ≤ r := by exact_mod_cast hr
  have hscaled := mul_le_mul_of_nonneg_left hsZ (Nat.cast_nonneg r : (0 : ℤ) ≤ r)
  have hslack := mul_nonneg
    (mul_nonneg (show 0 ≤ (r : ℤ) - 1 by omega) (show 0 ≤ (r : ℤ) - 2 by omega))
    (Nat.cast_nonneg (r.choose (t - 1)) : (0 : ℤ) ≤ r.choose (t - 1))
  nlinarith

/-- The coefficient bound needed for even-index last-input monotonicity is
automatic for any nonnegative earlier coefficients. -/
theorem lower_refinement_growth (r l : ℕ) (hr : 2 ≤ r) (a : ℕ → ℤ)
    (ha : ∀ i < l, 0 ≤ a i) :
    (r : ℤ) * (∑ i ∈ range l, (r.choose (2 * l - 2 * i) : ℤ) * a i) ≤
      ((r : ℤ) - 1) ^ 2 *
        (∑ i ∈ range l, (r.choose (2 * l - 1 - 2 * i) : ℤ) * a i) := by
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro i hi
  have hil : i < l := mem_range.mp hi
  have ht : 2 ≤ 2 * l - 2 * i := by omega
  have h := mul_le_mul_of_nonneg_right (choose_refinement_bound r (2 * l - 2 * i) hr ht)
    (ha i hil)
  have hd : 2 * l - 2 * i - 1 = 2 * l - 1 - 2 * i := by omega
  simpa only [hd, mul_assoc] using h

#print axioms even_refinement_defect_antitone
#print axioms odd_refinement_defect_antitone
#print axioms lower_refinement_growth
end BinaryResearch
