import BBFM.Binary.Recurrence
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.GeomSum

open Polynomial Finset
namespace BinaryResearch

lemma binary_floor_step (m j : ℕ) :
    (2 * m + 2) / 2 ^ (j + 1) - (2 * m) / 2 ^ (j + 1) =
      if 2 ^ j ∣ m + 1 then 1 else 0 := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  have h1 : (2 * m + 2) / 2 = m + 1 := by omega
  have h0 : (2 * m) / 2 = m := by omega
  rw [h1, h0, Nat.succ_div]
  omega

lemma jump_carry_product (m : ℕ) :
    jump m = ∏ j ∈ range (padicValNat 2 (m + 1) + 1), (1 + X ^ (2 ^ (j + 1))) := by
  unfold jump
  rw [Finset.prod_range_succ']
  simp only [ite_true, pow_zero, mul_one]
  have hval : padicValNat 2 (m + 1) ≤ m := by
    have hd : 2 ^ padicValNat 2 (m + 1) ∣ m + 1 := pow_padicValNat_dvd
    have hp := Nat.le_of_dvd (by omega : 0 < m + 1) hd
    have hl := (padicValNat 2 (m + 1)).lt_two_pow_self
    omega
  have he (j : ℕ) :
      (1 + X ^ (2 ^ (j + 1)) : ℤ[X]) ^
        (if j + 1 = 0 then 0 else (2 * m + 2) / 2 ^ (j + 1) - (2 * m) / 2 ^ (j + 1)) =
      if j ≤ padicValNat 2 (m + 1) then 1 + X ^ (2 ^ (j + 1)) else 1 := by
    rw [ite_eq_right (by omega), binary_floor_step]
    have hd := padicValNat_dvd_iff_le_of_ne_one (n := j) (by norm_num : 2 ≠ 1) (by omega : m + 1 ≠ 0)
    by_cases hj : j ≤ padicValNat 2 (m + 1)
    · simp [hj, hd.mpr hj]
    · have hn : ¬ 2 ^ j ∣ m + 1 := fun h => hj (hd.mp h)
      simp [hj, hn]
  simp_rw [he]
  symm
  calc
    ∏ j ∈ range (padicValNat 2 (m + 1) + 1), (1 + X ^ (2 ^ (j + 1)) : ℤ[X]) =
        ∏ j ∈ range (padicValNat 2 (m + 1) + 1),
          (if j ≤ padicValNat 2 (m + 1) then 1 + X ^ (2 ^ (j + 1)) else 1) := by
      apply prod_congr rfl
      intro j hj
      rw [ite_eq_left (by simpa using mem_range.mp hj)]
    _ = _ := by
      apply prod_subset (range_mono (by omega))
      intro j hj hsmall
      simp only [mem_range] at hsmall
      rw [ite_eq_right (by omega)]

lemma binary_product_telescopes (z : ℤ[X]) (t : ℕ) :
    (∏ j ∈ range t, (1 + z ^ (2 ^ j))) * (z - 1) = z ^ (2 ^ t) - 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [prod_range_succ]
    calc
      ((∏ j ∈ range t, (1 + z ^ (2 ^ j))) * (1 + z ^ (2 ^ t))) * (z - 1) =
          (1 + z ^ (2 ^ t)) * ((∏ j ∈ range t, (1 + z ^ (2 ^ j))) * (z - 1)) := by ring
      _ = (1 + z ^ (2 ^ t)) * (z ^ (2 ^ t) - 1) := by rw [ih]
      _ = z ^ (2 ^ (t + 1)) - 1 := by rw [pow_succ, pow_mul]; ring

lemma binary_product_geometric (t : ℕ) :
    (∏ j ∈ range t, (1 + (X : ℤ[X]) ^ (2 ^ (j + 1)))) =
      ∑ r ∈ range (2 ^ t), X ^ (2 * r) := by
  have he : (∏ j ∈ range t, (1 + (X : ℤ[X]) ^ (2 ^ (j + 1)))) =
      ∏ j ∈ range t, (1 + (X ^ 2) ^ (2 ^ j)) := by
    apply prod_congr rfl
    intro j hj
    rw [← pow_mul, ← pow_succ']
  rw [he]
  apply mul_right_cancel₀ (b := ((X : ℤ[X]) ^ 2 - 1))
  · intro h
    have h0 := congrArg (fun P : ℤ[X] => P.coeff 0) h
    norm_num [coeff_sub] at h0
  · rw [binary_product_telescopes]
    have hg := geom_sum_mul ((X : ℤ[X]) ^ 2) (2 ^ t)
    simp_rw [← pow_mul] at hg
    rw [← pow_mul]
    exact hg.symm

/-- Length of the even geometric recurrence factor. -/
def jumpLength (m : ℕ) : ℕ := 2 ^ (padicValNat 2 (m + 1) + 1)

lemma jumpLength_pos (m : ℕ) : 0 < jumpLength m := by unfold jumpLength; positivity
lemma jumpLength_even (m : ℕ) : Even (jumpLength m) := by
  unfold jumpLength
  rw [pow_succ']
  exact even_two_mul _
lemma jumpLength_le (m : ℕ) : jumpLength m ≤ 2 * m + 2 := by
  have hd : 2 ^ padicValNat 2 (m + 1) ∣ m + 1 := pow_padicValNat_dvd
  have hp := Nat.le_of_dvd (by omega : 0 < m + 1) hd
  unfold jumpLength
  rw [pow_succ']
  omega

/-- The actual source recurrence factor is the published even geometric polynomial. -/
theorem jump_geometric (m : ℕ) : jump m = ∑ r ∈ range (jumpLength m), (X : ℤ[X]) ^ (2 * r) := by
  rw [jump_carry_product, binary_product_geometric]
  rfl

#print axioms jump_carry_product
#print axioms jump_geometric
#print axioms jumpLength_le
end BinaryResearch
