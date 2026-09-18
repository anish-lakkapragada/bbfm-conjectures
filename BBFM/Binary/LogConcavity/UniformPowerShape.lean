import BBFM.Binary.LogConcavity.UniformPowerWindow
import Mathlib.Algebra.BigOperators.Intervals

open Finset BinaryPowerConcavity
namespace BinaryUniformPower

structure SymmetricPositive (f : ℤ → ℝ) (D : ℕ) : Prop where
  nonneg : ∀ z, 0 ≤ f z
  positive : ∀ z : ℤ, 0 ≤ z → z ≤ (D : ℤ) → 0 < f z
  zero_left : ∀ z, z < 0 → f z = 0
  zero_right : ∀ z, (D : ℤ) < z → f z = 0
  reflection : ∀ z, f ((D : ℤ) - z) = f z
  mono : ∀ z : ℤ, 2 * z < (D : ℤ) → f z ≤ f (z + 1)

noncomputable def window (f : ℤ → ℝ) (L : ℕ) (z : ℤ) : ℝ :=
  ∑ j ∈ range L, f (z - j)

lemma window_nonneg (f : ℤ → ℝ) (L : ℕ) (hf : ∀ z, 0 ≤ f z) (z : ℤ) :
    0 ≤ window f L z := sum_nonneg (fun j _ => hf _)

lemma window_difference (f : ℤ → ℝ) (L : ℕ) (z : ℤ) :
    window f L (z + 1) - window f L z = f (z + 1) - f (z + 1 - L) := by
  cases L with
  | zero => simp [window]
  | succ L =>
    have hs : window f (L + 1) (z + 1) = f (z + 1) + window f L z := by
      unfold window
      rw [sum_range_succ']
      simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
      have he : (fun j : ℕ => f (z + 1 - (j + 1))) = (fun j : ℕ => f (z - j)) := by
        funext j
        congr 1
        omega
      rw [he]
      exact add_comm _ _
    have ht : window f (L + 1) z = window f L z + f (z - L) := by
      exact sum_range_succ _ _
    rw [hs, ht]
    have he : z + 1 - ((L + 1 : ℕ) : ℤ) = z - L := by omega
    rw [he]
    ring

lemma window_reflection (f : ℤ → ℝ) (D L : ℕ)
    (hf : ∀ z, f ((D : ℤ) - z) = f z) (z : ℤ) :
    window f L ((D : ℤ) + L - 1 - z) = window f L z := by
  unfold window
  rw [← sum_range_reflect (fun j : ℕ => f (z - j)) L]
  apply sum_congr rfl
  intro j hj
  have hjL : j < L := mem_range.mp hj
  have he : (D : ℤ) + L - 1 - z - j = (D : ℤ) - (z - ((L - 1 - j : ℕ) : ℤ)) := by omega
  rw [he, hf]

lemma shape_comparison (f : ℤ → ℝ) (D : ℕ) (hf : SymmetricPositive f D)
    (a b : ℤ) (hab : a ≤ b) (hsum : a + b ≤ D) : f a ≤ f b := by
  have hlower (a b : ℤ) (hab : a ≤ b) (hb : 2 * b ≤ (D : ℤ) + 1) : f a ≤ f b := by
    have hall : ∀ n : ℕ, 2 * (a + n) ≤ (D : ℤ) + 1 → f a ≤ f (a + n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        have hstep := hf.mono (a + n) (by omega)
        have he : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by omega
        rw [he]
        exact le_trans hprev hstep
    have he : a + ((b - a).toNat : ℤ) = b := by omega
    simpa only [he] using hall (b - a).toNat (by omega)
  by_cases hb : 2 * b ≤ (D : ℤ) + 1
  · exact hlower a b hab hb
  · rw [← hf.reflection b]
    exact hlower a ((D : ℤ) - b) (by omega) (by omega)

lemma window_lower_increasing (f : ℤ → ℝ) (D L : ℕ)
    (hf : SymmetricPositive f D) (z : ℤ) (hz : 2 * z ≤ (D : ℤ) + L) :
    window f L (z - 1) ≤ window f L z := by
  have hd := window_difference f L (z - 1)
  have hcmp := shape_comparison f D hf (z - L) z (by omega) (by omega)
  have he : z - 1 + 1 = z := by omega
  rw [he] at hd
  linarith

lemma window_zero_left (f : ℤ → ℝ) (L : ℕ) (hf : ∀ z, z < 0 → f z = 0)
    (z : ℤ) (hz : z < 0) : window f L z = 0 := by
  apply sum_eq_zero
  intro j hj
  exact hf _ (by omega)

lemma window_reverse_sum (f : ℤ → ℝ) (L : ℕ) (z : ℤ) :
    window f L z = ∑ i ∈ range L, f (z - L + (i + 1)) := by
  unfold window
  rw [← sum_range_reflect (fun j : ℕ => f (z - j)) L]
  apply sum_congr rfl
  intro j hj
  have hjL := mem_range.mp hj
  congr 1
  omega

lemma window_eq_prefix (f : ℤ → ℝ) (L k : ℕ) (hk : k + 1 ≤ L)
    (hf : ∀ z, z < 0 → f z = 0) : window f L k = ∑ i ∈ range (k + 1), f i := by
  have hsplit := sum_range_add_sum_Ico (fun j : ℕ => f ((k : ℤ) - j)) hk
  have hzero : (∑ j ∈ Ico (k + 1) L, f ((k : ℤ) - j)) = 0 := by
    apply sum_eq_zero
    intro j hj
    exact hf _ (by have hh := (mem_Ico.mp hj).1; omega)
  rw [hzero, add_zero] at hsplit
  unfold window
  rw [← hsplit]
  calc
    _ = ∑ j ∈ range (k + 1), f ((k + 1 - 1 - j : ℕ) : ℤ) := by
      apply sum_congr rfl
      intro j hj
      have hh := mem_range.mp hj
      congr 1
      omega
    _ = _ := sum_range_reflect (fun j : ℕ => f j) (k + 1)

end BinaryUniformPower

#print axioms BinaryUniformPower.window_difference
#print axioms BinaryUniformPower.window_reflection
#print axioms BinaryUniformPower.window_lower_increasing
