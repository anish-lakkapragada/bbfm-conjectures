import BBFM.Binary.LogConcavity.UniformPowerPotential

open Finset BinaryPowerConcavity
namespace BinaryUniformPower

theorem pc_of_nonnegative_concave (p a b c : ℝ) (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hconc : a + c ≤ 2 * b) : PC p a b c := by
  have hs := mul_nonneg (show 0 ≤ 2 * b - (a + c) by linarith)
    (show 0 ≤ 2 * b + (a + c) by positivity)
  have ht : 0 ≤ b ^ 2 - a * c := by nlinarith [sq_nonneg (a - c)]
  have h1 : 0 ≤ b * (2 * b - a - c) := mul_nonneg hb (by linarith)
  have h2 := mul_nonneg (show 0 ≤ p - 1 by linarith) ht
  unfold PC
  nlinarith only [h1, h2]

theorem previous_increase_of_pc (p a b c : ℝ) (hp : 1 ≤ p)
    (hb : 0 < b) (hbc : b < c) (hpc : PC p a b c) : a < b := by
  by_contra hn
  have hab : 0 ≤ a - b := by linarith
  have hcb : 0 < c - b := sub_pos.mpr hbc
  have hpos : 0 < p * b * (c - b) := mul_pos (mul_pos (by linarith) hb) hcb
  have hfirst : 0 ≤ p * b * (a - b) := by positivity
  have hsecond : 0 ≤ (p - 1) * (a - b) * (c - b) := by positivity
  unfold PC at hpc
  nlinarith only [hpc, hpos, hfirst, hsecond]

theorem increasing_prefix_of_final_increase (p : ℝ) (f : ℕ → ℝ) (K : ℕ)
    (hp : 1 ≤ p) (hf : ∀ i ≤ K, 0 < f (i + 1))
    (hpc : ∀ i ≤ K, PC p (f i) (f (i + 1)) (f (i + 2)))
    (hlast : f (K + 1) < f (K + 2)) :
    ∀ i ≤ K + 1, f i < f (i + 1) := by
  induction K with
  | zero =>
    intro i hi
    have h0 := previous_increase_of_pc p (f 0) (f 1) (f 2) hp (hf 0 (by omega)) hlast
      (hpc 0 (by omega))
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact h0
    · exact hlast
  | succ K ih =>
    have hprev := previous_increase_of_pc p (f (K + 1)) (f (K + 2)) (f (K + 3))
      hp (hf (K + 1) (by omega)) hlast (hpc (K + 1) (by omega))
    have hprefix := ih (by intro i hi; exact hf i (by omega))
      (by intro i hi; exact hpc i (by omega)) hprev
    intro i hi
    by_cases hi' : i ≤ K + 1
    · exact hprefix i hi'
    · have he : i = K + 2 := by omega
      simpa only [he] using hlast

/-- A moving sum gains one unit of power-concavity when its underlying window
is strictly increasing and the output second difference is positive. -/
theorem increasing_window_powerConcave (p : ℝ) (f : ℕ → ℝ) (L : ℕ)
    (hp : 1 ≤ p) (hf : ∀ i ≤ L, 0 ≤ f (i + 1))
    (hinc : ∀ i ≤ L, f i < f (i + 1))
    (hpc : ∀ i < L, PC p (f i) (f (i + 1)) (f (i + 2)))
    (hconv : f 1 - f 0 < f (L + 1) - f L) :
    let W := ∑ i ∈ range L, f (i + 1)
    PC (p + 1) (W - f L + f 0) W (W + f (L + 1) - f 1) := by
  exact pc_moving_sum_of_potential_bound p _ (f L) (f (L + 1)) (f 0) (f 1)
    hp (sub_pos.mpr (hinc 0 (by omega))) hconv
    (window_sum_le_potential p f L hp hf hinc hpc)

/-- A cumulative sum is the one-sided boundary case of the same potential
argument. The zero initial value is the missing coefficient before support. -/
theorem increasing_prefix_powerConcave (p : ℝ) (f : ℕ → ℝ) (L : ℕ)
    (hp : 1 ≤ p) (hzero : f 0 = 0)
    (hf : ∀ i ≤ L, 0 ≤ f (i + 1))
    (hinc : ∀ i ≤ L, f i < f (i + 1))
    (hpc : ∀ i < L, PC p (f i) (f (i + 1)) (f (i + 2))) :
    let W := ∑ i ∈ range L, f (i + 1)
    PC (p + 1) (W - f L) W (W + f (L + 1)) := by
  have hsum := window_sum_le_potential p f L hp hf hinc hpc
  simp only [hzero, potential, mul_zero, zero_mul, zero_div, sub_zero] at hsum
  have hden : 0 < (p + 1) * (f (L + 1) - f L) :=
    mul_pos (by linarith) (sub_pos.mpr (hinc L (le_refl L)))
  have hmul := (le_div_iff₀ hden).mp hsum
  dsimp only
  unfold PC
  nlinarith only [hmul]

end BinaryUniformPower

#print axioms BinaryUniformPower.increasing_prefix_of_final_increase
#print axioms BinaryUniformPower.increasing_window_powerConcave
#print axioms BinaryUniformPower.increasing_prefix_powerConcave
