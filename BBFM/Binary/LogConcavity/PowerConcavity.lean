import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace BinaryPowerConcavity

/-- Local power-concavity, expressed without division or powers of coefficients. -/
def PC (p a b c : ℝ) : Prop :=
  (p + 1) * b ^ 2 - b * (a + c) - (p - 1) * a * c ≥ 0

theorem pc_iff_turan (p a b c : ℝ) :
    PC p a b c ↔ p * (b ^ 2 - a * c) ≥ (b - a) * (c - b) := by
  unfold PC
  constructor <;> intro h <;> nlinarith

/-- Convolution by `(1 + X)` raises the local power-concavity parameter by one.
The middle coefficients are positive; the outer coefficients may vanish. -/
theorem bernoulli_pos (p a b c d : ℝ) (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (hd : 0 ≤ d)
    (habc : PC p a b c) (hbcd : PC p b c d) :
    PC (p + 1) (a + b) (b + c) (c + d) := by
  unfold PC at *
  let u := b + (p - 1) * c
  let v := c + (p - 1) * b
  let A := (p + 1) * b ^ 2 - b * c
  let D := (p + 1) * c ^ 2 - b * c
  have hpm : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have he1 : 0 ≤ A - u * a := by dsimp [A, u]; nlinarith [habc]
  have he2 : 0 ≤ D - v * d := by dsimp [D, v]; nlinarith [hbcd]
  have hA : 0 ≤ A := by nlinarith [mul_nonneg (le_of_lt hu) ha]
  have hbase : 0 ≤ 4 * b * c * p * (b - c) ^ 2 := by positivity
  have hfirst : 0 ≤ (v * (b + c + p * (c + d))) * (A - u * a) := by
    positivity
  have hsecond : 0 ≤ (u * (b + c) + p * (A + u * b)) * (D - v * d) := by
    positivity
  have hid :
      u * v * ((p + 1 + 1) * (b + c) ^ 2 -
        (b + c) * ((a + b) + (c + d)) -
        (p + 1 - 1) * (a + b) * (c + d)) =
      4 * b * c * p * (b - c) ^ 2 +
        (v * (b + c + p * (c + d))) * (A - u * a) +
        (u * (b + c) + p * (A + u * b)) * (D - v * d) := by
    dsimp [u, v, A, D]
    ring
  exact nonneg_of_mul_nonneg_right (by linarith) (mul_pos hu hv)

theorem bernoulli_left_zero (p c d : ℝ) (h : PC p 0 c d) :
    PC (p + 1) (0 + 0) (0 + c) (c + d) := by
  unfold PC at *
  nlinarith

theorem bernoulli_right_zero (p a b : ℝ) (h : PC p a b 0) :
    PC (p + 1) (a + b) (b + 0) (0 + 0) := by
  unfold PC at *
  nlinarith

#print axioms bernoulli_pos
#print axioms bernoulli_left_zero
#print axioms bernoulli_right_zero
end BinaryPowerConcavity
