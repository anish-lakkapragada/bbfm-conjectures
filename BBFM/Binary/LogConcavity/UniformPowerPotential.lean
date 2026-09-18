import BBFM.Binary.LogConcavity.PowerConcavity

open Finset BinaryPowerConcavity
namespace BinaryUniformPower

/-- A discrete antiderivative bound for a positive increasing PC profile. -/
noncomputable def potential (p a b : ℝ) : ℝ :=
  p * a * b / ((p + 1) * (b - a))

theorem potential_step_identity (p a b c : ℝ)
    (hp : p + 1 ≠ 0) (hab : b - a ≠ 0) (hbc : c - b ≠ 0) :
    (p + 1) * (b - a) * (c - b) *
      (potential p b c - potential p a b - b) =
      b * ((p + 1) * b ^ 2 - b * (a + c) - (p - 1) * a * c) := by
  unfold potential
  field_simp
  <;> ring

theorem potential_step (p a b c : ℝ) (hp : 1 ≤ p)
    (hb : 0 ≤ b) (hab : a < b) (hbc : b < c) (hpc : PC p a b c) :
    b ≤ potential p b c - potential p a b := by
  have hp1 : 0 < p + 1 := by linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  have hcb : 0 < c - b := sub_pos.mpr hbc
  have he := potential_step_identity p a b c hp1.ne' hba.ne' hcb.ne'
  have hn : 0 ≤ b * ((p + 1) * b ^ 2 - b * (a + c) - (p - 1) * a * c) :=
    mul_nonneg hb hpc
  rw [← he] at hn
  have hdiff := nonneg_of_mul_nonneg_right hn (mul_pos (mul_pos hp1 hba) hcb)
  linarith

theorem window_sum_le_potential (p : ℝ) (f : ℕ → ℝ) (L : ℕ)
    (hp : 1 ≤ p) (hf : ∀ i ≤ L, 0 ≤ f (i + 1))
    (hinc : ∀ i ≤ L, f i < f (i + 1))
    (hpc : ∀ i < L, PC p (f i) (f (i + 1)) (f (i + 2))) :
    (∑ i ∈ range L, f (i + 1)) ≤
      potential p (f L) (f (L + 1)) - potential p (f 0) (f 1) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hprev := ih (by intro i hi; exact hf i (by omega))
      (by intro i hi; exact hinc i (by omega))
      (by intro i hi; exact hpc i (by omega))
    have hlast := potential_step p (f L) (f (L + 1)) (f (L + 2)) hp
      (hf L (by omega)) (hinc L (by omega)) (hinc (L + 1) (le_refl _))
      (hpc L (by omega))
    rw [sum_range_succ]
    change (∑ i ∈ range L, f (i + 1)) + f (L + 1) ≤
      potential p (f (L + 1)) (f (L + 2)) - potential p (f 0) (f 1)
    linarith

/-- Exact endpoint comparison; the remainder is a square. -/
theorem potential_window_identity (p a c u v : ℝ)
    (hp : p + 1 ≠ 0) (hB : c - a ≠ 0) (hV : v - u ≠ 0)
    (hBV : (c - a) - (v - u) ≠ 0) :
    (p + 1) * (c - a) * (v - u) * ((c - a) - (v - u)) *
      (p * (a - u) * (c - v) / ((p + 1) * ((c - a) - (v - u))) -
        (potential p a c - potential p u v)) =
      p * ((c - a) * u - (v - u) * a) ^ 2 := by
  unfold potential
  field_simp
  <;> ring

theorem potential_window_bound (p a c u v : ℝ) (hp : 1 ≤ p)
    (hV : 0 < v - u) (hBV : v - u < c - a) :
    potential p a c - potential p u v ≤
      p * (a - u) * (c - v) / ((p + 1) * ((c - a) - (v - u))) := by
  have hp1 : 0 < p + 1 := by linarith
  have hB : 0 < c - a := lt_trans hV hBV
  have hd : 0 < (c - a) - (v - u) := sub_pos.mpr hBV
  have he := potential_window_identity p a c u v hp1.ne' hB.ne' hV.ne' hd.ne'
  have hn : 0 ≤ p * ((c - a) * u - (v - u) * a) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  rw [← he] at hn
  have hdiff := nonneg_of_mul_nonneg_right hn
    (mul_pos (mul_pos (mul_pos hp1 hB) hV) hd)
  linarith

theorem pc_moving_sum_of_potential_bound (p W a c u v : ℝ) (hp : 1 ≤ p)
    (hV : 0 < v - u) (hBV : v - u < c - a)
    (hW : W ≤ potential p a c - potential p u v) :
    PC (p + 1) (W - a + u) W (W + c - v) := by
  have hbound := le_trans hW (potential_window_bound p a c u v hp hV hBV)
  have hden : 0 < (p + 1) * ((c - a) - (v - u)) := by positivity
  have hmul := (le_div_iff₀ hden).mp hbound
  unfold PC
  nlinarith only [hmul]

end BinaryUniformPower

#print axioms BinaryUniformPower.potential_step
#print axioms BinaryUniformPower.window_sum_le_potential
#print axioms BinaryUniformPower.potential_window_bound
#print axioms BinaryUniformPower.pc_moving_sum_of_potential_bound
