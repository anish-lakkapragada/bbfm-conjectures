import BBFM.Binary.SignInterval

namespace BinaryResearch

/-- The extremal PC ratio recurrence is order preserving. This is an integral,
division-free comparison with an equality profile. -/
theorem power_ratio_comparison_step (p a b c A B C : ℤ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (hf : PowerConcaveAt p a b c) (hg : powerDefect p A B C = 0)
    (hcomp : b * A ≤ B * a) : c * B ≤ C * b := by
  let u := b + (p - 1) * a
  let U := B + (p - 1) * A
  let v := (p + 1) * b - a
  let V := (p + 1) * B - A
  have hu : 0 < u := by dsimp [u]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hf' : c * u ≤ b * v := (powerConcaveAt_iff p a b c).mp hf
  have hg' : C * U = B * V := by
    dsimp [U, V]
    unfold powerDefect at hg
    nlinarith
  have hid : v * U - V * u = p ^ 2 * (b * A - B * a) := by
    dsimp [u, U, v, V]
    ring
  have hv : v * U ≤ V * u := by
    have h := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p) (sub_nonpos.mpr hcomp)
    rw [← hid] at h
    omega
  have hout : (c * B) * (u * U) ≤ (C * b) * (u * U) := by
    calc
      _ = (c * u) * (B * U) := by ring
      _ ≤ (b * v) * (B * U) := mul_le_mul_of_nonneg_right hf' (le_of_lt (mul_pos hB hU))
      _ = (b * B) * (v * U) := by ring
      _ ≤ (b * B) * (V * u) := mul_le_mul_of_nonneg_left hv (le_of_lt (mul_pos hb hB))
      _ = (B * V) * (b * u) := by ring
      _ = (C * U) * (b * u) := by rw [hg']
      _ = _ := by ring
  exact le_of_mul_le_mul_right hout (mul_pos hu hU)

/-- Once the input-to-envelope ratio stops increasing, it cannot increase again
on a positive coefficient interval. -/
theorem power_ratio_comparison_propagates (p : ℤ) (f g : ℕ → ℤ) (d start last : ℕ)
    (hp : 1 ≤ p) (hsl : start ≤ last) (hld : last + 1 ≤ d)
    (hfpos : ∀ i ≤ d, 0 < f i) (hgpos : ∀ i ≤ d, 0 < g i)
    (hf : ∀ i, i + 2 ≤ d → PowerConcaveAt p (f i) (f (i + 1)) (f (i + 2)))
    (hg : ∀ i, i + 2 ≤ d → powerDefect p (g i) (g (i + 1)) (g (i + 2)) = 0)
    (hstart : f (start + 1) * g start ≤ g (start + 1) * f start) :
    f (last + 1) * g last ≤ g (last + 1) * f last := by
  have hall : ∀ t, start + t + 1 ≤ d →
      f (start + t + 1) * g (start + t) ≤ g (start + t + 1) * f (start + t) := by
    intro t
    induction t with
    | zero => simpa using fun _ : start + 0 + 1 ≤ d => hstart
    | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hs := power_ratio_comparison_step p (f (start + t)) (f (start + t + 1))
        (f (start + t + 2)) (g (start + t)) (g (start + t + 1)) (g (start + t + 2)) hp
        (hfpos _ (by omega)) (hfpos _ (by omega)) (hgpos _ (by omega)) (hgpos _ (by omega))
        (hf _ (by omega)) (hg _ (by omega)) hprev
      simpa [Nat.add_assoc] using hs
  have he : start + (last - start) = last := by omega
  simpa [he] using hall (last - start) (by omega)

#print axioms power_ratio_comparison_step
#print axioms power_ratio_comparison_propagates
end BinaryResearch
