import Mathlib

noncomputable section
namespace DenominatorResearch
open Finset

lemma growing_sums (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (m : ℕ)
    (hg : ∀ j < m, 3 * a j ≤ a (j + 1)) :
    (∑ r ∈ range (m + 1), a r) ≤ 2 * a m ∧
    (∑ r ∈ range (m + 1), ((m : ℝ) + 2 - r) * a r) ≤ 4 * a m := by
  induction m with
  | zero => simp; constructor <;> nlinarith [ha 0]
  | succ m ih =>
    obtain ⟨hS, hW⟩ := ih (fun j hj => hg j (by omega))
    have hG := hg m (by omega)
    have hw : (∑ r ∈ range (m + 1), (((m + 1 : ℕ) : ℝ) + 2 - r) * a r) =
        (∑ r ∈ range (m + 1), ((m : ℝ) + 2 - r) * a r) +
        (∑ r ∈ range (m + 1), a r) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro r _
      push_cast
      ring
    constructor
    · rw [sum_range_succ]
      nlinarith [ha m]
    · rw [sum_range_succ, hw]
      push_cast
      nlinarith

lemma three_term_logconcave (t k A B C : ℝ) (hk : 1 ≤ k) (ht : 6 * k ^ 2 ≤ t)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hL : (t - k + 1) * A ≤ k * B)
    (hU : (k + 1) * C ≤ t * B + 4 * t * A) : A * C ≤ B ^ 2 := by
  have hk0 : 0 ≤ k := by linarith
  have hkk : k ≤ k ^ 2 := by nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk)]
  have ht0 : 0 ≤ t := by nlinarith [sq_nonneg k]
  let u := t - k + 1
  have hu : 0 < u := by dsimp [u]; nlinarith
  have hL' : u * A ≤ k * B := hL
  have hcoef : t * k * u + 4 * t * k ^ 2 ≤ (k + 1) * u ^ 2 := by
    have h1 : 0 ≤ t * (t - 5 * k ^ 2 - k + 2) :=
      mul_nonneg ht0 (by nlinarith)
    have h2 : 0 ≤ (k + 1) * (k - 1) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    dsimp [u]
    nlinarith
  have hsquare : (u * A) ^ 2 ≤ (k * B) ^ 2 :=
    sq_le_sq₀ (mul_nonneg hu.le hA) (mul_nonneg hk0 hB) |>.2 hL'
  have hfirst := mul_le_mul_of_nonneg_left hL' (mul_nonneg (mul_nonneg ht0 hu.le) hB)
  have hsecond := mul_le_mul_of_nonneg_left hsquare (by positivity : 0 ≤ 4 * t)
  have hthird := mul_le_mul_of_nonneg_left hU (mul_nonneg (sq_nonneg u) hA)
  have hscale : (k + 1) * u ^ 2 * (A * C) ≤ (t * k * u + 4 * t * k ^ 2) * B ^ 2 := by
    nlinarith [hfirst, hsecond, hthird]
  have hfinal := hscale.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg B))
  have hpos : 0 < (k + 1) * u ^ 2 := mul_pos (by linarith) (sq_pos_of_pos hu)
  exact (mul_le_mul_iff_right₀ hpos).mp (by nlinarith [hfinal])

/-- Pure coefficient estimate. The later polynomial theorem discharges all inputs. -/
theorem edge_logconcave_of_bounds (a : ℕ → ℝ) (t : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (ht : 6 * (k : ℝ) ^ 2 ≤ t)
    (ha : ∀ j, 0 ≤ a j)
    (hlower : ∀ j, ((t - j) * a j) ≤ ((j : ℝ) + 1) * a (j + 1))
    (hupper : ((k : ℝ) + 1) * a (k + 1) ≤
      t * ∑ r ∈ range (k + 1), ((k : ℝ) + 1 - r) * a r) :
    a (k - 1) * a (k + 1) ≤ a k ^ 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  have hkk : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have ht0 : 0 ≤ t := by nlinarith
  have hg : ∀ j < k - 1, 3 * a j ≤ a (j + 1) := by
    intro j hj
    have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j + 1 ≤ k by omega)
    have hj0 : 0 ≤ (j : ℝ) := by positivity
    have hx := hlower j
    have hcoeff : 3 * ((j : ℝ) + 1) ≤ t - j := by nlinarith
    have hy := mul_le_mul_of_nonneg_right hcoeff (ha j)
    nlinarith
  obtain ⟨_, hW⟩ := growing_sums a ha (k - 1) hg
  have heq : k - 1 + 1 = k := by omega
  have heqR : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]; norm_num
  rw [heq, heqR] at hW
  have hsum : (∑ r ∈ range (k + 1), ((k : ℝ) + 1 - r) * a r) ≤
      a k + 4 * a (k - 1) := by
    rw [sum_range_succ]
    have hw' : (∑ r ∈ range k, ((k : ℝ) + 1 - r) * a r) ≤ 4 * a (k - 1) := by
      convert hW using 1 <;> congr 1 <;> ext r <;> ring
    simp only [add_sub_cancel_left, one_mul]
    linarith
  have hU := hupper.trans (mul_le_mul_of_nonneg_left hsum ht0)
  have hL := hlower (k - 1)
  rw [heq, heqR] at hL
  apply three_term_logconcave t k (a (k - 1)) (a k) (a (k + 1)) hkR ht
    (ha _) (ha _) (ha _)
  · convert hL using 1 <;> ring
  · nlinarith [hU]

end DenominatorResearch
