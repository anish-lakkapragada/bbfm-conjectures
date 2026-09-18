import BBFM.Binary.ShiftedProfilePC
import BBFM.Binary.RealSeriesRefinement

open BinaryPowerConcavity BinaryRealSign PowerSeries
namespace BinaryResearch
noncomputable section

/-- Real version of the previously checked integral ratio comparison. -/
theorem real_power_ratio_comparison_step (p a b c A B C : ℝ)
    (hp : 1 ≤ p) (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (hf : PC p a b c)
    (hg : (p + 1) * B ^ 2 - B * (A + C) - (p - 1) * A * C = 0)
    (hcomp : b * A ≤ B * a) : c * B ≤ C * b := by
  let u := b + (p - 1) * a
  let U := B + (p - 1) * A
  let v := (p + 1) * b - a
  let V := (p + 1) * B - A
  have hu : 0 < u := by dsimp [u]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hf' : c * u ≤ b * v := by
    dsimp [u, v]
    unfold PC at hf
    nlinarith
  have hg' : C * U = B * V := by dsimp [U, V]; nlinarith
  have hid : v * U - V * u = p ^ 2 * (b * A - B * a) := by
    dsimp [u, U, v, V]
    ring
  have hv : v * U ≤ V * u := by
    have hn := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg p) (sub_nonpos.mpr hcomp)
    rw [← hid] at hn
    linarith
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

lemma ratio_descent_propagates (r : ℕ → ℝ)
    (hr : ∀ k, r (k + 1) ≤ r k → r (k + 2) ≤ r (k + 1))
    (start last : ℕ) (hsl : start ≤ last) (hs : r (start + 1) ≤ r start) :
    r (last + 1) ≤ r last := by
  have hall : ∀ t, r (start + t + 1) ≤ r (start + t) := by
    intro t
    induction t with
    | zero => simpa using hs
    | succ t ih => simpa [Nat.add_assoc] using hr (start + t) ih
  have he : start + (last - start) = last := by omega
  simpa [he] using hall (last - start)

lemma exists_ratio_descent (r : ℕ → ℝ) (i j : ℕ) (hij : i < j) (h : r j < r i) :
    ∃ t, i ≤ t ∧ t < j ∧ r (t + 1) ≤ r t := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
    by_cases hi : i = j
    · subst i; exact ⟨j, le_rfl, by omega, h.le⟩
    by_cases hl : r (j + 1) ≤ r j
    · exact ⟨j, by omega, by omega, hl⟩
    · obtain ⟨t, hit, htj, ht⟩ := ih i (by omega) (lt_trans (lt_of_not_ge hl) h)
      exact ⟨t, hit, by omega, ht⟩

lemma ratio_descent_tail (r : ℕ → ℝ)
    (hr : ∀ k, r (k + 1) ≤ r k → r (k + 2) ≤ r (k + 1))
    (start j k : ℕ) (hsj : start ≤ j) (hjk : j ≤ k)
    (hs : r (start + 1) ≤ r start) : r k ≤ r j := by
  have hall : ∀ t, r (j + t) ≤ r j := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hn := ratio_descent_propagates r hr start (j + t) (by omega) hs
      have hh := le_trans hn ih
      simpa [Nat.add_assoc] using hh
  have he : j + (k - j) = k := by omega
  simpa [he] using hall (k - j)

/-- A local irreversible decrease gives a global interval of values above any level. -/
theorem ratio_level_interval (r : ℕ → ℝ)
    (hr : ∀ k, r (k + 1) ≤ r k → r (k + 2) ≤ r (k + 1))
    (α : ℝ) (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k)
    (hi : α < r i) (hk : α < r k) : α < r j := by
  by_contra hj
  have hji : r j < r i := lt_of_le_of_lt (le_of_not_gt hj) hi
  have hij' : i < j := by
    by_contra hn
    have he : i = j := by omega
    simpa [he] using hji
  obtain ⟨t, hit, htj, ht⟩ := exists_ratio_descent r i j hij' hji
  have hh := ratio_descent_tail r hr t j k (by omega) hjk ht
  linarith

lemma pc_ratio_local_descent (p : ℝ) (f g : ℕ → ℝ) (d : ℕ)
    (hp : 1 ≤ p) (hfpos : ∀ i ≤ d, 0 < f i) (hfsup : ∀ i, d < i → f i = 0)
    (hgpos : ∀ i, 0 < g i)
    (hf : ∀ i, i + 2 ≤ d → PC p (f i) (f (i + 1)) (f (i + 2)))
    (hg : ∀ i, (p + 1) * (g (i + 1)) ^ 2 - g (i + 1) * (g i + g (i + 2)) -
      (p - 1) * g i * g (i + 2) = 0) (k : ℕ)
    (hc : f (k + 1) / g (k + 1) ≤ f k / g k) :
    f (k + 2) / g (k + 2) ≤ f (k + 1) / g (k + 1) := by
  by_cases hk : k + 2 ≤ d
  · have hcross : f (k + 1) * g k ≤ g (k + 1) * f k := by
      have he := (div_le_div_iff₀ (hgpos (k + 1)) (hgpos k)).mp hc
      nlinarith
    have hn := real_power_ratio_comparison_step p (f k) (f (k + 1)) (f (k + 2))
      (g k) (g (k + 1)) (g (k + 2)) hp (hfpos k (by omega))
      (hfpos (k + 1) (by omega)) (hgpos k) (hgpos (k + 1)) (hf k hk) (hg k) hcross
    apply (div_le_div_iff₀ (hgpos (k + 2)) (hgpos (k + 1))).mpr
    nlinarith
  · rw [hfsup (k + 2) (by omega), zero_div]
    apply div_nonneg _ (hgpos _).le
    by_cases he : k + 1 ≤ d
    · exact (hfpos _ he).le
    · rw [hfsup _ (by omega)]

lemma shiftedProfile_equality (p k : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    (p + 1 : ℝ) * (shiftedProfile p h (k + 1)) ^ 2 -
      shiftedProfile p h (k + 1) * (shiftedProfile p h k + shiftedProfile p h (k + 2)) -
      (p - 1 : ℝ) * shiftedProfile p h k * shiftedProfile p h (k + 2) = 0 := by
  apply shifted_profile_homogeneous p (h + k + 1)
    (shiftedProfile p h k) (shiftedProfile p h (k + 1)) (shiftedProfile p h (k + 2))
    (by positivity)
  · convert shiftedProfile_recurrence p h k using 1 <;> ring
  · convert shiftedProfile_recurrence p h (k + 1) using 1 <;> push_cast <;> ring

/-- Every finite positive PC input has one interval above every scaled shifted
profile. This is the input needed by variation diminishing. -/
theorem pc_shiftedProfile_positiveInterval (p d : ℕ) (hp : 1 ≤ p) (f : ℕ → ℝ)
    (hfpos : ∀ i ≤ d, 0 < f i) (hfsup : ∀ i, d < i → f i = 0)
    (hf : ∀ i, i + 2 ≤ d → PC p (f i) (f (i + 1)) (f (i + 2)))
    (h : ℝ) (hh : 0 ≤ h) (α : ℝ) :
    BinaryRealSign.PositiveInterval (fun z : ℤ => if 0 ≤ z then f z.toNat - α * shiftedProfile p h z.toNat else 0) := by
  intro i j k hij hjk hi hk
  have hi0 : 0 ≤ i := by by_contra hn; simp [hn] at hi
  have hj0 : 0 ≤ j := by omega
  have hk0 : 0 ≤ k := by omega
  simp only [if_pos hi0] at hi
  simp only [if_pos hk0] at hk
  simp only [if_pos hj0]
  have hgp := shiftedProfile_positive p h hh
  have hir : α < f i.toNat / shiftedProfile p h i.toNat :=
    (lt_div_iff₀ (hgp _)).mpr (by linarith)
  have hkr : α < f k.toNat / shiftedProfile p h k.toNat :=
    (lt_div_iff₀ (hgp _)).mpr (by linarith)
  have hr := pc_ratio_local_descent p f (shiftedProfile p h) d (by exact_mod_cast hp)
    hfpos hfsup hgp hf (fun i => shiftedProfile_equality p i h hh)
  have hmid := ratio_level_interval (fun i => f i / shiftedProfile p h i) hr α
    i.toNat j.toNat k.toNat (by omega) (by omega) hir hkr
  have hm := (lt_div_iff₀ (hgp _)).mp hmid
  linarith

#print axioms real_power_ratio_comparison_step
#print axioms pc_shiftedProfile_positiveInterval
end
end BinaryResearch
