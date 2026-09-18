import BBFM.Binary.LogConcavity.HistoricalTP2

open Finset
namespace BinaryLC

lemma ratio_adjacent (a : ℕ → ℝ) (d : ℕ)
    (hpos : ∀ k, k ≤ d → 0 < a k)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2)
    (j : ℕ) (hj : j + 2 ≤ d) :
    a (j + 2) / a (j + 1) ≤ a (j + 1) / a j := by
  apply (div_le_div_iff₀ (hpos (j + 1) (by omega)) (hpos j (by omega))).mpr
  have h := hlc (j + 1) (by omega)
  simp only [Nat.add_sub_cancel, show j + 1 + 1 = j + 2 by omega, pow_two] at h
  simpa only [mul_comm] using h

lemma ratio_antitone (a : ℕ → ℝ) (d : ℕ)
    (hpos : ∀ k, k ≤ d → 0 < a k)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2)
    (i j : ℕ) (hij : i ≤ j) (hj : j < d) :
    a (j + 1) / a j ≤ a (i + 1) / a i := by
  induction j generalizing i with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact le_rfl
    · have hstep := ratio_adjacent a d hpos hlc j (by omega)
      exact hstep.trans (ih i (by omega) (by omega))

/-- Every longer Toeplitz minor follows from adjacent log-concavity when the
whole finite support interval is positive. -/
theorem shifted_cross (a : ℕ → ℝ) (d : ℕ)
    (hpos : ∀ k, k ≤ d → 0 < a k)
    (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2)
    (i j s : ℕ) (hij : i ≤ j) (hjs : j + s ≤ d) :
    a i * a (j + s) ≤ a (i + s) * a j := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hp := ih (by omega)
    have hr := ratio_antitone a d hpos hlc (i + s) (j + s) (by omega) (by omega)
    have hcross : a (i + s) * a (j + s + 1) ≤ a (i + s + 1) * a (j + s) := by
      have h := (div_le_div_iff₀ (hpos (j + s) (by omega))
        (hpos (i + s) (by omega))).mp hr
      simpa only [mul_comm] using h
    apply (mul_le_mul_iff_right₀ (hpos (j + s) (by omega))).mp
    calc
      a (j + s) * (a i * a (j + (s + 1))) =
          a (j + s + 1) * (a i * a (j + s)) := by simp only [Nat.add_assoc]; ring
      _ ≤ a (j + s + 1) * (a (i + s) * a j) :=
        mul_le_mul_of_nonneg_left hp (hpos _ (by omega)).le
      _ = a j * (a (i + s) * a (j + s + 1)) := by ring
      _ ≤ a j * (a (i + s + 1) * a (j + s)) :=
        mul_le_mul_of_nonneg_left hcross (hpos j (by omega)).le
      _ = a (j + s) * (a (i + (s + 1)) * a j) := by simp only [Nat.add_assoc]; ring

theorem TP2_of_positive_interval (a : ℤ → ℝ) (d : ℕ)
    (hnonneg : ∀ z, 0 ≤ a z)
    (hzero : ∀ z, z < 0 ∨ (d : ℤ) < z → a z = 0)
    (hpos : ∀ k : ℕ, k ≤ d → 0 < a k)
    (hlc : ∀ k : ℕ, 1 ≤ k →
      a ((k - 1 : ℕ) : ℤ) * a ((k + 1 : ℕ) : ℤ) ≤ a k ^ 2) :
    BBFMCombinatorics.TP2 a := by
  intro r₁ r₂ c₁ c₂ hr hc
  by_cases hlow : a (c₁ - r₂) = 0
  · rw [hlow, mul_zero]
    exact mul_nonneg (hnonneg _) (hnonneg _)
  by_cases hhigh : a (c₂ - r₁) = 0
  · rw [hhigh, zero_mul]
    exact mul_nonneg (hnonneg _) (hnonneg _)
  have hlo : 0 ≤ c₁ - r₂ := by
    by_contra h
    exact hlow (hzero _ (Or.inl (by omega)))
  have hhi : c₂ - r₁ ≤ (d : ℤ) := by
    by_contra h
    exact hhigh (hzero _ (Or.inr (by omega)))
  let i := (c₁ - r₂).toNat
  let j := (c₁ - r₁).toNat
  let s := (c₂ - c₁).toNat
  have hi : (i : ℤ) = c₁ - r₂ := by dsimp [i]; omega
  have hj : (j : ℤ) = c₁ - r₁ := by dsimp [j]; omega
  have hs : (s : ℤ) = c₂ - c₁ := by dsimp [s]; omega
  have h := shifted_cross (fun k : ℕ => a k) d hpos hlc i j s (by omega) (by omega)
  have his : ((i + s : ℕ) : ℤ) = c₂ - r₂ := by omega
  have hjs : ((j + s : ℕ) : ℤ) = c₂ - r₁ := by omega
  rw [hi, hj, his, hjs] at h
  simpa only [mul_comm] using h

end BinaryLC

#print axioms BinaryLC.TP2_of_positive_interval
