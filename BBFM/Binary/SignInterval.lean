import BBFM.Binary.RefinementExtremal

open Polynomial
namespace BinaryResearch

/-- A signed sequence has one (possibly empty) interval of strictly positive values. -/
def PositiveInterval (f : ℤ → ℤ) : Prop :=
  ∀ i j k : ℤ, i ≤ j → j ≤ k → 0 < f i → 0 < f k → 0 < f j

def bernoulliSequence (f : ℤ → ℤ) (z : ℤ) : ℤ := f z + f (z - 1)
def duplicateSequence (f : ℤ → ℤ) (z : ℤ) : ℤ := f (z / 2)

theorem positiveInterval_bernoulli (f : ℤ → ℤ) (h : PositiveInterval f) :
    PositiveInterval (bernoulliSequence f) := by
  intro i j k hij hjk hi hk
  by_cases hij' : i = j
  · simpa [hij'] using hi
  by_cases hjk' : j = k
  · simpa [hjk'] using hk
  have hijs : i < j := by omega
  have hjks : j < k := by omega
  have hl : ∃ l, l ≤ i ∧ 0 < f l := by
    unfold bernoulliSequence at hi
    by_cases hfi : 0 < f i
    · exact ⟨i, le_rfl, hfi⟩
    · exact ⟨i - 1, by omega, by omega⟩
  have hr : ∃ r, k - 1 ≤ r ∧ 0 < f r := by
    unfold bernoulliSequence at hk
    by_cases hfk : 0 < f k
    · exact ⟨k, by omega, hfk⟩
    · exact ⟨k - 1, le_rfl, by omega⟩
  obtain ⟨l, hli, hfl⟩ := hl
  obtain ⟨r, hkr, hfr⟩ := hr
  have h1 := h l j r (by omega) (by omega) hfl hfr
  have h2 := h l (j - 1) r (by omega) (by omega) hfl hfr
  unfold bernoulliSequence
  omega

theorem positiveInterval_duplicate (f : ℤ → ℤ) (h : PositiveInterval f) :
    PositiveInterval (duplicateSequence f) := by
  intro i j k hij hjk hi hk
  exact h (i / 2) (j / 2) (k / 2) (by omega) (by omega) hi hk

/-- One duplication followed by `r` adjacent averaging steps. No finite-support,
positivity, or symmetry assumption is needed for this comparison tool. -/
def refinedSequence : ℕ → (ℤ → ℤ) → (ℤ → ℤ)
  | 0, f => duplicateSequence f
  | r + 1, f => bernoulliSequence (refinedSequence r f)

theorem positiveInterval_refinedSequence (r : ℕ) (f : ℤ → ℤ)
    (h : PositiveInterval f) : PositiveInterval (refinedSequence r f) := by
  induction r with
  | zero => exact positiveInterval_duplicate f h
  | succ r ih => exact positiveInterval_bernoulli _ ih

lemma intCoeff_duplicate (P : ℤ[X]) (z : ℤ) :
    BinaryShape.intCoeff ((1 + X) * P.comp (X ^ 2)) z =
      duplicateSequence (BinaryShape.intCoeff P) z := by
  by_cases hz : 0 ≤ z
  · have he : z = (z.toNat : ℤ) := by omega
    rw [he, BinaryShape.intCoeff_nat, BinaryShape.duplicated_coeff]
    unfold duplicateSequence
    rw [show (z.toNat : ℤ) / 2 = ((z.toNat / 2 : ℕ) : ℤ) by omega,
      BinaryShape.intCoeff_nat]
  · have hh : ¬ 0 ≤ z / 2 := by omega
    simp [BinaryShape.intCoeff, duplicateSequence, hz, hh]

lemma intCoeff_refined (r : ℕ) (P : ℤ[X]) (z : ℤ) :
    BinaryShape.intCoeff ((1 + X) ^ (r + 1) * P.comp (X ^ 2)) z =
      refinedSequence r (BinaryShape.intCoeff P) z := by
  induction r generalizing z with
  | zero => simpa [refinedSequence] using intCoeff_duplicate P z
  | succ r ih =>
    have he : (1 + X : ℤ[X]) ^ (r + 1 + 1) * P.comp (X ^ 2) =
        (1 + X) * ((1 + X) ^ (r + 1) * P.comp (X ^ 2)) := by
      rw [pow_succ]
      ring
    rw [he, BinaryShape.intCoeff_one_add_X_mul, ih, ih]
    rfl

/-- Exact polynomial bridge for the signed comparison-sequence theorem. -/
theorem positiveInterval_binomial_refinement (r : ℕ) (P : ℤ[X])
    (h : PositiveInterval (BinaryShape.intCoeff P)) :
    PositiveInterval (BinaryShape.intCoeff ((1 + X) ^ (r + 1) * P.comp (X ^ 2))) := by
  have he : BinaryShape.intCoeff ((1 + X) ^ (r + 1) * P.comp (X ^ 2)) =
      refinedSequence r (BinaryShape.intCoeff P) := funext (intCoeff_refined r P)
  rw [he]
  exact positiveInterval_refinedSequence r _ h

#print axioms positiveInterval_refinedSequence
#print axioms positiveInterval_binomial_refinement
end BinaryResearch
