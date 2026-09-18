import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Real-valued sign intervals and binomial smoothing coefficient identities. -/

open Polynomial
namespace BinaryRealSign

/-- Polynomial coefficients extended by zero to all integer indices. -/
def intCoeff (P : ℝ[X]) (z : ℤ) : ℝ := if 0 ≤ z then P.coeff z.toNat else 0

@[simp] lemma intCoeff_nat (P : ℝ[X]) (k : ℕ) : intCoeff P (k:ℤ)=P.coeff k := by
  simp [intCoeff]

lemma intCoeff_one_add_X_mul (P : ℝ[X]) (z : ℤ) :
    intCoeff ((1 + X) * P) z = intCoeff P z + intCoeff P (z - 1) := by
  by_cases hz0 : 0 ≤ z
  · simp only [intCoeff, if_pos hz0, add_mul, one_mul, coeff_add]
    have hx := Polynomial.coeff_X_pow_mul' P 1 z.toNat
    rw [pow_one] at hx
    rw [hx]
    by_cases hz1 : 1 ≤ z
    · have hn : 1 ≤ z.toNat := by omega
      have hm : 0 ≤ z - 1 := by omega
      have he : (z - 1).toNat = z.toNat - 1 := by omega
      simp only [if_pos hn, if_pos hm, he]
    · have hn : ¬ 1 ≤ z.toNat := by omega
      have hm : ¬ 0 ≤ z - 1 := by omega
      simp only [if_neg hn, if_neg hm]
  · have hm : ¬ 0 ≤ z - 1 := by omega
    simp only [intCoeff, if_neg hz0, if_neg hm, add_zero]

lemma duplicated_coeff (P : ℝ[X]) (k : ℕ) :
    ((1 + X) * P.comp (X ^ 2)).coeff k = P.coeff (k / 2) := by
  have hc : ∀ j, (P.comp (X ^ 2)).coeff j = if 2 ∣ j then P.coeff (j / 2) else 0 := by
    intro j
    exact Polynomial.coeff_expand (by decide : 0 < 2) P j
  rw [add_mul, one_mul, coeff_add]
  cases k with
  | zero => simp [hc]
  | succ k =>
    rw [Polynomial.coeff_X_mul, hc, hc]
    by_cases he : 2 ∣ k
    · have ho : ¬ 2 ∣ k + 1 := by omega
      rw [if_pos he, if_neg ho, zero_add]
      congr 1
      omega
    · have ho : 2 ∣ k + 1 := by omega
      rw [if_neg he, if_pos ho, add_zero]


/-- A signed sequence has one (possibly empty) interval of strictly positive values. -/
def PositiveInterval (f : ℤ → ℝ) : Prop :=
  ∀ i j k : ℤ, i ≤ j → j ≤ k → 0 < f i → 0 < f k → 0 < f j

def bernoulliSequence (f : ℤ → ℝ) (z : ℤ) : ℝ := f z + f (z - 1)
def duplicateSequence (f : ℤ → ℝ) (z : ℤ) : ℝ := f (z / 2)

theorem positiveInterval_bernoulli (f : ℤ → ℝ) (h : PositiveInterval f) :
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
    · exact ⟨i - 1, by omega, by linarith⟩
  have hr : ∃ r, k - 1 ≤ r ∧ 0 < f r := by
    unfold bernoulliSequence at hk
    by_cases hfk : 0 < f k
    · exact ⟨k, by omega, hfk⟩
    · exact ⟨k - 1, le_rfl, by linarith⟩
  obtain ⟨l, hli, hfl⟩ := hl
  obtain ⟨r, hkr, hfr⟩ := hr
  have h1 := h l j r (by omega) (by omega) hfl hfr
  have h2 := h l (j - 1) r (by omega) (by omega) hfl hfr
  unfold bernoulliSequence
  linarith only [h1,h2]

theorem positiveInterval_duplicate (f : ℤ → ℝ) (h : PositiveInterval f) :
    PositiveInterval (duplicateSequence f) := by
  intro i j k hij hjk hi hk
  exact h (i / 2) (j / 2) (k / 2) (by omega) (by omega) hi hk

/-- One duplication followed by `r` adjacent averaging steps. No finite-support,
positivity, or symmetry assumption is needed for this comparison tool. -/
def refinedSequence : ℕ → (ℤ → ℝ) → (ℤ → ℝ)
  | 0, f => duplicateSequence f
  | r + 1, f => bernoulliSequence (refinedSequence r f)

theorem positiveInterval_refinedSequence (r : ℕ) (f : ℤ → ℝ)
    (h : PositiveInterval f) : PositiveInterval (refinedSequence r f) := by
  induction r with
  | zero => exact positiveInterval_duplicate f h
  | succ r ih => exact positiveInterval_bernoulli _ ih

lemma intCoeff_duplicate (P : ℝ[X]) (z : ℤ) :
    intCoeff ((1 + X) * P.comp (X ^ 2)) z =
      duplicateSequence (intCoeff P) z := by
  by_cases hz : 0 ≤ z
  · have he : z = (z.toNat : ℤ) := by omega
    rw [he, intCoeff_nat, duplicated_coeff]
    unfold duplicateSequence
    rw [show (z.toNat : ℤ) / 2 = ((z.toNat / 2 : ℕ) : ℤ) by omega,
      intCoeff_nat]
  · have hh : ¬ 0 ≤ z / 2 := by omega
    simp [intCoeff, duplicateSequence, hz, hh]

lemma intCoeff_refined (r : ℕ) (P : ℝ[X]) (z : ℤ) :
    intCoeff ((1 + X) ^ (r + 1) * P.comp (X ^ 2)) z =
      refinedSequence r (intCoeff P) z := by
  induction r generalizing z with
  | zero => simpa [refinedSequence] using intCoeff_duplicate P z
  | succ r ih =>
    have he : (1 + X : ℝ[X]) ^ (r + 1 + 1) * P.comp (X ^ 2) =
        (1 + X) * ((1 + X) ^ (r + 1) * P.comp (X ^ 2)) := by
      rw [pow_succ]
      ring
    rw [he, intCoeff_one_add_X_mul, ih, ih]
    rfl

/-- Exact polynomial bridge for the signed comparison-sequence theorem. -/
theorem positiveInterval_binomial_refinement (r : ℕ) (P : ℝ[X])
    (h : PositiveInterval (intCoeff P)) :
    PositiveInterval (intCoeff ((1 + X) ^ (r + 1) * P.comp (X ^ 2))) := by
  have he : intCoeff ((1 + X) ^ (r + 1) * P.comp (X ^ 2)) =
      refinedSequence r (intCoeff P) := funext (intCoeff_refined r P)
  rw [he]
  exact positiveInterval_refinedSequence r _ h

#print axioms positiveInterval_refinedSequence
#print axioms positiveInterval_binomial_refinement
end BinaryRealSign
