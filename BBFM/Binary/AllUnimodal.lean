import BBFM.Binary.ShapeAssembly
import BBFM.Binary.Unimodality.FiniteBases

open Polynomial Finset BinaryShape
namespace BinaryResearch

/-- The simultaneous source invariant holds at every even index from 48 on. -/
theorem strong_even (m : ℕ) (hm : 24 ≤ m) : Strong (2 * m) := by
  suffices ∀ m : ℕ, 24 ≤ m → Strong (2 * m) from this m hm
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    by_cases hsmall : m ≤ 48
    · exact ⟨BinaryCertificate.numB_shape_even_le96 m (by omega) hsmall,
        BinaryCertificate.residual_shape_even_le96 m (by omega) hsmall,
        BinaryCertificate.numB_slope_even_le96 m hm hsmall⟩
    · exact strong_step m (by omega)
        (ih (m - 1) (by omega) (by omega)) (ih (m / 2) (by omega) (by omega))

theorem numB_shape_even (m : ℕ) (hm : 1 ≤ m) :
    HasShape (numB (2 * m)) (2 * center (2 * m)) := by
  by_cases hsmall : m ≤ 48
  · exact BinaryCertificate.numB_shape_even_le96 m hm hsmall
  · exact (strong_even m (by omega)).sourceShape

/-- Full all-n symmetric unimodality of the literal public binary numerator. -/
theorem numB_shape (n : ℕ) (hn : 2 ≤ n) : HasShape (numB n) (2 * center n) := by
  rw [numB_even_part n, center_even_part n]
  exact numB_shape_even (n / 2) (by omega)

lemma even_shape_upper_mono (P : ℤ[X]) (c : ℕ) (h : HasShape P (2 * c))
    (k : ℕ) (hk : c ≤ k) : P.coeff (k + 1) ≤ P.coeff k := by
  by_cases hlast : 2 * c ≤ k
  · rw [h.support (k + 1) (by omega)]
    exact h.nonneg k
  · rw [h.symm (k + 1) (by omega), h.symm k (by omega)]
    have hm := h.mono (2 * c - (k + 1)) (by omega)
    simpa only [show 2 * c - (k + 1) + 1 = 2 * c - k by omega] using hm

/-- Ordinary coefficient unimodality: a single peak separates increase and
decrease, including all coefficients after the polynomial's support. -/
def CoeffUnimodal (P : ℤ[X]) : Prop :=
  ∃ p : ℕ, (∀ k, k < p → P.coeff k ≤ P.coeff (k + 1)) ∧
    (∀ k, p ≤ k → P.coeff (k + 1) ≤ P.coeff k)

/-- Revised BBFM Conjecture 6, for every n≥2, with the exact source `numB`.
This is weaker than revised Conjecture 7 (log-concavity), which is not claimed. -/
theorem binary_numerator_unimodal (n : ℕ) (hn : 2 ≤ n) : CoeffUnimodal (numB n) := by
  have h := numB_shape n hn
  exact ⟨center n, (fun k hk => h.mono k (by omega)), even_shape_upper_mono _ _ h⟩

/-- Explicit fully quantified form of the completed all-n endpoint. -/
theorem revised_BBFM_C6 : ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ,
    (∀ k : ℕ, k < p → (numB n).coeff k ≤ (numB n).coeff (k + 1)) ∧
    (∀ k : ℕ, p ≤ k → (numB n).coeff (k + 1) ≤ (numB n).coeff k) :=
  binary_numerator_unimodal

/-- The stronger corrected log-concavity target remains a distinct proposition. -/
def CorrectedBinaryLogConcavity : Prop :=
  ∀ n : ℕ, 6 ≤ n → ∀ k : ℕ, 1 ≤ k →
    (numB n).coeff (k - 1) * (numB n).coeff (k + 1) ≤ ((numB n).coeff k) ^ 2

#print axioms strong_even
#print axioms numB_shape
#print axioms revised_BBFM_C6
#print CorrectedBinaryLogConcavity
end BinaryResearch
