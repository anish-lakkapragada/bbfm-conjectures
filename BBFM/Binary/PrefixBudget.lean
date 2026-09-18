import BBFM.Binary.BlockMonotonicity

open Polynomial Finset
namespace BinaryResearch

/-- The actual partial sum of source blocks through `j`. -/
noncomputable def prefixNumerator (m j : ℕ) : ℤ[X] :=
  tailFactor m j * numB (2 * j)

lemma prefixNumerator_eq_blocks (m j : ℕ) (hj : j ≤ m) :
    prefixNumerator m j = ∑ i ∈ range (j + 1), sourceBlock m i :=
  (sourceBlock_prefix m j hj).symm

lemma tailFactor_top_step (m j : ℕ) (hj : j ≤ m) :
    tailFactor (m + 1) j = tailFactor m j * jump m := by
  exact prod_Ico_succ_top hj jump

lemma tailFactor_low_coefficients (m j : ℕ) (hj : j ≤ m) :
    (tailFactor m j).coeff 0 = 1 ∧
    (tailFactor m j).coeff 1 = 0 ∧
    (tailFactor m j).coeff 2 = (m - j : ℕ) := by
  induction m, hj using Nat.le_induction with
  | base => norm_num [tailFactor_self, coeff_one]
  | succ m hj ih =>
    rw [tailFactor_top_step m j hj]
    have hd : m + 1 - j = (m - j) + 1 := by omega
    norm_num [coeff_mul, Nat.antidiagonal_succ, jump_coeff_zero,
      jump_coeff_one, jump_coeff_two, ih.1, ih.2.1, ih.2.2, hd]
    ring

theorem prefixNumerator_low_coefficients (m j : ℕ) (hj : j ≤ m) :
    (prefixNumerator m j).coeff 0 = b (2 * j) ∧
    (prefixNumerator m j).coeff 1 = (numB (2 * j)).coeff 1 ∧
    (prefixNumerator m j).coeff 2 =
      (numB (2 * j)).coeff 2 + (m - j : ℕ) * b (2 * j) := by
  have h := tailFactor_low_coefficients m j hj
  norm_num [prefixNumerator, coeff_mul, Nat.antidiagonal_succ,
    h.1, h.2.1, h.2.2, numB_coeff_zero]

/-- The first Turan determinant pays exactly one squared constant coefficient
for each additional source jump. -/
theorem prefix_first_turan_budget (m j : ℕ) (hj : j ≤ m) :
    (prefixNumerator m j).coeff 1 ^ 2 -
      (prefixNumerator m j).coeff 0 * (prefixNumerator m j).coeff 2 =
    (numB (2 * j)).coeff 1 ^ 2 -
      b (2 * j) * (numB (2 * j)).coeff 2 -
      (m - j : ℕ) * b (2 * j) ^ 2 := by
  obtain ⟨h0, h1, h2⟩ := prefixNumerator_low_coefficients m j hj
  rw [h0, h1, h2]
  ring

theorem prefix_logconcave_budget (m j : ℕ) (hj : j ≤ m)
    (h : CoeffLogConcave (prefixNumerator m j)) :
    (m - j : ℕ) * b (2 * j) ^ 2 ≤
      (numB (2 * j)).coeff 1 ^ 2 - b (2 * j) * (numB (2 * j)).coeff 2 := by
  have he := prefix_first_turan_budget m j hj
  have h1 := h 1 (by omega)
  norm_num at h1
  omega

/-- This strengthening is a conjectural invariant, not a theorem. It includes
the open source log-concavity statement by setting `m = j`. -/
def PrefixFirstEdgePrinciple : Prop :=
  ∀ m j : ℕ, 8 ≤ j → j ≤ m →
    (m - j : ℕ) * b (2 * j) ^ 2 ≤
      (numB (2 * j)).coeff 1 ^ 2 - b (2 * j) * (numB (2 * j)).coeff 2 →
    CoeffLogConcave (prefixNumerator m j)

lemma prefixNumerator_top_step (m j : ℕ) (hj : j ≤ m) :
    prefixNumerator (m + 1) j = jump m * prefixNumerator m j := by
  simp only [prefixNumerator, tailFactor_top_step m j hj]
  ring

lemma jump_eval_one (m : ℕ) : (jump m).eval 1 = jumpLength m := by
  rw [jump_geometric]
  simp [eval_finsetSum]

/-- All prefixes have exactly the same alternating coefficient sum. -/
theorem prefix_eval_neg_one (m j : ℕ) (hj : j ≤ m) :
    (prefixNumerator m j).eval (-1) = amplitude (2 * m) := by
  induction m, hj using Nat.le_induction with
  | base => simp [prefixNumerator, tailFactor_self, amplitude]
  | succ m hj ih =>
    rw [prefixNumerator_top_step m j hj, eval_mul, jump_eval_neg_one, ih]
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, amplitude_even]

/-- Additional dyadic factors preserve the ratio of the total coefficient mass
to the alternating mass. Cross multiplication keeps the statement integral. -/
theorem prefix_total_mass_ratio (m j : ℕ) (hj : j ≤ m) :
    (prefixNumerator m j).eval 1 * amplitude (2 * j) =
      (numB (2 * j)).eval 1 * amplitude (2 * m) := by
  induction m, hj using Nat.le_induction with
  | base => simp [prefixNumerator, tailFactor_self]
  | succ m hj ih =>
    rw [prefixNumerator_top_step m j hj, eval_mul, jump_eval_one,
      show 2 * (m + 1) = 2 * m + 2 by omega, amplitude_even]
    linear_combination (jumpLength m : ℤ) * ih

#print axioms prefixNumerator_low_coefficients
#print axioms prefix_first_turan_budget
#print axioms prefix_logconcave_budget
#print axioms prefix_eval_neg_one
#print axioms prefix_total_mass_ratio
end BinaryResearch
