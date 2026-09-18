import BBFM.Binary.Source

open Polynomial Finset

namespace BinaryResearch

/-- The unbounded powers-of-two predicate; proved equivalent below to the exact public predicate. -/
def IsBinary {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, ∃ j : ℕ, i = 2 ^ j

abbrev Part (n : ℕ) := {p : Nat.Partition n // IsBinary p}
noncomputable instance (n : ℕ) : Fintype (Part n) := by
  classical
  unfold Part
  infer_instance

lemma isBinary_iff_source (n : ℕ) (p : Nat.Partition n) :
    IsBinary p ↔ IsBinaryPartition p := by
  constructor
  · intro hp i hi
    obtain ⟨j, rfl⟩ := hp i hi
    apply Finset.mem_image.mpr
    refine ⟨j, Finset.mem_range.mpr ?_, rfl⟩
    have hle : 2 ^ j ≤ n := p.le_of_mem_parts hi
    exact lt_of_lt_of_le j.lt_two_pow_self hle |>.trans_le (Nat.le_succ n)
  · intro hp i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hp i hi)
    exact ⟨j, rfl⟩

lemma numerator_eq_sum (n : ℕ) : numB n = ∑ p : Part n, hBPartition n p.val := by
  classical
  simp only [numB, binaryPartitions]
  unfold Part
  apply Finset.sum_subtype
  intro p
  simp [isBinary_iff_source]

/-- Append one part of size one. -/
def appendOne {n : ℕ} (p : Part n) : Part (n + 1) :=
  ⟨{ parts := 1 ::ₘ p.val.parts
     parts_pos := by
       intro i hi
       rcases Multiset.mem_cons.mp hi with h | h
       · subst i; omega
       · exact p.val.parts_pos h
     parts_sum := by simp [p.val.parts_sum, Nat.add_comm] }, by
    intro i hi
    rcases Multiset.mem_cons.mp hi with h | h
    · subst i; exact ⟨0, by simp⟩
    · exact p.property i h⟩

lemma appendOne_injective (n : ℕ) : Function.Injective (@appendOne n) := by
  intro p q h
  apply Subtype.ext
  apply Nat.Partition.ext
  have hparts := congrArg (fun r : Part (n + 1) => r.val.parts) h
  simpa [appendOne] using hparts

lemma one_mem_odd (m : ℕ) (p : Part (2 * m + 1)) : 1 ∈ p.val.parts := by
  by_contra hn
  have hdiv : 2 ∣ p.val.parts.sum := by
    apply Multiset.dvd_sum
    intro i hi
    obtain ⟨j, rfl⟩ := p.property i hi
    cases j with
    | zero => simp only [pow_zero] at hi; exact (hn hi).elim
    | succ j => exact dvd_pow_self 2 (by omega)
  rw [p.val.parts_sum] at hdiv
  omega

lemma appendOne_surjective (m : ℕ) : Function.Surjective (@appendOne (2 * m)) := by
  intro p
  have hmem := one_mem_odd m p
  let q : Part (2 * m) :=
    ⟨{ parts := p.val.parts.erase 1
       parts_pos := fun hi => p.val.parts_pos (Multiset.mem_of_mem_erase hi)
       parts_sum := by
         have hs := congrArg Multiset.sum (Multiset.cons_erase hmem)
         simp only [Multiset.sum_cons, p.val.parts_sum] at hs
         omega }, fun i hi => p.property i (Multiset.mem_of_mem_erase hi)⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Nat.Partition.ext
  exact Multiset.cons_erase hmem

noncomputable def oddEquiv (m : ℕ) : Part (2 * m) ≃ Part (2 * m + 1) :=
  Equiv.ofBijective appendOne ⟨appendOne_injective _, appendOne_surjective m⟩

lemma div_odd_two_pow (m j : ℕ) :
    (2 * m + 1) / 2 ^ (j + 1) = (2 * m) / 2 ^ (j + 1) := by
  rw [pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  congr 1
  omega

lemma summand_appendOne (m : ℕ) (p : Part (2 * m)) :
    hBPartition (2 * m + 1) (appendOne p).val = hBPartition (2 * m) p.val := by
  unfold hBPartition
  rw [Finset.prod_range_succ]
  have hlast : (2 * m + 1) / 2 ^ (2 * m + 1) = 0 :=
    Nat.div_eq_of_lt (2 * m + 1).lt_two_pow_self
  simp only [hlast, Nat.zero_sub, pow_zero, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases j with
  | zero => simp [appendOne]
  | succ j =>
    rw [div_odd_two_pow]
    simp [appendOne]

/-- Published odd/even equality, here proved for the exact public `numB` definition. -/
theorem numB_odd (m : ℕ) : numB (2 * m + 1) = numB (2 * m) := by
  rw [numerator_eq_sum, numerator_eq_sum]
  symm
  apply Fintype.sum_equiv (oddEquiv m)
  intro p
  exact (summand_appendOne m p).symm

#print axioms isBinary_iff_source
#print axioms numerator_eq_sum
#print axioms numB_odd

end BinaryResearch
