import BBFM.Binary.EvenSplit

open Polynomial Finset
namespace BinaryResearch

/-- The extra factors beyond `n+1` all have exponent zero. -/
lemma hBPartition_extend (n L : ℕ) (p : Nat.Partition n) (h : n ≤ L) :
    hBPartition n p =
      ∏ j ∈ range (L + 1), (1 + X ^ (2 ^ j)) ^ (n / 2 ^ j - p.parts.count (2 ^ j)) := by
  apply Finset.prod_subset (Finset.range_mono (by omega))
  intro j hj hjn
  have hnj : n < j := by simp only [Finset.mem_range] at *; omega
  have hz : n / 2 ^ j = 0 := Nat.div_eq_of_lt (lt_trans hnj j.lt_two_pow_self)
  simp [hz]

/-- Reused elementary bound, from the prior private `BinaryMultiplicity` proof. -/
lemma count_weight_le (s : Multiset ℕ) (i : ℕ) : s.count i * i ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    by_cases h : a = i
    · subst a
      simpa [Multiset.count_cons, Nat.add_mul, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_le_add_left ih i
    · simp only [Multiset.count_cons, ite_eq_right (Ne.symm h), Multiset.sum_cons, Nat.add_zero]
      omega

lemma multiplicity_bound (n : ℕ) (p : Nat.Partition n) (j : ℕ) :
    p.parts.count (2 ^ j) ≤ n / 2 ^ j := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 ^ j)).mpr
  simpa [p.parts_sum] using count_weight_le p.parts (2 ^ j)

lemma count_doublePart {m : ℕ} (p : Part m) (j : ℕ) :
    (doublePart p).val.parts.count (2 ^ (j + 1)) = p.val.parts.count (2 ^ j) := by
  rw [pow_succ']
  exact Multiset.count_map_eq_count' (2 * ·) p.val.parts (by intro a b h; dsimp at h; omega) (2 ^ j)

lemma summand_doublePart {m : ℕ} (p : Part m) :
    hBPartition (2 * m) (doublePart p).val =
      (1 + X) ^ (2 * m) * (hBPartition m p.val).comp (X ^ 2) := by
  rw [hBPartition_extend (2 * m) (2 * m + 1) _ (by omega), Finset.prod_range_succ']
  rw [hBPartition_extend m (2 * m) _ (by omega)]
  simp only [Polynomial.prod_comp, Polynomial.pow_comp, Polynomial.add_comp,
    Polynomial.one_comp, Polynomial.X_comp]
  have hone : (doublePart p).val.parts.count 1 = 0 :=
    Multiset.count_eq_zero.mpr (doublePart_no_one p)
  simp only [pow_zero, Nat.div_one, hone, Nat.sub_zero, pow_one]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [count_doublePart]
  have hdiv : (2 * m) / 2 ^ (j + 1) = m / 2 ^ j := by
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    simp
  rw [hdiv, ← pow_mul]
  congr 2
  rw [pow_succ']

/-- Denominator jump after removing two ones; this is the product-form recurrence factor.
The zero-index exponent is zero because those two ones already account for `(1+X)^2`. -/
noncomputable def jump (m : ℕ) : ℤ[X] :=
  ∏ j ∈ range (2 * m + 3), (1 + X ^ (2 ^ j)) ^
    (if j = 0 then 0 else (2 * m + 2) / 2 ^ j - (2 * m) / 2 ^ j)

lemma summand_appendTwo (m : ℕ) (p : Part (2 * m)) :
    hBPartition (2 * m + 2) (appendOne (appendOne p)).val =
      jump m * hBPartition (2 * m) p.val := by
  rw [hBPartition_extend (2 * m) (2 * m + 2) _ (by omega)]
  unfold hBPartition jump
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← pow_add]
  congr 1
  cases j with
  | zero => simp [appendOne]
  | succ j =>
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
    have hbound := multiplicity_bound (2 * m) p.val (j + 1)
    have hmono : (2 * m) / 2 ^ (j + 1) ≤ (2 * m + 2) / 2 ^ (j + 1) :=
      Nat.div_le_div_right (by omega)
    have hne : 2 ^ (j + 1) ≠ 1 := ne_of_gt (Nat.one_lt_pow (by omega) (by omega))
    simp only [appendOne, Multiset.count_cons, hne, ↓reduceIte, Nat.add_zero]
    omega

/-- Exact public numerator recurrence. The finite floor-difference factor `jump` is explicit;
its identification with the shorter valuation-indexed product is recorded separately. -/
theorem numB_even_recurrence (m : ℕ) :
    numB (2 * m + 2) =
      jump m * numB (2 * m) + (1 + X) ^ (2 * m + 2) * (numB (m + 1)).comp (X ^ 2) := by
  rw [numerator_eq_sum, sum_even_split]
  have hd (p : Part (m + 1)) :
      hBPartition (2 * m + 2) (doublePart p).val =
        (1 + X) ^ (2 * m + 2) * (hBPartition (m + 1) p.val).comp (X ^ 2) := by
    convert summand_doublePart p using 1 <;> congr 1 <;> omega
  simp_rw [summand_appendTwo, hd]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Polynomial.sum_comp]
  rw [← numerator_eq_sum, ← numerator_eq_sum]

#print axioms summand_doublePart
#print axioms summand_appendTwo
#print axioms numB_even_recurrence
end BinaryResearch
