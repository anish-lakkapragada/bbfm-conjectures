import BBFM.Binary.Parity

open Polynomial Finset
namespace BinaryResearch

/-- Remove a one when it is present. -/
def eraseOne {n : ℕ} (p : Part (n + 1)) (h : 1 ∈ p.val.parts) : Part n :=
  ⟨{ parts := p.val.parts.erase 1
     parts_pos := fun hi => p.val.parts_pos (Multiset.mem_of_mem_erase hi)
     parts_sum := by
       have hs := congrArg Multiset.sum (Multiset.cons_erase h)
       simp only [Multiset.sum_cons, p.val.parts_sum] at hs
       omega }, fun i hi => p.property i (Multiset.mem_of_mem_erase hi)⟩

@[simp] lemma appendOne_eraseOne {n : ℕ} (p : Part (n + 1)) (h : 1 ∈ p.val.parts) :
    appendOne (eraseOne p h) = p := by
  apply Subtype.ext
  apply Nat.Partition.ext
  exact Multiset.cons_erase h

noncomputable def withOneEquiv (n : ℕ) : Part n ≃ {p : Part (n + 1) // 1 ∈ p.val.parts} where
  toFun p := ⟨appendOne p, by simp [appendOne]⟩
  invFun p := eraseOne p.val p.property
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact Multiset.erase_cons_head 1 p.val.parts
  right_inv p := Subtype.ext (appendOne_eraseOne p.val p.property)

lemma sum_double (s : Multiset ℕ) : (s.map (2 * ·)).sum = 2 * s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; omega

/-- Double all parts, the no-ones branch of the published binary recurrence. -/
def doublePart {m : ℕ} (p : Part m) : Part (2 * m) :=
  ⟨{ parts := p.val.parts.map (2 * ·)
     parts_pos := by
       intro i hi
       obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hi
       exact Nat.mul_pos (by omega) (p.val.parts_pos ha)
     parts_sum := by
       rw [sum_double, p.val.parts_sum] }, by
    intro i hi
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hi
    obtain ⟨j, rfl⟩ := p.property a ha
    exact ⟨j + 1, (pow_succ' 2 j).symm⟩⟩

lemma doublePart_no_one {m : ℕ} (p : Part m) : 1 ∉ (doublePart p).val.parts := by
  intro h
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.mp h
  omega

lemma doublePart_injective (m : ℕ) : Function.Injective (@doublePart m) := by
  intro p q h
  apply Subtype.ext
  apply Nat.Partition.ext
  apply Multiset.map_injective (f := (2 * ·)) (by intro a b h; dsimp at h; omega)
  exact congrArg (fun p : Part (2 * m) => p.val.parts) h

lemma binary_even_of_ne_one {m : ℕ} (p : Part m) (a : ℕ) (ha : a ∈ p.val.parts)
    (h1 : a ≠ 1) : 2 ∣ a := by
  obtain ⟨j, rfl⟩ := p.property a ha
  cases j with
  | zero => exact (h1 rfl).elim
  | succ j => exact dvd_pow_self 2 (by omega)

lemma double_half_parts {m : ℕ} (p : Part (2 * m)) (h1 : 1 ∉ p.val.parts) :
    (p.val.parts.map (· / 2)).map (2 * ·) = p.val.parts := by
  rw [Multiset.map_map]
  trans p.val.parts.map id
  · apply Multiset.map_congr rfl
    intro a ha
    exact Nat.mul_div_cancel' (binary_even_of_ne_one p a ha (by intro h; subst a; exact h1 ha))
  · exact Multiset.map_id _

lemma doublePart_surjective (m : ℕ) (p : Part (2 * m)) (h1 : 1 ∉ p.val.parts) :
    ∃ q : Part m, doublePart q = p := by
  let q : Part m :=
    ⟨{ parts := p.val.parts.map (· / 2)
       parts_pos := by
         intro a ha
         obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
         have hd := binary_even_of_ne_one p b hb (by intro h; subst b; exact h1 hb)
         have hp := p.val.parts_pos hb
         have := Nat.mul_div_cancel' hd
         omega
       parts_sum := by
         have hs := congrArg Multiset.sum (double_half_parts p h1)
         rw [sum_double, p.val.parts_sum] at hs
         omega }, by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.mp ha
      obtain ⟨j, rfl⟩ := p.property b hb
      cases j with
      | zero => exact (h1 hb).elim
      | succ j => refine ⟨j, ?_⟩; simp [pow_succ']⟩
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Nat.Partition.ext
  exact double_half_parts p h1

noncomputable def noOneEquiv (m : ℕ) : Part m ≃ {p : Part (2 * m) // 1 ∉ p.val.parts} :=
  Equiv.ofBijective (fun p => ⟨doublePart p, doublePart_no_one p⟩) ⟨by
    intro p q h
    exact doublePart_injective m (congrArg Subtype.val h), by
    intro p
    obtain ⟨q, hq⟩ := doublePart_surjective m p.val p.property
    exact ⟨q, Subtype.ext hq⟩⟩

/-- General finite sum decomposition via the two actual partition bijections. -/
theorem sum_even_split (m : ℕ) (f : Part (2 * m + 2) → ℤ[X]) :
    ∑ p, f p =
      (∑ p : Part (2 * m), f (appendOne (appendOne p))) +
      ∑ p : Part (m + 1), f (doublePart p) := by
  classical
  let g : Part (2 * m + 1) → ℤ[X] := fun p => f (appendOne p)
  have hone : (∑ p : {p : Part (2 * m + 2) // 1 ∈ p.val.parts}, f p.val) =
      ∑ p : Part (2 * m), f (appendOne (appendOne p)) := by
    symm
    exact Fintype.sum_equiv ((oddEquiv m).trans (withOneEquiv (2 * m + 1))) _ _ (fun _ => rfl)
  have hnone : (∑ p : {p : Part (2 * m + 2) // 1 ∉ p.val.parts}, f p.val) =
      ∑ p : Part (m + 1), f (doublePart p) := by
    symm
    exact Fintype.sum_equiv (noOneEquiv (m + 1)) _ _ (fun _ => rfl)
  rw [← hone, ← hnone]
  exact (Fintype.sum_subtype_add_sum_subtype (fun p : Part (2 * m + 2) => 1 ∈ p.val.parts) f).symm

#print axioms noOneEquiv
#print axioms sum_even_split
end BinaryResearch
