import BBFM.Denominator.Bridge.ReducedRoots
import BBFM.Denominator.Bridge.DyadicCount

open Polynomial Finset
noncomputable section
namespace DenominatorBridge

def productQ (n : ℕ) : ℚ[X] :=
  ∏ i ∈ Icc 1 n, (1 + X ^ i) ^ (Nat.log 2 (n / i) + 1)

lemma one_add_X_pow_monic {R : Type*} [CommRing R] [Nontrivial R]
    (i : ℕ) (hi : 1 ≤ i) : (1 + (X : R[X]) ^ i).Monic := by
  simpa [add_comm] using (Polynomial.monic_X_pow_add_C (R := R) 1 (by omega : i ≠ 0))

lemma productQ_monic (n : ℕ) : (productQ n).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (one_add_X_pow_monic i (mem_Icc.mp hi).1).pow _

lemma productQ_map_ne_zero (n : ℕ) : (productQ n).map (algebraMap ℚ ℂ) ≠ 0 :=
  Polynomial.map_ne_zero (productQ_monic n).ne_zero

lemma badSet_eq_odd_multiple {n s : ℕ} (α : ℂ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    badSet α n = ((Icc 1 (n / s)).filter Odd).image (fun j => s * j) := by
  ext i
  constructor
  · intro hi
    rcases mem_filter.mp hi with ⟨hin, hroot⟩
    have hm := (pow_eq_neg_one_iff_aux hs hord i).mp hroot
    have he : i = s * (2 * (i / (2 * s)) + 1) := by
      have hd := Nat.mod_add_div i (2 * s)
      rw [hm] at hd
      nlinarith
    refine mem_image.mpr ⟨2 * (i / (2 * s)) + 1, ?_, he.symm⟩
    apply mem_filter.mpr
    constructor
    · apply mem_Icc.mpr
      constructor
      · omega
      · apply (Nat.le_div_iff_mul_le hs).mpr
        have := (mem_Icc.mp hin).2
        nlinarith [he]
    · exact ⟨i / (2 * s), rfl⟩
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    rcases mem_filter.mp hj with ⟨hjN, hjodd⟩
    apply mem_filter.mpr
    constructor
    · apply mem_Icc.mpr
      exact ⟨Nat.mul_pos hs (mem_Icc.mp hjN).1,
        by simpa [mul_comm] using (Nat.le_div_iff_mul_le hs).mp (mem_Icc.mp hjN).2⟩
    · obtain ⟨r, rfl⟩ := hjodd
      rw [pow_mul, pow_s_eq_neg_one hs hord.1 hord.2]
      simp [pow_add, pow_mul]

lemma rootMultiplicity_productQ_sum (n : ℕ) (α : ℂ) :
    rootMultiplicity α ((productQ n).map (algebraMap ℚ ℂ)) =
      ∑ i ∈ badSet α n, (Nat.log 2 (n / i) + 1) := by
  unfold productQ
  simp only [Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_add,
    Polynomial.map_one, Polynomial.map_X]
  rw [_root_.rootMultiplicity_prod _ _ α
    (fun i _ => pow_ne_zero _ (one_add_X_pow_ne_zero_complex i))]
  have he : ∀ i ∈ Icc 1 n,
      rootMultiplicity α ((1 + (X : ℂ[X]) ^ i) ^ (Nat.log 2 (n / i) + 1)) =
        if α ^ i = -1 then Nat.log 2 (n / i) + 1 else 0 := by
    intro i hi
    rw [_root_.rootMultiplicity_pow _ _ α (one_add_X_pow_ne_zero_complex i),
      rootMultiplicity_one_add_X_pow_complex α i (mem_Icc.mp hi).1]
    split <;> simp_all
  rw [Finset.sum_congr rfl he]
  simp [badSet, Finset.sum_filter]

/-- The explicit product has exactly the root multiplicities of the source
denominator, for every positive order parameter s (including s>n). -/
theorem rootMultiplicity_productQ (n : ℕ) (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    rootMultiplicity α ((productQ n).map (algebraMap ℚ ℂ)) = n / s := by
  rw [rootMultiplicity_productQ_sum, badSet_eq_odd_multiple α hs hord]
  rw [Finset.sum_image]
  · simp only [← Nat.div_div_eq_div_mul]
    exact sum_odd_log (n / s)
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hs hij

end DenominatorBridge

#print axioms DenominatorBridge.rootMultiplicity_productQ
