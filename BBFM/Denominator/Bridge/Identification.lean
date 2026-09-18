import BBFM.Denominator.Bridge.ProductRoots

open Polynomial Finset
noncomputable section
namespace DenominatorBridge

lemma denStar_monic (n : ℕ) : (denStar n).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (one_add_X_pow_monic i (mem_Icc.mp hi).1).pow _

lemma gCommon_monic (n : ℕ) (hn : 1 ≤ n) : (gCommon n).Monic := by
  have h := Polynomial.monic_normalize (gCommon_ne_zero n hn)
  simpa [gCommon, Finset.normalize_gcd] using h

lemma denReduced_monic (n : ℕ) (hn : 1 ≤ n) : (denReduced n).Monic := by
  apply (gCommon_monic n hn).of_mul_monic_right
  rw [← denStar_eq_denReduced_mul_gCommon n hn]
  exact denStar_monic n

lemma all_rootMultiplicities_equal (n : ℕ) (hn : 1 ≤ n) (α : ℂ) :
    rootMultiplicity α ((denReduced n).map (algebraMap ℚ ℂ)) =
      rootMultiplicity α ((productQ n).map (algebraMap ℚ ℂ)) := by
  by_cases hex : ∃ i ∈ Icc 1 n, α ^ i = -1
  · obtain ⟨i, hi, hα⟩ := hex
    obtain ⟨s, hs, hp, hmin⟩ :=
      exists_even_order_of_pow_eq_neg_one α i (mem_Icc.mp hi).1 hα
    have hsi := s_le_of_pow_eq_neg_one hs ⟨hp, hmin⟩ (mem_Icc.mp hi).1 hα
    rw [rootMultiplicity_denReduced α s hs ⟨hp, hmin⟩ (hsi.trans (mem_Icc.mp hi).2),
      rootMultiplicity_productQ n α s hs ⟨hp, hmin⟩]
  · have hstar : ¬ IsRoot ((denStar n).map (algebraMap ℚ ℂ)) α := by
      exact fun he => hex (exists_pow_eq_neg_one_of_denStar_eval α he)
    have hdvd : (denReduced n).map (algebraMap ℚ ℂ) ∣
        (denStar n).map (algebraMap ℚ ℂ) := by
      apply Polynomial.map_dvd
      exact ⟨gCommon n, denStar_eq_denReduced_mul_gCommon n hn⟩
    have hz : rootMultiplicity α ((denReduced n).map (algebraMap ℚ ℂ)) = 0 := by
      apply Nat.eq_zero_of_le_zero
      have hle := Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd
        (Polynomial.map_ne_zero (denStar_ne_zero n) :
          (denStar n).map (algebraMap ℚ ℂ) ≠ 0) hdvd α
      simpa [Polynomial.rootMultiplicity_eq_zero hstar] using hle
    have hb : badSet α n = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hex ⟨i, (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩
    rw [hz, rootMultiplicity_productQ_sum, hb]
    simp

/-- BBFM's product formula for the exact monic gcd-normalized denominator
defined in Axiom's formal C2 artifact. The equality is formal, with no
coefficient or partition-identification hypothesis. -/
theorem denReduced_eq_productQ (n : ℕ) (hn : 1 ≤ n) : denReduced n = productQ n := by
  apply Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective
  have hroots : ((denReduced n).map (algebraMap ℚ ℂ)).roots =
      ((productQ n).map (algebraMap ℚ ℂ)).roots := by
    apply Multiset.ext.mpr
    intro α
    simpa [Polynomial.count_roots] using all_rootMultiplicities_equal n hn α
  rw [(IsAlgClosed.splits ((denReduced n).map (algebraMap ℚ ℂ))).eq_prod_roots_of_monic
      ((denReduced_monic n hn).map _),
    (IsAlgClosed.splits ((productQ n).map (algebraMap ℚ ℂ))).eq_prod_roots_of_monic
      ((productQ_monic n).map _), hroots]

end DenominatorBridge

#print axioms DenominatorBridge.denReduced_eq_productQ
