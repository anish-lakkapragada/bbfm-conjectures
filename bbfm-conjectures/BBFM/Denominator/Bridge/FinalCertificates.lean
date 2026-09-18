import BBFM.Denominator.Bridge.SmallCertificates


namespace C4Search
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem denominator_coefficient (n k : ℕ) :
    (DenominatorResearch.den n).coeff k = ((coefficients n)[k]?.getD 0 : ℝ) := by
  rw [← poly_coefficients, coeff_poly]

/-- The all-index denominator statement, with coefficient zero extension. -/
def DenLC (n : ℕ) : Prop := ∀ k : ℕ, 1 ≤ k →
  (DenominatorResearch.den n).coeff (k-1) * (DenominatorResearch.den n).coeff (k+1) ≤
    ((DenominatorResearch.den n).coeff k)^2

lemma not_DenLC_of_certificate (n k : ℕ) (hk : 1 ≤ k)
    (h : ((coefficients n)[k]?.getD 0)^2 <
      ((coefficients n)[k-1]?.getD 0) * ((coefficients n)[k+1]?.getD 0)) : ¬ DenLC n := by
  intro hLC
  have hc := hLC k hk
  simp only [denominator_coefficient] at hc
  have hb : (((coefficients n)[k]?.getD 0 : ℝ))^2 <
      ((coefficients n)[k-1]?.getD 0 : ℝ) * ((coefficients n)[k+1]?.getD 0 : ℝ) := by
    exact_mod_cast h
  exact (not_lt_of_ge hc) hb

theorem not_DenLC_three : ¬ DenLC 3 :=
  not_DenLC_of_certificate 3 2 (by decide) (by decide +kernel)

theorem not_DenLC_five : ¬ DenLC 5 :=
  not_DenLC_of_certificate 5 5 (by decide) (by decide +kernel)

theorem not_DenLC_six : ¬ DenLC 6 :=
  not_DenLC_of_certificate 6 2 (by decide) (by decide +kernel)

theorem not_DenLC_seven : ¬ DenLC 7 :=
  not_DenLC_of_certificate 7 2 (by decide) (by decide +kernel)

/-- Complete finite classification; the known exclusions are necessary and sufficient. -/
theorem denominator_classification_through_16 (n : ℕ) (hn : n ≤ 16) :
    DenLC n ↔ n ≠ 3 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro he; subst n; exact not_DenLC_three h
    · intro he; subst n; exact not_DenLC_five h
    · intro he; subst n; exact not_DenLC_six h
    · intro he; subst n; exact not_DenLC_seven h
  · rintro ⟨h3,h5,h6,h7⟩
    exact denominator_through_16 n hn h3 h5 h6 h7

#print axioms not_DenLC_three
#print axioms denominator_classification_through_16
end C4Search


namespace C4Search
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def coreFourCoefficients : List ℕ :=
  repeatFactor (repeatFactor (repeatFactor (repeatFactor [1] 1 4) 2 3) 4 2) 8 1

noncomputable def coreFour : ℝ[X] := poly coreFourCoefficients

theorem coreFour_product : coreFour =
    (1+X)^4 * (1+X^2)^3 * (1+X^4)^2 * (1+X^8) := by
  simp [coreFour, coreFourCoefficients, poly_repeatFactor, poly]

theorem coreFour_logconcave (k : ℕ) (hk : 1 ≤ k) :
    coreFour.coeff (k-1) * coreFour.coeff (k+1) ≤ (coreFour.coeff k)^2 := by
  exact logconcave_of_checks coreFourCoefficients
    (checks_of_fastChecks _ (by decide +kernel)) k hk

theorem early_weight_nine_turan :
    ((coreFour * (1+X^9)).coeff 11)^2 -
      (coreFour * (1+X^9)).coeff 10 * (coreFour * (1+X^9)).coeff 12 = -31 := by
  have h10 : (factor coreFourCoefficients 9)[10]?.getD 0 = 67 := by decide +kernel
  have h11 : (factor coreFourCoefficients 9)[11]?.getD 0 = 73 := by decide +kernel
  have h12 : (factor coreFourCoefficients 9)[12]?.getD 0 = 80 := by decide +kernel
  rw [coreFour, ← poly_factor]
  norm_num [coeff_poly, h10, h11, h12]

#print axioms early_weight_nine_turan
#print axioms coreFour_logconcave
end C4Search
