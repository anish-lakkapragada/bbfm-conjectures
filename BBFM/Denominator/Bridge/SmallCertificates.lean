import BBFM.Denominator.Bridge.ExactCoefficients


namespace C4Search

/-- Linear traversal of consecutive coefficient triples. -/
def fastChecks : List ℕ → Bool
  | a :: b :: c :: p => decide (a*c ≤ b^2) && fastChecks (b :: c :: p)
  | _ => true

lemma fastChecks_tail (a : ℕ) (p : List ℕ) (h : fastChecks (a :: p) = true) :
    fastChecks p = true := by
  cases p with
  | nil => rfl
  | cons b p =>
    cases p with
    | nil => rfl
    | cons c p => exact (Bool.and_eq_true_iff.mp h).2

lemma fastChecks_at (p : List ℕ) (h : fastChecks p = true) (k : ℕ) (hk : 1 ≤ k) :
    (p[k-1]?.getD 0) * (p[k+1]?.getD 0) ≤ (p[k]?.getD 0)^2 := by
  induction p generalizing k with
  | nil => simp
  | cons a p ih =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        cases p with
        | nil => simp
        | cons b p =>
          cases p with
          | nil => simp
          | cons c p =>
            simpa using of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
      | succ k =>
        have ht := ih (fastChecks_tail a p h) (k+1) (by omega)
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel,
          List.getElem?_cons_succ] using ht

lemma checks_of_fastChecks (p : List ℕ) (h : fastChecks p = true) : checks p := by
  intro k _ hk
  exact fastChecks_at p h k hk

 theorem denominator_logconcave_of_fastChecks (n : ℕ)
    (h : fastChecks (coefficients n) = true) (k : ℕ) (hk : 1 ≤ k) :
    (DenominatorResearch.den n).coeff (k-1) * (DenominatorResearch.den n).coeff (k+1) ≤
      ((DenominatorResearch.den n).coeff k)^2 :=
  denominator_logconcave_of_checks n (checks_of_fastChecks _ h) k hk

#print axioms denominator_logconcave_of_fastChecks
end C4Search
namespace C4Search
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem small_certificate_0 : fastChecks (coefficients 0) = true := by decide +kernel
theorem small_certificate_1 : fastChecks (coefficients 1) = true := by decide +kernel
theorem small_certificate_2 : fastChecks (coefficients 2) = true := by decide +kernel
theorem small_certificate_4 : fastChecks (coefficients 4) = true := by decide +kernel
theorem small_certificate_8 : fastChecks (coefficients 8) = true := by decide +kernel
theorem small_certificate_9 : fastChecks (coefficients 9) = true := by decide +kernel
theorem small_certificate_10 : fastChecks (coefficients 10) = true := by decide +kernel
theorem small_certificate_11 : fastChecks (coefficients 11) = true := by decide +kernel
theorem small_certificate_12 : fastChecks (coefficients 12) = true := by decide +kernel
theorem small_certificate_13 : fastChecks (coefficients 13) = true := by decide +kernel
theorem small_certificate_14 : fastChecks (coefficients 14) = true := by decide +kernel
theorem small_certificate_15 : fastChecks (coefficients 15) = true := by decide +kernel
theorem small_certificate_16 : fastChecks (coefficients 16) = true := by decide +kernel
theorem denominator_through_16 (n : ℕ) (hn : n ≤ 16)
    (h3 : n ≠ 3) (h5 : n ≠ 5) (h6 : n ≠ 6) (h7 : n ≠ 7)
    (k : ℕ) (hk : 1 ≤ k) :
    (DenominatorResearch.den n).coeff (k-1) * (DenominatorResearch.den n).coeff (k+1) ≤
      ((DenominatorResearch.den n).coeff k)^2 := by
  apply denominator_logconcave_of_fastChecks n _ k hk
  interval_cases n <;> (first | contradiction | decide +kernel)
#print axioms denominator_through_16
end C4Search


namespace C4Search
open Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def interiorCoefficients : List ℕ :=
  repeatFactor
    (repeatFactor
      (repeatFactor
        (repeatFactor
          (repeatFactor [1] 1 4) 2 3) 4 2) 8 1) 3 2

noncomputable def interiorPoly : ℝ[X] := poly interiorCoefficients

theorem interiorPoly_product : interiorPoly =
    (1+X)^4 * (1+X^2)^3 * (1+X^4)^2 * (1+X^8) * (1+X^3)^2 := by
  simp [interiorPoly, interiorCoefficients, poly_repeatFactor, poly]

theorem interior_coefficient_vector : interiorCoefficients =
    [1,4,9,18,32,50,73,100,128,156,183,206,224,238,247,252,254,
     252,247,238,224,206,183,156,128,100,73,50,32,18,9,4,1] := by
  decide +kernel

theorem interior_logconcave (k : ℕ) (hk : 1 ≤ k) :
    interiorPoly.coeff (k-1) * interiorPoly.coeff (k+1) ≤ (interiorPoly.coeff k)^2 := by
  exact logconcave_of_checks interiorCoefficients
    (checks_of_fastChecks _ (by decide +kernel)) k hk

theorem inserted_logconcave (k : ℕ) (hk : 1 ≤ k) :
    (interiorPoly * (1+X^5)).coeff (k-1) * (interiorPoly * (1+X^5)).coeff (k+1) ≤
      ((interiorPoly * (1+X^5)).coeff k)^2 := by
  rw [interiorPoly, ← poly_factor]
  exact logconcave_of_checks (factor interiorCoefficients 5)
    (checks_of_fastChecks _ (by decide +kernel)) k hk

/-- Every coefficient in the failed synchronization inequality is positive. -/
theorem interior_mixed_term :
    2 * interiorPoly.coeff 7 * interiorPoly.coeff 2 -
      interiorPoly.coeff 6 * interiorPoly.coeff 3 -
      interiorPoly.coeff 8 * interiorPoly.coeff 1 = -26 := by
  norm_num [interiorPoly, coeff_poly, interior_coefficient_vector]

#print axioms interior_mixed_term
#print axioms interior_logconcave
#print axioms inserted_logconcave
end C4Search
