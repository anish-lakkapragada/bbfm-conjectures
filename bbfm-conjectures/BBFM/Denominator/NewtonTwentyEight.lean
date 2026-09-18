import BBFM.Denominator.LinearNewton
import BBFM.Denominator.ReciprocalTwentyEight

/-! Coefficient-ratio induction with the constant required by the reciprocal bound. -/
noncomputable section
namespace BBFM28
open Finset BBFMLinear

theorem normRatio_lipschitz (a b : ℕ → ℝ) (r : ℝ) (K : ℕ)
    (hr : 28*(K : ℝ) ≤ r) (hr0 : 0<r)
    (ha : ∀ i ≤ K+1, 0<a i)
    (hrec : ∀ j ≤ K, ((j : ℝ)+1)*a (j+1)=∑ t ∈ range (j+1), b t*a (j-t))
    (hb : ∀ t<K, |b (t+1)| ≤ r*((t : ℝ)+2)^2)
    (hrough : ∀ j ≤ K, r-j ≤ normRatio a j ∧ normRatio a j ≤ r+8*j) :
    ∀ j ≤ K, |normRatio a j-normRatio a (j-1)| ≤ 16 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hjK
    by_cases hj0 : j=0
    · subst j; simp
    have hj : 1 ≤ j := by omega
    have hstep (t : ℕ) (ht : 1 ≤ t) (htj : t ≤ j) :
        |qratio a t-qratio a (t-1)| ≤ 2/r ∧ |qratio a t| ≤ 1/16 := by
      have hu := hrough (t-1) (by omega)
      have hv := hrough (t-2) (by omega)
      have htm1 : ((t-1 : ℕ) : ℝ) ≤ t := by exact_mod_cast Nat.sub_le t 1
      have htm2 : ((t-2 : ℕ) : ℝ) ≤ t := by exact_mod_cast Nat.sub_le t 2
      have hd : |normRatio a (t-1)-normRatio a (t-2)| ≤ 16 := by
        have hh := ih (t-1) (by omega) (by omega)
        simpa [show t-1-1=t-2 by omega] using hh
      have hh := BBFM28Support.reciprocal_ratio_step_of_bound r
        (normRatio a (t-1)) (normRatio a (t-2)) t K ht (by omega) hr
        (by linarith [hu.1]) (by linarith [hv.1]) (by linarith [hv.2]) hd
      rw [qratio_eq_normRatio_all a t (fun i hi => ha i (by omega)),
        qratio_eq_normRatio_all a (t-1) (fun i hi => ha i (by omega))]
      rw [show t-1-1=t-2 by omega, Nat.cast_sub ht]
      norm_num only [Nat.cast_one]
      exact ⟨hh.1,by rw [abs_of_nonneg hh.2.1]; exact hh.2.2⟩
    have hq : ∀ t ≤ j, |qratio a t| ≤ 1/16 := by
      intro t htj
      by_cases ht0 : t=0
      · subst t; simp [qratio]
      · exact (hstep t (by omega) htj).2
    rw [normRatio_eq_newton a b K j hjK (fun i hi => ha i (by omega)) (hrec j hjK),
      normRatio_eq_newton a b K (j-1) (by omega) (fun i hi => ha i (by omega)) (hrec _ (by omega))]
    exact newtonValue_step b (qratio a) r K j hr0 hj hb hq
      (fun t ht htj => (hstep t ht htj).1)

#print axioms normRatio_lipschitz
end BBFM28
