import BBFM.Denominator.LinearProducts
import BBFM.Denominator.EdgeSupport.ReciprocalLipschitz

noncomputable section
namespace BBFMLinear
open Finset

def qratio (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then 0 else a (j-1)/a j

def normRatio (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ)+1)*a (j+1)/a j

lemma backProduct_qratio (a : ℕ → ℝ) (j t : ℕ) (ht : t ≤ j)
    (ha : ∀ i ≤ j, 0<a i) : backProduct (qratio a) j t=a (j-t)/a j := by
  induction t with
  | zero => simp [backProduct,ne_of_gt (ha j le_rfl)]
  | succ t ih =>
    rw [backProduct,prod_range_succ]
    change backProduct (qratio a) j t*qratio a (j-t)=_
    rw [ih (by omega),qratio,ite_eq_right (by omega)]
    have h1 := ne_of_gt (ha j le_rfl)
    have h2 := ne_of_gt (ha (j-t) (by omega))
    rw [show j-t-1=j-(t+1) by omega]
    field_simp

lemma backProduct_zero (q : ℕ → ℝ) (hzero : q 0=0) (j t : ℕ) (hjt : j<t) :
    backProduct q j t=0 := by
  apply Finset.prod_eq_zero (show j ∈ range t by simpa using hjt)
  simpa using hzero

lemma normRatio_eq_newton (a b : ℕ → ℝ) (K j : ℕ) (hj : j ≤ K)
    (ha : ∀ i ≤ K, 0<a i)
    (hrec : ((j : ℝ)+1)*a (j+1)=∑ t ∈ range (j+1), b t*a (j-t)) :
    normRatio a j=newtonValue b (qratio a) K j := by
  have he : normRatio a j=∑ t ∈ range (j+1), b t*backProduct (qratio a) j t := by
    rw [normRatio,hrec,Finset.sum_div]
    apply sum_congr rfl
    intro t ht
    rw [backProduct_qratio a j t (by simpa using ht) (fun i hi => ha i (by omega))]
    ring
  rw [he,sum_range_succ']
  simp only [backProduct,prod_range_zero,mul_one]
  rw [add_comm]
  change b 0+∑ t ∈ range j, b (t+1)*backProduct (qratio a) j (t+1)=_
  congr 1
  apply sum_subset (range_mono hj)
  intro t ht htj
  have hjt : j<t+1 := by simp only [mem_range] at ht htj; omega
  rw [backProduct_zero _ (by simp [qratio]) _ _ hjt,mul_zero]

lemma qratio_eq_normRatio (a : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (ha : ∀ i ≤ j, 0<a i) : qratio a j=(j : ℝ)/normRatio a (j-1) := by
  rw [qratio,ite_eq_right (by omega),normRatio]
  have he : ((j-1 : ℕ) : ℝ)=(j : ℝ)-1 := by rw [Nat.cast_sub hj]; norm_num
  rw [show j-1+1=j by omega,he]
  have hj0 : (0 : ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have ha1 := ne_of_gt (ha j le_rfl)
  have ha2 := ne_of_gt (ha (j-1) (by omega))
  simp only [sub_add_cancel]
  field_simp

#print axioms normRatio_eq_newton
#print axioms qratio_eq_normRatio

lemma qratio_eq_normRatio_all (a : ℕ → ℝ) (j : ℕ)
    (ha : ∀ i ≤ j, 0<a i) : qratio a j=(j : ℝ)/normRatio a (j-1) := by
  by_cases hj : j=0
  · subst j; simp [qratio]
  · exact qratio_eq_normRatio a j (by omega) ha

theorem normRatio_lipschitz (a b : ℕ → ℝ) (r : ℝ) (K : ℕ)
    (hr : 1000*(K : ℝ) ≤ r) (hr0 : 0<r)
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
      have hh := DenominatorEdgeSupport.reciprocal_ratio_step_of_bound r
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
end BBFMLinear
