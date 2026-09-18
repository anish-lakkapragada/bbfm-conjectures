import BBFM.Denominator.LinearNewton

/-! A one-sided Newton induction. Nonnegative kernel coefficients retain the
sign of every reciprocal-ratio increment, avoiding the factor loss in the
previous absolute-value-only induction. The kernel hypotheses are explicit. -/
noncomputable section
namespace BBFMPositiveNewton
open Finset BBFMLinear
set_option maxHeartbeats 0

lemma reciprocal_step (r u v j : ℝ) (hr : 0<r) (hj : 1≤j)
    (hrj : 4*j≤r) (hu : r≤u) (hv : r≤v) (hd0 : 0≤u-v) (hd4 : u-v≤4) :
    0≤j/u-(j-1)/v ∧ j/u-(j-1)/v≤1/r := by
  have hu0 : 0<u := lt_of_lt_of_le hr hu
  have hv0 : 0<v := lt_of_lt_of_le hr hv
  have hid : j/u-(j-1)/v=(v-(j-1)*(u-v))/(u*v) := by field_simp; ring
  have hd := mul_le_mul_of_nonneg_left hd4 (by linarith : 0≤j-1)
  have hn : 0≤v-(j-1)*(u-v) := by nlinarith
  have hn' : v-(j-1)*(u-v)≤v := by nlinarith [mul_nonneg (by linarith : 0≤j-1) hd0]
  rw [hid]
  constructor
  · exact div_nonneg hn (mul_pos hu0 hv0).le
  · calc
      _ ≤ v/(u*v) := div_le_div_of_nonneg_right hn' (mul_pos hu0 hv0).le
      _ = 1/u := by field_simp
      _ ≤ 1/r := one_div_le_one_div_of_le hr hu

lemma normRatio_lower (a b : ℕ → ℝ) (r : ℝ) (j : ℕ)
    (ha : ∀ i≤j+1, 0<a i) (hb : ∀ t≤j, 0≤b t) (hb0 : b 0=r)
    (hrec : ((j:ℝ)+1)*a (j+1)=∑ t ∈ range (j+1), b t*a (j-t)) :
    r≤normRatio a j := by
  have hs := Finset.single_le_sum
    (fun t ht => mul_nonneg (hb t (by simp only [mem_range] at ht; omega))
      (ha (j-t) (by omega)).le) (show 0 ∈ range (j+1) by simp)
  rw [hb0,Nat.sub_zero,←hrec] at hs
  exact (le_div_iff₀ (ha j (by omega))).mpr hs

lemma newtonValue_step_positive (b q : ℕ → ℝ) (r : ℝ) (K j : ℕ)
    (hr : 0<r) (hj : 1≤j)
    (hb : ∀ t<K, 0≤b (t+1))
    (hsum : (∑ t ∈ range K, b (t+1)*((t:ℝ)+1)*(1/4)^t)≤4*r)
    (hq : ∀ t≤j, 0≤q t ∧ q t≤1/4)
    (hd : ∀ t, 1≤t → t≤j → 0≤q t-q (t-1) ∧ q t-q (t-1)≤1/r) :
    0≤newtonValue b q K j-newtonValue b q K (j-1) ∧
      newtonValue b q K j-newtonValue b q K (j-1)≤4 := by
  have hp (t : ℕ) : 0≤backProduct q j (t+1)-backProduct q (j-1) (t+1) ∧
      backProduct q j (t+1)-backProduct q (j-1) (t+1)≤((t:ℝ)+1)*(1/r)*(1/4)^t := by
    have hmono (u : ℕ) : q (j-1-u)≤q (j-u) := by
      by_cases hu : u<j
      · have hh := (hd (j-u) (by omega) (by omega)).1
        rw [show j-1-u=(j-u)-1 by omega]
        linarith
      · simp only [show j-u=0 by omega,show j-1-u=0 by omega]
        exact le_rfl
    have hnon : 0≤backProduct q j (t+1)-backProduct q (j-1) (t+1) := by
      apply sub_nonneg.mpr
      exact prod_le_prod (fun u hu => (hq _ (by omega)).1) (fun u hu => hmono u)
    have hh := prod_difference_bound (fun u => q (j-u)) (fun u => q (j-1-u))
      (1/4) (1/r) (t+1) (by norm_num) (by positivity)
      (fun u hu => by rw [abs_of_nonneg (hq _ (by omega)).1]; exact (hq _ (by omega)).2)
      (fun u hu => by rw [abs_of_nonneg (hq _ (by omega)).1]; exact (hq _ (by omega)).2)
      (fun u hu => ?_)
    · have hh' : |backProduct q j (t+1)-backProduct q (j-1) (t+1)|≤((t:ℝ)+1)*(1/r)*(1/4)^t := by
        simpa [backProduct] using hh
      rw [abs_of_nonneg hnon] at hh'
      exact ⟨hnon,hh'⟩
    · by_cases huj : u<j
      · rw [show j-1-u=(j-u)-1 by omega, abs_of_nonneg (hd (j-u) (by omega) (by omega)).1]
        exact (hd (j-u) (by omega) (by omega)).2
      · rw [show j-u=0 by omega,show j-1-u=0 by omega]
        simp
        positivity
  have heq : newtonValue b q K j-newtonValue b q K (j-1)=
      ∑ t ∈ range K, b (t+1)*(backProduct q j (t+1)-backProduct q (j-1) (t+1)) := by
    simp only [newtonValue,add_sub_add_left_eq_sub,←sum_sub_distrib]
    apply sum_congr rfl
    intro t ht
    ring
  rw [heq]
  constructor
  · exact sum_nonneg (fun t ht => mul_nonneg (hb t (mem_range.mp ht)) (hp t).1)
  · have hh := sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (hp t).2 (hb t (mem_range.mp ht)))
    have he : (∑ t ∈ range K, b (t+1)*(((t:ℝ)+1)*(1/r)*(1/4)^t))=
        (∑ t ∈ range K, b (t+1)*((t:ℝ)+1)*(1/4)^t)/r := by
      rw [sum_div]
      apply sum_congr rfl
      intro t ht
      ring
    rw [he] at hh
    exact hh.trans ((div_le_iff₀ hr).mpr (by linarith))

/-- Kernel positivity and an explicit geometric first-moment budget give a
uniform LC edge without a finite coefficient scan. -/
theorem logconcave_of_positive_kernel (a b : ℕ → ℝ) (r : ℝ) (K : ℕ)
    (hr : 0<r) (hrK : 4*(K:ℝ)≤r)
    (ha : ∀ i≤K+1, 0<a i) (hb : ∀ t≤K, 0≤b t) (hb0 : b 0=r)
    (hrec : ∀ j≤K, ((j:ℝ)+1)*a (j+1)=∑ t ∈ range (j+1), b t*a (j-t))
    (hsum : (∑ t ∈ range K, b (t+1)*((t:ℝ)+1)*(1/4)^t)≤4*r) :
    ∀ j, 1≤j → j≤K → a (j-1)*a (j+1)≤a j^2 := by
  have hlo (j : ℕ) (hj : j≤K) : r≤normRatio a j :=
    normRatio_lower a b r j (fun i hi => ha i (by omega))
      (fun t ht => hb t (by omega)) hb0 (hrec j hj)
  have hstep : ∀ j≤K, 0≤normRatio a j-normRatio a (j-1) ∧
      normRatio a j-normRatio a (j-1)≤4 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hjK
      by_cases hj0 : j=0
      · subst j; simp
      have hj : 1≤j := by omega
      have hqstep (t : ℕ) (ht : 1≤t) (htj : t≤j) :
          0≤qratio a t-qratio a (t-1) ∧ qratio a t-qratio a (t-1)≤1/r := by
        have hd := ih (t-1) (by omega) (by omega)
        have htK : (t:ℝ)≤K := by exact_mod_cast (show t≤K by omega)
        have hrt : 4*(t:ℝ)≤r := by linarith
        have hh := reciprocal_step r (normRatio a (t-1)) (normRatio a (t-2)) t hr
          (by exact_mod_cast ht) hrt
          (hlo _ (by omega)) (hlo _ (by omega)) (by simpa [Nat.sub_sub] using hd.1)
          (by simpa [Nat.sub_sub] using hd.2)
        rw [qratio_eq_normRatio_all a t (fun i hi => ha i (by omega)),
          qratio_eq_normRatio_all a (t-1) (fun i hi => ha i (by omega)),
          show t-1-1=t-2 by omega, Nat.cast_sub ht] 
        simpa using hh
      have hq (t : ℕ) (ht : t≤j) : 0≤qratio a t ∧ qratio a t≤1/4 := by
        rw [qratio_eq_normRatio_all a t (fun i hi => ha i (by omega))]
        have hu := hlo (t-1) (by omega)
        have hu0 : 0<normRatio a (t-1) := lt_of_lt_of_le hr hu
        constructor
        · positivity
        · apply (div_le_iff₀ hu0).mpr
          have htK : (t:ℝ)≤K := by exact_mod_cast (show t≤K by omega)
          nlinarith
      rw [normRatio_eq_newton a b K j hjK (fun i hi => ha i (by omega)) (hrec j hjK),
        normRatio_eq_newton a b K (j-1) (by omega) (fun i hi => ha i (by omega)) (hrec _ (by omega))]
      exact newtonValue_step_positive b (qratio a) r K j hr hj
        (fun t ht => hb (t+1) (by omega)) hsum hq hqstep
  intro j hj1 hj
  have hd := (hstep j hj).2
  have hl := hlo (j-1) (by omega)
  have hjR : (j:ℝ)≤K := by exact_mod_cast hj
  have hh : (j:ℝ)*normRatio a j≤((j:ℝ)+1)*normRatio a (j-1) := by
    have hp := mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤j by positivity)
    nlinarith
  rw [normRatio,normRatio,show j-1+1=j by omega,Nat.cast_sub hj1] at hh
  norm_num only [Nat.cast_one,sub_add_cancel] at hh
  have ha0 := ha j (by omega)
  have ha1 := ha (j-1) (by omega)
  have hjp : (0:ℝ)<j := by exact_mod_cast hj1
  field_simp at hh
  nlinarith

#print axioms logconcave_of_positive_kernel
end BBFMPositiveNewton
