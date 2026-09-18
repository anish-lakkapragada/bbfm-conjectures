import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace BinaryRefinementMLR
open Finset

/-- Zero-extended adjacent binomial refinement kernel. -/
def kernel (L k j : ℕ) : ℝ :=
  if 2*j ≤ k then (L.choose (k-2*j) : ℝ) else 0

/-- The symmetrized two-by-two Cauchy-Binet identity, on any finite set. -/
theorem double_sum_identity {ι : Type*} (s : Finset ι) (f g u v : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, (f i*g j-f j*g i)*(u i*v j-u j*v i)) =
      2*((∑ i ∈ s,u i*f i)*(∑ i ∈ s,v i*g i)-
        (∑ i ∈ s,v i*f i)*(∑ i ∈ s,u i*g i)) := by
  have factor (a b : ι → ℝ) :
      (∑ i ∈ s, ∑ j ∈ s, a i*b j)=(∑ i ∈ s,a i)*(∑ j ∈ s,b j) := by
    simp only [Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  calc
    _ = (∑ i ∈ s, ∑ j ∈ s, (u i*f i)*(v j*g j)) -
        (∑ i ∈ s, ∑ j ∈ s, (v i*f i)*(u j*g j)) -
        (∑ i ∈ s, ∑ j ∈ s, (u i*g i)*(v j*f j)) +
        (∑ i ∈ s, ∑ j ∈ s, (v i*g i)*(u j*f j)) := by
      simp only [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [factor,factor,factor,factor]; ring

/-- A two-row TP2 kernel transports all pairwise likelihood-ratio inequalities.
The algebra only needs the cross-product assumptions, including for signed
inputs when those assumptions happen to hold. -/
theorem finite_mlr_transfer {ι : Type*} [LinearOrder ι] (s : Finset ι)
    (f g u v : ι → ℝ)
    (hfg : ∀ i∈s, ∀ j∈s, i≤j → f j*g i ≤ f i*g j)
    (huv : ∀ i∈s, ∀ j∈s, i≤j → u j*v i ≤ u i*v j) :
    (∑ i ∈ s,v i*f i)*(∑ i ∈ s,u i*g i) ≤
      (∑ i ∈ s,u i*f i)*(∑ i ∈ s,v i*g i) := by
  have hsum : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      (f i*g j-f j*g i)*(u i*v j-u j*v i) := by
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    rcases le_total i j with hij | hji
    · exact mul_nonneg (sub_nonneg.mpr (hfg i hi j hj hij))
        (sub_nonneg.mpr (huv i hi j hj hij))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hfg j hj i hi hji))
        (sub_nonpos.mpr (huv j hj i hi hji))
  rw [double_sum_identity] at hsum
  linarith only [hsum]

lemma choose_adjacent_minor (L a b : ℕ) (hab : a ≤ b) :
    (L.choose a : ℝ)*L.choose (b+1) ≤ (L.choose (a+1) : ℝ)*L.choose b := by
  by_cases hb : b ≤ L
  · have ha : a ≤ L := hab.trans hb
    have hra : (L.choose (a+1) : ℝ)*((a:ℝ)+1)=(L.choose a : ℝ)*((L:ℝ)-a) := by
      exact_mod_cast (Nat.choose_succ_right_eq L a)
    have hrb : (L.choose (b+1) : ℝ)*((b:ℝ)+1)=(L.choose b : ℝ)*((L:ℝ)-b) := by
      exact_mod_cast (Nat.choose_succ_right_eq L b)
    have hid : ((a:ℝ)+1)*((b:ℝ)+1)*
        ((L.choose (a+1) : ℝ)*L.choose b-(L.choose a : ℝ)*L.choose (b+1)) =
        ((b:ℝ)-a)*((L:ℝ)+1)*(L.choose a : ℝ)*L.choose b := by
      linear_combination ((b:ℝ)+1)*(L.choose b : ℝ)*hra -
        ((a:ℝ)+1)*(L.choose a : ℝ)*hrb
    have hnn : 0 ≤ ((b:ℝ)-a)*((L:ℝ)+1)*(L.choose a : ℝ)*L.choose b := by
      have habR : (a:ℝ)≤b := by exact_mod_cast hab
      positivity
    have hp : 0 < ((a:ℝ)+1)*((b:ℝ)+1) := by positivity
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right (by rw [hid]; exact hnn) hp)
  · rw [Nat.choose_eq_zero_of_lt (by omega : L < b),
      Nat.choose_eq_zero_of_lt (by omega : L < b+1)]
    simp

def intBinomial (L : ℕ) (z : ℤ) : ℝ :=
  if 0 ≤ z then (L.choose z.toNat : ℝ) else 0

lemma intBinomial_nonneg (L : ℕ) (z : ℤ) : 0 ≤ intBinomial L z := by
  unfold intBinomial
  split <;> positivity

lemma intBinomial_adjacent_minor (L : ℕ) (a b : ℤ) (hab : a ≤ b) :
    intBinomial L a * intBinomial L (b+1) ≤
      intBinomial L (a+1) * intBinomial L b := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have ha' : 0 ≤ a+1 := by omega
    have hb' : 0 ≤ b+1 := by omega
    simp only [intBinomial,if_pos ha,if_pos hb,if_pos ha',if_pos hb']
    rw [show (a+1).toNat=a.toNat+1 by omega,show (b+1).toNat=b.toNat+1 by omega]
    exact choose_adjacent_minor L a.toNat b.toNat (by omega)
  · rw [intBinomial,if_neg ha,zero_mul]
    exact mul_nonneg (intBinomial_nonneg _ _) (intBinomial_nonneg _ _)

lemma kernel_eq_intBinomial (L k j : ℕ) :
    kernel L k j=intBinomial L ((k:ℤ)-2*j) := by
  by_cases h : 2*j ≤ k
  · have hz : 0 ≤ (k:ℤ)-2*j := by omega
    simp only [kernel,if_pos h,intBinomial,if_pos hz]
    congr 2
    omega
  · have hz : ¬ 0 ≤ (k:ℤ)-2*j := by omega
    simp only [kernel,if_neg h,intBinomial,if_neg hz]

lemma kernel_adjacent_minor (L k i j : ℕ) (hij : i ≤ j) :
    kernel L k j * kernel L (k+1) i ≤ kernel L k i * kernel L (k+1) j := by
  simp only [kernel_eq_intBinomial]
  have h := intBinomial_adjacent_minor L ((k:ℤ)-2*j) ((k:ℤ)-2*i) (by omega)
  convert h using 1 <;> push_cast <;> ring_nf

theorem binomial_refinement_mlr (s : Finset ℕ) (L k : ℕ) (f g : ℕ → ℝ)
    (h : ∀ i∈s, ∀ j∈s, i≤j → f j*g i ≤ f i*g j) :
    (∑ i ∈ s,kernel L (k+1) i*f i)*(∑ i ∈ s,kernel L k i*g i) ≤
      (∑ i ∈ s,kernel L k i*f i)*(∑ i ∈ s,kernel L (k+1) i*g i) :=
  finite_mlr_transfer s f g (kernel L k) (kernel L (k+1)) h
    (fun i _ j _ hij => kernel_adjacent_minor L k i j hij)

#print axioms finite_mlr_transfer
#print axioms kernel_adjacent_minor
#print axioms binomial_refinement_mlr
end BinaryRefinementMLR
