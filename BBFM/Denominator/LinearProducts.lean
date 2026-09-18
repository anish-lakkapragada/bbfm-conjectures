import BBFM.Denominator.RefinedEdgeSequence
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace BBFMLinear
open Finset

lemma prod_difference_bound (f g : ℕ → ℝ) (c e : ℝ) (n : ℕ)
    (hc : 0 ≤ c) (he : 0 ≤ e)
    (hf : ∀ i<n, |f i| ≤ c) (hg : ∀ i<n, |g i| ≤ c)
    (hd : ∀ i<n, |f i-g i| ≤ e) :
    |(∏ i ∈ range n, f i)-(∏ i ∈ range n, g i)| ≤ (n : ℝ)*e*c^(n-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i hi => hf i (by omega)) (fun i hi => hg i (by omega))
      (fun i hi => hd i (by omega))
    have hp : |∏ i ∈ range n, f i| ≤ c^n := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod (fun i hi => abs_nonneg _) (fun i hi => hf i (by simp only [mem_range] at hi; omega))).trans_eq
        (by simp)
    rw [prod_range_succ,prod_range_succ]
    have hid : (∏ i ∈ range n,f i)*f n-(∏ i ∈ range n,g i)*g n =
      (∏ i ∈ range n,f i)*(f n-g n)+
        ((∏ i ∈ range n,f i)-(∏ i ∈ range n,g i))*g n := by ring
    rw [hid]
    have h1 : |∏ i ∈ range n,f i| * |f n-g n| ≤ c^n*e :=
      mul_le_mul hp (hd n (by omega)) (abs_nonneg _) (pow_nonneg hc _)
    have h2 : |(∏ i ∈ range n,f i)-(∏ i ∈ range n,g i)| * |g n| ≤
        (n : ℝ)*e*c^(n-1)*c :=
      mul_le_mul ih' (hg n (by omega)) (abs_nonneg _) (by positivity)
    calc
      _ ≤ |(∏ i ∈ range n,f i)*(f n-g n)| + 
          |((∏ i ∈ range n,f i)-(∏ i ∈ range n,g i))*g n| := abs_add_le _ _
      _ ≤ c^n*e+(n : ℝ)*e*c^(n-1)*c := by
        simp only [abs_mul]
        exact add_le_add h1 h2
      _ = _ := by
        cases n with
        | zero => simp
        | succ n =>
          simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
          rw [pow_succ c]
          ring

lemma cubic_geometric_majorant (t : ℕ) :
    ((t : ℝ)+2)^2*((t : ℝ)+1) ≤ 4*8^t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [pow_succ (8 : ℝ)]
    push_cast
    have ht : (0 : ℝ) ≤ t := by positivity
    nlinarith [sq_nonneg (t : ℝ),mul_nonneg ht (sq_nonneg (t : ℝ))]

lemma weighted_geometric_sum (n : ℕ) :
    (∑ t ∈ range n, ((t : ℝ)+2)^2*((t : ℝ)+1)*(1/16)^t) ≤ 8 := by
  calc
    _  ≤  ∑ t ∈ range n, 4*(1/2 : ℝ)^t := by
      apply sum_le_sum
      intro t ht
      have hh := mul_le_mul_of_nonneg_right (cubic_geometric_majorant t)
        (show 0 ≤ (1/16 : ℝ)^t by positivity)
      convert hh using 1
      rw [mul_assoc,← mul_pow]
      norm_num
    _ = 4*∑ t ∈ range n, (1/2 : ℝ)^t := by rw [mul_sum]
    _  ≤  8 := by nlinarith [sum_geometric_two_le n]

#print axioms prod_difference_bound
#print axioms weighted_geometric_sum

def backProduct (q : ℕ → ℝ) (j t : ℕ) : ℝ :=
  ∏ u ∈ range t, q (j-u)

def newtonValue (b q : ℕ → ℝ) (K j : ℕ) : ℝ :=
  b 0+∑ t ∈ range K, b (t+1)*backProduct q j (t+1)

theorem newtonValue_step (b q : ℕ → ℝ) (r : ℝ) (K j : ℕ)
    (hr : 0<r) (hj : 1 ≤ j)
    (hb : ∀ t<K, |b (t+1)| ≤ r*((t : ℝ)+2)^2)
    (hq : ∀ t ≤ j, |q t| ≤ 1/16)
    (hd : ∀ t, 1 ≤ t → t ≤ j → |q t-q (t-1)| ≤ 2/r) :
    |newtonValue b q K j-newtonValue b q K (j-1)| ≤ 16 := by
  have hp (t : ℕ) : |backProduct q j (t+1)-backProduct q (j-1) (t+1)| ≤
      ((t : ℝ)+1)*(2/r)*(1/16)^t := by
    have hh := prod_difference_bound (fun u => q (j-u)) (fun u => q (j-1-u))
      (1/16) (2/r) (t+1) (by norm_num) (by positivity)
      (fun u hu => hq _ (by omega)) (fun u hu => hq _ (by omega))
      (fun u hu => ?_)
    · simpa [backProduct] using hh
    · by_cases h : u<j
      · rw [show j-1-u=(j-u)-1 by omega]
        exact hd (j-u) (by omega) (by omega)
      · rw [show j-u=0 by omega,show j-1-u=0 by omega]
        simp
        positivity
  have heq : newtonValue b q K j-newtonValue b q K (j-1) =
      ∑ t ∈ range K, b (t+1)*(backProduct q j (t+1)-backProduct q (j-1) (t+1)) := by
    simp only [newtonValue,add_sub_add_left_eq_sub,← sum_sub_distrib]
    apply sum_congr rfl
    intro t ht
    ring
  rw [heq]
  calc
    _ ≤ ∑ t ∈ range K, |b (t+1)*(backProduct q j (t+1)-backProduct q (j-1) (t+1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ range K, 2*(((t : ℝ)+2)^2*((t : ℝ)+1)*(1/16)^t) := by
      apply sum_le_sum
      intro t ht
      rw [abs_mul]
      have hh := mul_le_mul (hb t (by simpa using ht)) (hp t) (abs_nonneg _) (by positivity)
      apply hh.trans_eq
      field_simp <;> ring
    _ = 2*∑ t ∈ range K, ((t : ℝ)+2)^2*((t : ℝ)+1)*(1/16)^t := by rw [mul_sum]
    _ ≤ 16 := by nlinarith [weighted_geometric_sum K]

#print axioms newtonValue_step
end BBFMLinear
