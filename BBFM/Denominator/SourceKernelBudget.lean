import BBFM.Denominator.SourceKernelWindow
import BBFM.Denominator.LinearProducts

noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear
set_option maxHeartbeats 0

def sourceKernel (n j : ℕ) : ℝ :=
  coeff j (logD (weightedSeries (fun i => Nat.log 2 (n/i)+1) n))

def headMajorant (t : ℕ) : ℝ :=
  if t=0 then 1 else if t=1 then 4 else if t=2 then 1 else
  if t=3 then 6 else if t=4 then 4 else if t=5 then 8 else ((t:ℝ)+2)^2

lemma headMajorant_nonneg (t : ℕ) : 0≤headMajorant t := by
  unfold headMajorant
  split_ifs <;> positivity

lemma source_kernel_oddpart_upper (n s u : ℕ) (hu : Odd u) (hun : 2^s*u≤n) :
    sourceKernel n (2^s*u-1) ≤ ((Nat.log 2 n+1:ℕ):ℝ)*(∑ d ∈ u.divisors, (d:ℝ)) := by
  rw [sourceKernel,source_logD_dyadic n s u hu hun,mul_sum]
  apply sum_le_sum
  intro d hd
  have hm : Nat.log 2 (n/d)+1 ≤ Nat.log 2 n+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n d)) 1
  have hmR : ((Nat.log 2 (n/d)+1:ℕ):ℝ)≤(Nat.log 2 n+1:ℕ) := by exact_mod_cast hm
  have hpN : 2≤2^(s+1) := by
    rw [pow_succ]
    have hh : 1≤2^s := Nat.one_le_two_pow
    omega
  have hp : (2:ℝ)≤2^(s+1) := by exact_mod_cast hpN
  have hh := mul_le_mul_of_nonneg_left (show ((Nat.log 2 (n/d)+1:ℕ):ℝ)+2-2^(s+1)≤(Nat.log 2 n+1:ℕ) by linarith)
    (show (0:ℝ)≤d by positivity)
  simpa only [mul_comm] using hh

lemma source_kernel_head_bound (n t : ℕ) (hn : 8≤n) :
    sourceKernel n (t+1) ≤ ((Nat.log 2 n+1:ℕ):ℝ)*headMajorant t := by
  have hd3 : (3:ℕ).divisors={1,3} := by decide
  have hd5 : (5:ℕ).divisors={1,5} := by decide
  have hd7 : (7:ℕ).divisors={1,7} := by decide
  by_cases ht : t<6
  · interval_cases t
    · have h := source_kernel_oddpart_upper n 1 1 (by decide) (by omega)
      norm_num [headMajorant] at h ⊢
      exact h
    · have h := source_kernel_oddpart_upper n 0 3 (by decide) (by omega)
      norm_num [headMajorant, hd3, hd5, hd7] at h ⊢
      exact h
    · have h := source_kernel_oddpart_upper n 2 1 (by decide) (by omega)
      norm_num [headMajorant] at h ⊢
      exact h
    · have h := source_kernel_oddpart_upper n 0 5 (by decide) (by omega)
      norm_num [headMajorant, hd3, hd5, hd7] at h ⊢
      exact h
    · have h := source_kernel_oddpart_upper n 1 3 (by decide) (by omega)
      norm_num [headMajorant, hd3, hd5, hd7] at h ⊢
      exact h
    · have h := source_kernel_oddpart_upper n 0 7 (by decide) (by omega)
      norm_num [headMajorant, hd3, hd5, hd7] at h ⊢
      exact h
  · have hh := weightedSeries_logD_coeff_bound (fun i => Nat.log 2 (n/i)+1) n (t+1)
      (fun i hi hin => by simpa using Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1)
    have he : headMajorant t=((t:ℝ)+2)^2 := by
      simp [headMajorant,show t≠0 by omega,show t≠1 by omega,show t≠2 by omega,
        show t≠3 by omega,show t≠4 by omega,show t≠5 by omega]
    rw [he]
    apply (le_abs_self _).trans
    simpa [sourceKernel,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num] using hh

lemma cubic_tail_majorant (u : ℕ) :
    ((u:ℝ)+8)^2*((u:ℝ)+7)≤448*2^u := by
  induction u with
  | zero => norm_num
  | succ u ih =>
    rw [pow_succ (2:ℝ)]
    push_cast
    have hu : (0:ℝ)≤u := by positivity
    nlinarith [sq_nonneg (u:ℝ),mul_nonneg hu (sq_nonneg (u:ℝ))]

lemma head_weighted_sum (K : ℕ) :
    (∑ t ∈ range K, headMajorant t*((t:ℝ)+1)*(1/4)^t)≤4 := by
  have hnn (t : ℕ) : 0≤headMajorant t*((t:ℝ)+1)*(1/4)^t :=
    mul_nonneg (mul_nonneg (headMajorant_nonneg t) (by positivity)) (by positivity)
  have hle := sum_le_sum_of_subset_of_nonneg (range_mono (show K≤6+K by omega))
    (fun t ht htn => hnn t)
  have hsplit : (∑ t ∈ range (6+K), headMajorant t*((t:ℝ)+1)*(1/4)^t)=
      59/16 + ∑ u ∈ range K, headMajorant (6+u)*((6+u:ℕ)+1)*(1/4)^(6+u) := by
    rw [sum_range_add]
    norm_num [Finset.sum_range_succ,headMajorant]
  have htail : (∑ u ∈ range K, headMajorant (6+u)*((6+u:ℕ)+1)*(1/4)^(6+u))≤7/32 := by
    calc
      _ ≤ ∑ u ∈ range K, (7/64:ℝ)*(1/2)^u := by
        apply sum_le_sum
        intro u hu
        have he : headMajorant (6+u)=((u:ℝ)+8)^2 := by
          simp [headMajorant,show 6+u≠0 by omega,show 6+u≠1 by omega,
            show 6+u≠2 by omega,show 6+u≠3 by omega,show 6+u≠4 by omega,show 6+u≠5 by omega]
          ring
        rw [he]
        have hh := mul_le_mul_of_nonneg_right (cubic_tail_majorant u)
          (show (0:ℝ)≤(1/4)^(6+u) by positivity)
        convert hh using 1
        · push_cast; ring
        · rw [pow_add]
          norm_num
          have hp : (2:ℝ)^u*(1/4)^u=(1/2)^u := by rw [←mul_pow]; norm_num
          rw [←hp]
          ring
      _ = (7/64:ℝ)*∑ u ∈ range K, (1/2:ℝ)^u := by rw [mul_sum]
      _ ≤ 7/32 := by nlinarith [sum_geometric_two_le K]
  rw [hsplit] at hle
  linarith

/-- The exact first six odd-divisor bounds and a geometric tail yield the
weighted kernel budget needed by the one-sided Newton induction. -/
theorem source_kernel_weighted_budget (n K : ℕ) (hn : 8≤n) :
    (∑ t ∈ range K, sourceKernel n (t+1)*((t:ℝ)+1)*(1/4)^t)≤
      4*((Nat.log 2 n+1:ℕ):ℝ) := by
  have hh := sum_le_sum (s := range K) (fun t ht => mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (source_kernel_head_bound n t hn) (by positivity : 0≤(t:ℝ)+1))
    (by positivity : (0:ℝ)≤(1/4)^t))
  have he : (∑ t ∈ range K, ((Nat.log 2 n+1:ℕ):ℝ)*headMajorant t*((t:ℝ)+1)*(1/4)^t)=
      ((Nat.log 2 n+1:ℕ):ℝ)*(∑ t ∈ range K, headMajorant t*((t:ℝ)+1)*(1/4)^t) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro t ht
    ring
  rw [he] at hh
  have hp := mul_le_mul_of_nonneg_left (head_weighted_sum K)
    (show (0:ℝ)≤(Nat.log 2 n+1:ℕ) by positivity)
  nlinarith

#print axioms source_kernel_weighted_budget
end BBFMKernel
