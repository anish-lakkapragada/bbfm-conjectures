import BBFM.Denominator.FullDyadicKernel
import Mathlib.Data.Nat.Factorization.Basic

/-! A uniformly positive initial Newton-kernel window for the exact BBFM
multiplicity profile. This is not a coefficient log-concavity theorem. -/
noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear
set_option maxHeartbeats 0

lemma source_exponent_loss (n d : ℕ) (hn : 0<n) (hd : 1≤d)
    (hdlog : d ≤ Nat.log 2 n) :
    Nat.log 2 n+1 ≤ (Nat.log 2 (n/d)+1)+d := by
  have hp := Nat.pow_le_of_le_log (Nat.ne_of_gt hn) hdlog
  have he := source_exponent_pow_two n 1 d (by decide) (by simpa using hp)
  have hdp : d ≤ 2^d := Nat.lt_two_pow_self.le
  have hh : Nat.log 2 (n/2^d) ≤ Nat.log 2 (n/d) :=
    Nat.log_mono_right (Nat.div_le_div_left hdp hd)
  simp only [Nat.mul_one, Nat.div_one] at he
  omega

lemma source_dyadic_kernel_summand_ge_one (n s u d : ℕ)
    (hu : Odd u) (hd : d ∈ u.divisors) (hw : 2*(2^s*u) ≤ Nat.log 2 n+1) :
    (1:ℝ) ≤ ((Nat.log 2 (n/d)+1:ℕ):ℝ)+2-(2:ℝ)^(s+1) := by
  have hu0 := hu.pos
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdu := Nat.divisor_le hd
  have hp : 1 ≤ 2^s := Nat.one_le_two_pow
  have hdlog : d ≤ Nat.log 2 n := by nlinarith
  have hn : 0<n := by
    by_contra hn
    have hn0 : n=0 := by omega
    subst n
    norm_num at hw
    nlinarith
  have he := source_exponent_loss n d hn hd0 hdlog
  have hs : 2^(s+1)+1 ≤ Nat.log 2 (n/d)+1+2 := by
    rw [pow_succ]
    nlinarith
  have hsR : ((2^(s+1):ℕ):ℝ)+1 ≤ ((Nat.log 2 (n/d)+1:ℕ):ℝ)+2 := by exact_mod_cast hs
  push_cast at hsR ⊢
  linarith

/-- If the kernel index is at most half the number of weight-one factors,
every dyadic-divisor summand is positive. -/
theorem source_logD_positive_initial (n j : ℕ) (hj : 1≤j)
    (hjn : j≤n) (hw : 2*j ≤ Nat.log 2 n+1) :
    0 < coeff (j-1) (logD (weightedSeries (fun i => Nat.log 2 (n/i)+1) n)) := by
  obtain ⟨s,u,hu,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : j≠0)
  rw [source_logD_dyadic n s u hu hjn]
  apply sum_pos
  · intro d hd
    have hd0 : (0:ℝ)<d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    have hh := source_dyadic_kernel_summand_ge_one n s u d hu hd hw
    exact mul_pos hd0 (by linarith)
  · exact ⟨1, Nat.one_mem_divisors.mpr (by have := hu.pos; omega)⟩

#print axioms source_logD_positive_initial
end BBFMKernel
