import BBFM.Denominator.SourceKernelSigns
import Mathlib.Data.Finset.NatDivisors

/-! The full dyadic valuation identity for the source Newton kernel. -/
noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear
set_option maxHeartbeats 0

lemma sum_divisors_coprime {a b : ℕ} (h : a.Coprime b) (f : ℕ → ℝ) :
    (∑ d ∈ (a*b).divisors, f d) =
      ∑ i ∈ a.divisors, ∑ j ∈ b.divisors, f (i*j) := by
  rw [h.divisors_mul]
  simp only [sum_map]
  change (∑ x ∈ (a.divisors ×ˢ b.divisors).attach, f (x.val.1*x.val.2)) = _
  rw [Finset.sum_attach (a.divisors ×ˢ b.divisors) (fun p : ℕ × ℕ => f (p.1*p.2)), sum_product]

lemma source_exponent_pow_two (n d s : ℕ) (hd : 0<d) (h : 2^s*d ≤ n) :
    Nat.log 2 (n/(2^s*d))+1+s = Nat.log 2 (n/d)+1 := by
  induction s with
  | zero => simp
  | succ s ih =>
    have hprev : 2^s*d ≤ n := by
      have hp : 0 < 2^s := by positivity
      rw [pow_succ] at h
      nlinarith
    have he := source_exponent_twice n (2^s*d) (by positivity)
      (by simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h)
    have hi := ih hprev
    rw [show 2^(s+1)*d=2*(2^s*d) by ring]
    omega

lemma dyadic_weighted_sum (a : ℝ) (s : ℕ) :
    (∑ t ∈ range s, (2:ℝ)^t*(a-t)) =
      (2:ℝ)^s*(a-s+2)-a-2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma quotient_dyadic (s t u d : ℕ) (ht : t ≤ s) (hd : d ∣ u) :
    (2^s*u)/(2^t*d)=2^(s-t)*(u/d) := by
  have he : 2^s*u=2^t*(2^(s-t)*u) := by
    rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le ht]
  rw [he, Nat.mul_div_mul_left _ _ (by positivity : 0<2^t)]
  exact Nat.mul_div_assoc _ hd

lemma dyadic_sign (s t u d : ℕ) (ht : t ≤ s) (hu : Odd u) (hd : d ∈ u.divisors) :
    (-1:ℝ)^((2^s*u)/(2^t*d)-1) = if t=s then 1 else -1 := by
  rw [quotient_dyadic s t u d ht (Nat.mem_divisors.mp hd).1]
  have ho : Odd (u/d) := hu.of_dvd_nat (Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
  by_cases hts : t=s
  · subst t
    simp only [Nat.sub_self, pow_zero, one_mul, if_pos rfl]
    obtain ⟨a,ha⟩ := ho
    have hh : Even (u/d-1) := ⟨a,by omega⟩
    exact hh.neg_one_pow
  · rw [if_neg hts]
    have hst : 1 ≤ s-t := by omega
    have he : Even (2^(s-t)*(u/d)) := by
      refine ⟨2^(s-t-1)*(u/d),?_⟩
      have hepow : 2^(s-t)=2^(s-t-1)*2 := by
        conv_lhs => rw [show s-t=(s-t-1)+1 by omega]
        rw [pow_succ]
      rw [hepow]
      ring
    have hp : 0<2^(s-t)*(u/d) := mul_pos (by positivity) ho.pos
    have hh : Odd (2^(s-t)*(u/d)-1) := by
      obtain ⟨a,ha⟩ := he
      refine ⟨a-1,?_⟩
      omega
    exact hh.neg_one_pow

/-- Complete valuation formula, for an arbitrary odd part and every dyadic
exponent whose index lies within the literal source product. -/
theorem source_logD_dyadic (n s u : ℕ) (hu : Odd u) (h : 2^s*u ≤ n) :
    coeff (2^s*u-1) (logD (weightedSeries (fun i => Nat.log 2 (n/i)+1) n)) =
      ∑ d ∈ u.divisors, (d:ℝ)*((Nat.log 2 (n/d)+1:ℕ)+2-(2:ℝ)^(s+1)) := by
  have hcop : (2^s).Coprime u := (Nat.coprime_two_left.mpr hu).pow_left s
  rw [weighted_logD_divisors _ _ _ (by have hp : 0<2^s*u := mul_pos (by positivity) hu.pos; omega) h,
    sum_divisors_coprime hcop, Nat.sum_divisors_prime_pow Nat.prime_two, sum_comm]
  apply sum_congr rfl
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdu := Nat.divisor_le hd
  have hm (t : ℕ) (ht : t ≤ s) :
      ((Nat.log 2 (n/(2^t*d))+1:ℕ):ℝ) = (Nat.log 2 (n/d)+1:ℕ)-t := by
    have hp : 2^t*d ≤ n :=
      (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 1≤2) ht) hdu).trans h
    have hh := source_exponent_pow_two n d t hd0 hp
    have hhR : ((Nat.log 2 (n/(2^t*d))+1:ℕ):ℝ)+t = (Nat.log 2 (n/d)+1:ℕ) := by exact_mod_cast hh
    linarith
  have he : (∑ t ∈ range (s+1),
      ((Nat.log 2 (n/(2^t*d))+1:ℕ):ℝ)*(2^t*d)*(-1:ℝ)^((2^s*u)/(2^t*d)-1)) =
      (d:ℝ)*((2:ℝ)^s*((Nat.log 2 (n/d)+1:ℕ)-s) -
        ∑ t ∈ range s, (2:ℝ)^t*((Nat.log 2 (n/d)+1:ℕ)-t)) := by
    rw [sum_range_succ]
    have hlast := hm s le_rfl
    rw [dyadic_sign s s u d le_rfl hu hd, if_pos rfl, hlast]
    have hi : (∑ t ∈ range s,
      ((Nat.log 2 (n/(2^t*d))+1:ℕ):ℝ)*(2^t*d)*(-1:ℝ)^((2^s*u)/(2^t*d)-1)) =
      -(d:ℝ)*(∑ t ∈ range s, (2:ℝ)^t*((Nat.log 2 (n/d)+1:ℕ)-t)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro t ht
      have hts : t<s := mem_range.mp ht
      rw [dyadic_sign s t u d hts.le hu hd, if_neg (by omega), hm t hts.le]
      push_cast
      ring
    rw [hi]
    push_cast
    ring
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [he, dyadic_weighted_sum, pow_succ]
  ring

#print axioms source_logD_dyadic
end BBFMKernel
