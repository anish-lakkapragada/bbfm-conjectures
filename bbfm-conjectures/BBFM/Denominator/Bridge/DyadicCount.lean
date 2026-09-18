import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity

open Finset
namespace DenominatorBridge

lemma odd_power_two_injective {j k r t : ℕ} (hj : Odd j) (hk : Odd k)
    (he : j * 2 ^ r = k * 2 ^ t) : j = k ∧ r = t := by
  have hjnd : ¬ 2 ∣ j := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hj
  have hknd : ¬ 2 ∣ k := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hk
  have hc := congrArg (fun n : ℕ => n / 2 ^ n.factorization 2) he
  rw [mul_comm j, mul_comm k,
    Nat.ordCompl_pow_mul_of_not_dvd r Nat.prime_two hjnd,
    Nat.ordCompl_pow_mul_of_not_dvd t Nat.prime_two hknd] at hc
  refine ⟨hc, ?_⟩
  rw [hc] at he
  have hp : 2 ^ r = 2 ^ t := Nat.eq_of_mul_eq_mul_left hk.pos he
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hp

def dyadicPairs (N : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  ((Icc 1 N).filter Odd).sigma (fun j => range (Nat.log 2 (N / j) + 1))

lemma mem_dyadicPairs {N j r : ℕ} :
    Sigma.mk j r ∈ dyadicPairs N ↔
      1 ≤ j ∧ j ≤ N ∧ Odd j ∧ r ≤ Nat.log 2 (N / j) := by
  simp [dyadicPairs, and_assoc]

/-- The exponents in the denominator product count every integer exactly
once, by its odd part and its power of two. -/
theorem sum_odd_log (N : ℕ) :
    (∑ j ∈ (Icc 1 N).filter Odd, (Nat.log 2 (N / j) + 1)) = N := by
  have hcard : (dyadicPairs N).card = (Icc 1 N).card := by
    apply Finset.card_bij (fun a _ => a.1 * 2 ^ a.2)
    · intro a ha
      rcases (mem_dyadicPairs.mp ha) with ⟨hj, hjN, hjodd, hr⟩
      have hdiv : N / a.1 ≠ 0 := by
        have := Nat.div_pos hjN hj
        omega
      have hpow := Nat.pow_le_of_le_log hdiv hr
      have hbound := (Nat.le_div_iff_mul_le hj).mp hpow
      exact mem_Icc.mpr ⟨Nat.mul_pos hj (by positivity), by simpa [mul_comm] using hbound⟩
    · intro a ha b hb he
      have h := odd_power_two_injective (mem_dyadicPairs.mp ha).2.2.1
        (mem_dyadicPairs.mp hb).2.2.1 he
      cases a
      cases b
      simp only [Sigma.mk.inj_iff, heq_eq_eq]
      exact h
    · intro x hx
      have hx1 := (mem_Icc.mp hx).1
      have hxN := (mem_Icc.mp hx).2
      obtain ⟨r, j, hj, he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : x ≠ 0)
      have hj1 : 1 ≤ j := hj.pos
      have hjx : j ≤ x := by
        rw [he]
        exact Nat.le_mul_of_pos_left j (by positivity)
      have hbound : 2 ^ r ≤ N / j := by
        apply (Nat.le_div_iff_mul_le hj1).mpr
        simpa [he, mul_comm] using hxN
      refine ⟨⟨j, r⟩, mem_dyadicPairs.mpr
        ⟨hj1, hjx.trans hxN, hj, Nat.le_log_of_pow_le (by decide) hbound⟩, ?_⟩
      simpa [mul_comm] using he.symm
  simpa [dyadicPairs, Finset.card_sigma] using hcard

end DenominatorBridge

#print axioms DenominatorBridge.sum_odd_log
