import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Abel summation transfers every finite prefix inequality to every
decreasing nonnegative weight profile. -/
namespace BBFMMoment
open Finset

lemma abel_range (w f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, w i*f i) = w n*(∑ i ∈ range n, f i)+
      ∑ j ∈ range n, (w j-w (j+1))*(∑ i ∈ range (j+1), f i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih,sum_range_succ]
    simp only [sum_range_succ]
    ring

theorem weighted_prefix_nonnegative (w f : ℕ → ℝ) (n : ℕ)
    (hw : 0≤w n) (hstep : ∀ i<n, w (i+1)≤w i)
    (hprefix : ∀ k≤n, 0≤∑ i ∈ range k, f i) :
    0≤∑ i ∈ range n, w i*f i := by
  rw [abel_range]
  apply add_nonneg (mul_nonneg hw (hprefix n le_rfl))
  apply sum_nonneg
  intro j hj
  exact mul_nonneg (sub_nonneg.mpr (hstep j (mem_range.mp hj)))
    (hprefix (j+1) (by have := mem_range.mp hj; omega))

theorem weighted_prefix_le (w a b : ℕ → ℝ) (n : ℕ)
    (hw : 0≤w n) (hstep : ∀ i<n, w (i+1)≤w i)
    (hprefix : ∀ k≤n, (∑ i ∈ range k, a i)≤∑ i ∈ range k, b i) :
    (∑ i ∈ range n, w i*a i)≤∑ i ∈ range n, w i*b i := by
  have hh := weighted_prefix_nonnegative w (fun i => b i-a i) n hw hstep
    (fun k hk => by simpa only [sum_sub_distrib,sub_nonneg] using hprefix k hk)
  simpa only [mul_sub,sum_sub_distrib,sub_nonneg] using hh

#print axioms weighted_prefix_le
end BBFMMoment
