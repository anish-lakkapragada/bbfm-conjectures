import BBFM.Denominator.Analytic.Moments

noncomputable section
namespace DenominatorResearch
open Finset Polynomial

lemma weightedProduct_eval_zero (m : ℕ → ℕ) (n : ℕ) :
    (weightedProduct m n).eval 0 = 1 := by
  simp [weightedProduct, Polynomial.eval_prod]

lemma bernoulli_factor_ne_zero (i : ℕ) : (1 + (X : ℝ[X]) ^ (i + 1)) ≠ 0 := by
  intro h
  have hh := congrArg (fun P : ℝ[X] => P.eval 0) h
  simp at hh

/-- Exact degree of the genuine finite weighted product. -/
theorem weightedProduct_natDegree (m : ℕ → ℕ) (n : ℕ) :
    (weightedProduct m n).natDegree = ∑ i ∈ range n, m (i + 1) * (i + 1) := by
  unfold weightedProduct
  rw [Polynomial.natDegree_prod]
  · apply sum_congr rfl
    intro i hi
    rw [Polynomial.natDegree_pow,
      Polynomial.natDegree_add_eq_right_of_natDegree_lt]
    · simp [mul_comm]
    · simp
  · intro i hi
    exact pow_ne_zero _ (bernoulli_factor_ne_zero i)

lemma tiltedMean_zero (m : ℕ → ℕ) (n : ℕ) : tiltedMean m n 0 = 0 := by
  simp [tiltedMean]

lemma tiltedMean_one (m : ℕ → ℕ) (n : ℕ) :
    tiltedMean m n 1 = ((weightedProduct m n).natDegree : ℝ) / 2 := by
  rw [weightedProduct_natDegree]
  unfold tiltedMean
  push_cast
  simp only [one_pow, mul_one]
  norm_num
  rw [sum_div]

lemma tiltedMean_continuousOn (m : ℕ → ℕ) (n : ℕ) :
    ContinuousOn (tiltedMean m n) (Set.Icc 0 1) := by
  unfold tiltedMean
  apply continuousOn_finset_sum
  intro i hi
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro r hr
    have hr0 : 0 ≤ r := hr.1
    positivity

/-- Every positive coefficient index up to the middle has an actual tilting radius.
The endpoint is the degree of the concrete product, not an assumed range parameter. -/
theorem exists_saddle_radius (m : ℕ → ℕ) (n : ℕ) (k : ℝ) (hk : 0 < k)
    (hmid : k ≤ ((weightedProduct m n).natDegree : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ tiltedMean m n r = k := by
  have hx : k ∈ Set.Icc (tiltedMean m n 0) (tiltedMean m n 1) := by
    rw [tiltedMean_zero, tiltedMean_one]
    exact ⟨hk.le, hmid⟩
  obtain ⟨r, hr, heq⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (tiltedMean_continuousOn m n) hx
  refine ⟨r, ?_, hr.2, heq⟩
  by_contra h
  have hr0 : r = 0 := le_antisymm (le_of_not_gt h) hr.1
  subst r
  rw [tiltedMean_zero] at heq
  linarith

theorem den_exists_saddle_radius (n : ℕ) (k : ℝ) (hk : 0 < k)
    (hmid : k ≤ ((den n).natDegree : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ tiltedMean (fun i => Nat.log 2 (n / i) + 1) n r = k :=
  exists_saddle_radius _ _ _ hk hmid

end DenominatorResearch
