import BBFM.Binary.LogConcavity.PowerConcavitySequence

open Polynomial BinaryResearch BinaryShape
namespace BinaryPowerClosure

lemma intCoeff_bernoulli (P : ℤ[X]) (z : ℤ) :
    intCoeff ((1 + X) * P) z = bernoulli (intCoeff P) z := by
  by_cases hz : 0 ≤ z
  · lift z to ℕ using hz
    cases z with
    | zero => simp [intCoeff, bernoulli, add_mul]
    | succ n =>
      have he : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      simp only [bernoulli, he, intCoeff_nat,
        add_mul, one_mul, coeff_add, coeff_X_mul]
      omega
  · have hz' : ¬ 0 ≤ z - 1 := by omega
    simp only [bernoulli, intCoeff, if_neg hz, if_neg hz', add_zero]

theorem bernoulli_polynomial_interval (P : ℤ[X]) (lo hi : ℤ)
    (h : IntervalPositive (intCoeff P) lo hi) :
    IntervalPositive (intCoeff ((1 + X) * P)) lo (hi + 1) := by
  have he : intCoeff ((1 + X) * P) = bernoulli (intCoeff P) :=
    funext (intCoeff_bernoulli P)
  rw [he]
  exact bernoulli_interval h

theorem bernoulli_polynomial_pc (P : ℤ[X]) (lo hi p : ℤ) (hp : 1 ≤ p)
    (hs : IntervalPositive (intCoeff P) lo hi) (h : PowerConcave p P) :
    PowerConcave (p + 1) ((1 + X) * P) := by
  intro z
  simp only [intCoeff_bernoulli]
  exact bernoulli_pc hp hs h z

/-- Every additional binomial smoothing factor raises the quantitative
power-concavity parameter by exactly its exponent. -/
theorem binomial_preserves (P : ℤ[X]) (lo hi p : ℤ) (hp : 1 ≤ p)
    (hs : IntervalPositive (intCoeff P) lo hi) (h : PowerConcave p P) (r : ℕ) :
    IntervalPositive (intCoeff ((1 + X) ^ r * P)) lo (hi + r) ∧
      PowerConcave (p + r) ((1 + X) ^ r * P) := by
  induction r with
  | zero => simpa using And.intro hs h
  | succ r ih =>
    have hpr : 1 ≤ p + (r : ℤ) := by omega
    have hs' := bernoulli_polynomial_interval _ lo (hi + r) ih.1
    have h' := bernoulli_polynomial_pc _ lo (hi + r) (p + r) hpr ih.1 ih.2
    have he : ((1 + X : ℤ[X]) ^ (r + 1)) * P =
        (1 + X) * ((1 + X) ^ r * P) := by rw [pow_succ', mul_assoc]
    rw [he]
    simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using And.intro hs' h'

#print axioms bernoulli_polynomial_pc
#print axioms binomial_preserves
end BinaryPowerClosure
