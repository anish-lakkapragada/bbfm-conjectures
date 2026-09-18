import BBFM.Denominator.Analytic.Edge

noncomputable section
namespace DenominatorResearch
open Polynomial Finset

lemma bernoulli_reverse (s : ℕ) : (1 + (X : ℝ[X]) ^ s).reverse = 1 + X ^ s := by
  change (C 1 + (X : ℝ[X]) ^ s).reverse = 1 + X ^ s
  rw [reverse_C_add]
  simp [Polynomial.reverse]
  ring

lemma reverse_pow_eq {P : ℝ[X]} (hP : P.reverse = P) (r : ℕ) :
    (P ^ r).reverse = P ^ r := by
  induction r with
  | zero => simp [Polynomial.reverse]
  | succ r ih => rw [pow_succ, reverse_mul_of_domain, ih, hP]

lemma reverse_prod_eq {α : Type*} (s : Finset α) (P : α → ℝ[X])
    (hP : ∀ i ∈ s, (P i).reverse = P i) : (∏ i ∈ s, P i).reverse = ∏ i ∈ s, P i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.reverse]
  | @insert i s hi ih =>
    rw [prod_insert hi, reverse_mul_of_domain, hP i (by simp),
      ih (fun j hj => hP j (by simp [hj]))]

lemma weightedProduct_reverse (m : ℕ → ℕ) (n : ℕ) :
    (weightedProduct m n).reverse = weightedProduct m n :=
  reverse_prod_eq _ _ fun i _ => reverse_pow_eq (bernoulli_reverse _) _

lemma den_reverse (n : ℕ) : (den n).reverse = den n := weightedProduct_reverse _ _

/-- Reflection is proved from the concrete product. -/
theorem den_coeff_reflect (n k : ℕ) (hk : k ≤ (den n).natDegree) :
    (den n).coeff ((den n).natDegree - k) = (den n).coeff k := by
  have h := congrArg (fun P : ℝ[X] => P.coeff k) (den_reverse n)
  simpa only [coeff_reverse, revAt_le hk] using h

/-- The compiled edge theorem also applies at the other end of the coefficient list. -/
theorem den_upper_edge_logconcave (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hD : k + 1 ≤ (den n).natDegree) (hsize : 6 * k ^ 2 ≤ Nat.log 2 n + 1) :
    (den n).coeff ((den n).natDegree - k - 1) *
      (den n).coeff ((den n).natDegree - k + 1) ≤
      (den n).coeff ((den n).natDegree - k) ^ 2 := by
  have hleft := den_coeff_reflect n (k + 1) hD
  have hright := den_coeff_reflect n (k - 1) (by omega)
  have hcenter := den_coeff_reflect n k (by omega)
  have heq : (den n).natDegree - (k - 1) = (den n).natDegree - k + 1 := by omega
  rw [heq] at hright
  rw [← Nat.sub_add_eq, hleft, hright, hcenter, mul_comm]
  exact den_edge_logconcave n k hn hk hsize

end DenominatorResearch
