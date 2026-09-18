import BBFM.Denominator.Analytic.Differential
import BBFM.Denominator.Analytic.Sequence

noncomputable section
namespace DenominatorResearch
open Polynomial Finset

/-- General theorem for a genuine finite weighted Bernoulli product.
The only inputs are bounds on its multiplicities and the requested coefficient index. -/
theorem weightedProduct_edge_logconcave (m : ℕ → ℕ) (n k : ℕ) (hn : 0 < n)
    (hk : 1 ≤ k) (hm : ∀ i, 1 ≤ i → i ≤ n → m i ≤ m 1)
    (ht : 6 * k ^ 2 ≤ m 1) :
    (weightedProduct m n).coeff (k - 1) * (weightedProduct m n).coeff (k + 1) ≤
      (weightedProduct m n).coeff k ^ 2 := by
  apply edge_logconcave_of_bounds (fun j => (weightedProduct m n).coeff j) (m 1) k hk
  · exact_mod_cast ht
  · exact weightedProduct_nonneg m n
  · exact weightedProduct_coeff_lower m n hn
  · exact weightedProduct_coeff_upper m n (m 1) k hm

/-- Explicit unbounded edge range for BBFM's concrete denominator.
This is weaker than log-concavity of every coefficient. -/
theorem den_edge_logconcave (n k : ℕ) (hn : 0 < n) (hk : 1 ≤ k)
    (hsize : 6 * k ^ 2 ≤ Nat.log 2 n + 1) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  unfold den
  apply weightedProduct_edge_logconcave _ n k hn hk
  · intro i hi hin
    simp only [Nat.div_one]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self n i)) 1
  · simpa using hsize

/-- A direct exponential threshold for each individual coefficient index. -/
theorem den_edge_logconcave_of_pow_le (n k : ℕ) (hk : 1 ≤ k)
    (hsize : 2 ^ (6 * k ^ 2) ≤ n) :
    (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  have hn : 0 < n := lt_of_lt_of_le (by positivity : 0 < 2 ^ (6 * k ^ 2)) hsize
  apply den_edge_logconcave n k hn hk
  have hlog := Nat.le_log_of_pow_le (by decide : 1 < 2) hsize
  omega

/-- Every fixed positive coefficient index satisfies its Turán inequality eventually. -/
theorem den_coefficientwise_eventual_logconcave (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n ≥ N,
      (den n).coeff (k - 1) * (den n).coeff (k + 1) ≤ (den n).coeff k ^ 2 := by
  exact ⟨2 ^ (6 * k ^ 2), fun n hn => den_edge_logconcave_of_pow_le n k hk hn⟩

end DenominatorResearch
