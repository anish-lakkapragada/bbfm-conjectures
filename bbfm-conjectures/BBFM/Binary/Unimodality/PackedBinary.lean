import BBFM.Binary.Unimodality.PackedPolynomial
import BBFM.Binary.Residual

open Polynomial Finset BinaryResearch
namespace BinaryCertificate

def packedJump (m b : ℕ) : ℕ := ∑ r ∈ range (jumpLength m), b ^ (2 * r)

def packedEven : (m b : ℕ) → ℕ
  | 0, _ => 1
  | m + 1, b => packedJump m b * packedEven m b +
      (1 + b) ^ (2 * m + 2) * packedEven ((m + 1) / 2) (b ^ 2)
termination_by m _ => m
decreasing_by all_goals omega

lemma numB_reduce_half (n : ℕ) : numB n = numB (2 * (n / 2)) := by
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · congr 1
    omega
  · have hn : n = 2 * (n / 2) + 1 := by omega
    conv_lhs => rw [hn]
    exact numB_odd _

lemma jump_eval_packed (m b : ℕ) : (jump m).eval (b : ℤ) = (packedJump m b : ℕ) := by
  rw [jump_geometric]
  simp [packedJump, eval_finsetSum]

theorem numB_eval_packed (m b : ℕ) : (numB (2 * m)).eval (b : ℤ) = (packedEven m b : ℕ) := by
  induction m using Nat.strong_induction_on generalizing b with
  | h m ih =>
    cases m with
    | zero => simp [numB_zero, packedEven]
    | succ m =>
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, numB_even_recurrence]
      rw [eval_add, eval_mul, eval_mul, jump_eval_packed,
        ih m (by omega), numB_reduce_half (m + 1), eval_comp]
      simp only [eval_pow, eval_add, eval_one, eval_X]
      have hh := ih ((m + 1) / 2) (by omega) (b ^ 2)
      push_cast at hh
      rw [hh]
      simp only [packedEven, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]

/-- Check a candidate coefficient list by two scalar evaluations of the
original partition numerator, with no partition enumeration. -/
theorem numB_eq_of_packed (m b : ℕ) (p : List ℕ)
    (hbase : packedEven m 1 < b) (hp : ∀ a ∈ p, a < b)
    (hvalue : Nat.ofDigits b p = packedEven m b) : listPoly p = numB (2 * m) := by
  apply polynomial_eq_of_packed _ (2 * center (2 * m)) b p
    (numB_support (2 * m)) (numB_nonneg (2 * m))
  · have hh := numB_eval_packed m 1
    norm_num at hh
    rw [hh]
    exact_mod_cast hbase
  · exact hp
  · rw [numB_eval_packed, hvalue]

end BinaryCertificate

#print axioms BinaryCertificate.numB_eval_packed
#print axioms BinaryCertificate.numB_eq_of_packed
