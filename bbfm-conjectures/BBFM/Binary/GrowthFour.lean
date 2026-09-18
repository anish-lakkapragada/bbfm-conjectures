import BBFM.Binary.Growth

namespace BinaryResearch
lemma growth_budget_four (m : ℕ) (hm : 48 ≤ m) :
    8 * (2 * m - 2) * (3 ^ (2 * m) + 2 ^ (2 * m + 2)) ≤
      3 ^ (m - 1) * 2 ^ (2 * m) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hA : 8 * (2 * (m + 1) - 2) * 9 ≤ 12 * (8 * (2 * m - 2)) := by omega
    have hB : 8 * (2 * (m + 1) - 2) * 4 ≤ 12 * (8 * (2 * m - 2)) := by omega
    have hpow : 3 ^ ((m + 1) - 1) * 2 ^ (2 * (m + 1)) =
        12 * (3 ^ (m - 1) * 2 ^ (2 * m)) := by
      rw [show (m + 1) - 1 = (m - 1) + 1 by omega,
        show 2 * (m + 1) = 2 * m + 2 by omega, pow_add, pow_add]
      norm_num
      ring
    rw [hpow, show 2 * (m + 1) = 2 * m + 2 by omega,
      show 2 * m + 2 + 2 = (2 * m + 2) + 2 by omega, pow_add, pow_add]
    norm_num
    calc
      8 * (2 * m + 2 - 2) * (3 ^ (2 * m) * 9 + 2 ^ (2 * m + 2) * 4) =
          (8 * (2 * (m + 1) - 2) * 9) * 3 ^ (2 * m) +
          (8 * (2 * (m + 1) - 2) * 4) * 2 ^ (2 * m + 2) := by ring_nf
      _ ≤ (12 * (8 * (2 * m - 2))) * 3 ^ (2 * m) +
          (12 * (8 * (2 * m - 2))) * 2 ^ (2 * m + 2) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hA) (Nat.mul_le_mul_right _ hB)
      _ = 12 * (8 * (2 * m - 2) * (3 ^ (2 * m) + 2 ^ (2 * m + 2))) := by ring
      _ ≤ 12 * (3 ^ (m - 1) * 2 ^ (2 * m)) := Nat.mul_le_mul_left 12 ih

/-- The central binomial smoothing pays both the new `3^n` slope and two `2^n` corrections. -/
theorem central_smoothing_budget_four (m : ℕ) (hm : 48 ≤ m) :
    3 ^ (2 * m) + 2 ^ (2 * m + 2) ≤
      3 ^ (m - 1) * (2 * m - 3).choose (m - 2) := by
  have ha := central_binomial_average m (by omega)
  have hg := growth_budget_four m hm
  have hp : 2 ^ (2 * m) = 8 * 2 ^ (2 * m - 3) := by
    rw [show 2 * m = (2 * m - 3) + 3 by omega, pow_add]
    norm_num
    ring
  rw [hp] at hg
  have hmul := Nat.mul_le_mul_left (8 * 3 ^ (m - 1)) ha
  have hpos : 0 < 8 * (2 * m - 2) := by omega
  apply (Nat.mul_le_mul_left_iff hpos).mp
  calc
    8 * (2 * m - 2) * (3 ^ (2 * m) + 2 ^ (2 * m + 2)) ≤
        3 ^ (m - 1) * (8 * 2 ^ (2 * m - 3)) := hg
    _ ≤ (8 * (2 * m - 2)) *
        (3 ^ (m - 1) * (2 * m - 3).choose (m - 2)) := by nlinarith [hmul]


#print axioms central_smoothing_budget_four
end BinaryResearch
