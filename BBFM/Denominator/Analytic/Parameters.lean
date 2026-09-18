import BBFM.Denominator.Analytic.Basic

noncomputable section
namespace DenominatorResearch
open Real

/-- Exact bridge between the executable integer logarithm and BBFM's real-log formula. -/
theorem multiplicity_real_formula (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    (Nat.log 2 (n / i) : ℤ) = ⌊Real.logb 2 ((n : ℝ) / i)⌋ := by
  have hiR : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hratio : (1 : ℝ) ≤ (n : ℝ) / i := by
    apply (le_div_iff₀ hiR).2
    simp only [one_mul]
    exact_mod_cast hin
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
    Real.floor_logb_natCast (by positivity), Int.log_of_one_le_right 2 hratio,
    Nat.floor_div_natCast, Nat.floor_natCast]

/-- The logarithmic profile inequalities used in the written analytic argument. -/
theorem multiplicity_real_bounds (n i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    Real.logb 2 ((n : ℝ) / i) < (Nat.log 2 (n / i) + 1 : ℕ) ∧
      ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) ≤ Real.logb 2 ((n : ℝ) / i) + 1 := by
  have heq := multiplicity_real_formula n i hi hin
  have heqR : ((Nat.log 2 (n / i) : ℕ) : ℝ) = (⌊Real.logb 2 ((n : ℝ) / i)⌋ : ℝ) := by
    exact_mod_cast heq
  have hl := Int.floor_le (Real.logb 2 ((n : ℝ) / i))
  have hu := Int.lt_floor_add_one (Real.logb 2 ((n : ℝ) / i))
  push_cast
  rw [heqR]
  constructor <;> linarith

/-- The large numerical cutoff covers the remaining small-radius saddle points. -/
theorem effective_parameter_coverage (t k N₀ : ℝ) (hN : 0 < N₀)
    (ht : 100 * N₀ ^ 2 ≤ t) (hnotedge : t < 6 * k ^ 2) (hk : 0 ≤ k) :
    4 * N₀ < k := by
  by_contra h
  have hupper : k ≤ 4 * N₀ := le_of_not_gt h
  have hs := pow_le_pow_left₀ hk hupper 2
  nlinarith [sq_pos_of_pos hN]

end DenominatorResearch
