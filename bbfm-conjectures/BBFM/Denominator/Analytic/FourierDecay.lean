import BBFM.Denominator.Analytic.BernoulliFourier
import BBFM.Denominator.Analytic.Edge

noncomputable section
namespace DenominatorResearch
open Finset Real

/-- The uncentered characteristic function of a finite weighted Bernoulli product. -/
def weightedBernoulliChar (m : ℕ → ℕ) (p : ℕ → ℝ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∏ i ∈ range n, (bernoulliChar (p (i + 1)) (((i : ℝ) + 1) * θ)) ^ m (i + 1)

/-- A consecutive block with a uniform variance weight forces Fourier decay. -/
theorem weightedBernoulliChar_decay (m : ℕ → ℕ) (p : ℕ → ℝ) (n q : ℕ) (θ c : ℝ)
    (hq : q ≤ n) (hc : 0 ≤ c) (hθ : |θ| ≤ Real.pi)
    (hp : ∀ i, 1 ≤ i → i ≤ n → 0 ≤ p i ∧ p i ≤ 1)
    (hblock : ∀ i, 1 ≤ i → i ≤ q → c ≤ (m i : ℝ) * p i * (1 - p i)) :
    ‖weightedBernoulliChar m p n θ‖ ≤
      Real.exp (-c * (q : ℝ) / 50000 * min 1 ((q : ℝ) ^ 2 * θ ^ 2)) := by
  have hblocksum : c * sineEnergy q θ ≤
      ∑ i ∈ range q, (m (i + 1) : ℝ) * p (i + 1) * (1 - p (i + 1)) *
        Real.sin (((i : ℝ) + 1) * θ / 2) ^ 2 := by
    unfold sineEnergy
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right
      (hblock (i + 1) (by omega) (by have := mem_range.mp hi; omega)) (sq_nonneg _)
  have hsum : (∑ i ∈ range q, (m (i + 1) : ℝ) * p (i + 1) * (1 - p (i + 1)) *
        Real.sin (((i : ℝ) + 1) * θ / 2) ^ 2) ≤
      ∑ i ∈ range n, (m (i + 1) : ℝ) * p (i + 1) * (1 - p (i + 1)) *
        Real.sin (((i : ℝ) + 1) * θ / 2) ^ 2 := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono hq)
    intro i hi _
    have hp' := hp (i + 1) (by omega) (by have := mem_range.mp hi; omega)
    have hp0 := hp'.1
    have hp1 : 0 ≤ 1 - p (i + 1) := sub_nonneg.mpr hp'.2
    positivity
  have henergy := mul_le_mul_of_nonneg_left (sineEnergy_bound q θ hθ) hc
  have hn := bernoulliProduct_norm_le (range n) (fun i => m (i + 1))
    (fun i => p (i + 1)) (fun i => (i : ℝ) + 1) θ
  apply hn.trans
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Tilt parameter of each actual factor 1+x^i. -/
def tiltedProbability (r : ℝ) (i : ℕ) : ℝ := r ^ i / (1 + r ^ i)

lemma tiltedProbability_range (r : ℝ) (i : ℕ) (hr : 0 ≤ r) :
    0 ≤ tiltedProbability r i ∧ tiltedProbability r i ≤ 1 := by
  have hp : 0 ≤ r ^ i := pow_nonneg hr i
  have hd : 0 < 1 + r ^ i := by linarith
  unfold tiltedProbability
  constructor
  · positivity
  · apply (div_le_iff₀ hd).2
    linarith

lemma tiltedProbability_variance (r : ℝ) (i : ℕ) (hr : 0 ≤ r) :
    tiltedProbability r i * (1 - tiltedProbability r i) = r ^ i / (1 + r ^ i) ^ 2 := by
  have hd : 1 + r ^ i ≠ 0 := by positivity
  unfold tiltedProbability
  field_simp
  <;> ring

/-- Characteristic function associated to the concrete ordinary denominator. -/
def denChar (n : ℕ) (r θ : ℝ) : ℂ :=
  weightedBernoulliChar (fun i => Nat.log 2 (n / i) + 1) (tiltedProbability r) n θ

/-- Decay from the unit-weight factors alone, valid for every radius up to one. -/
theorem denChar_unit_decay (n : ℕ) (r θ : ℝ) (hn : 0 < n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hθ : |θ| ≤ Real.pi) :
    ‖denChar n r θ‖ ≤
      Real.exp (-((Nat.log 2 n + 1 : ℕ) : ℝ) * r / 200000 * min 1 (θ ^ 2)) := by
  have hvar : r / 4 ≤ tiltedProbability r 1 * (1 - tiltedProbability r 1) := by
    rw [tiltedProbability_variance r 1 hr, pow_one]
    apply (le_div_iff₀ (sq_pos_of_pos (show 0 < 1 + r by linarith))).2
    have hsq : (1 + r) ^ 2 ≤ 4 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hsq hr
    nlinarith
  have hh := weightedBernoulliChar_decay (fun i => Nat.log 2 (n / i) + 1)
    (tiltedProbability r) n 1 θ (((Nat.log 2 n + 1 : ℕ) : ℝ) * r / 4)
    (by omega) (by positivity) hθ
    (fun i _ _ => tiltedProbability_range r i hr) (by
      intro i hi hi1
      have hi : i = 1 := by omega
      subst i
      simp only [Nat.div_one]
      have h := mul_le_mul_of_nonneg_left hvar (show 0 ≤ ((Nat.log 2 n + 1 : ℕ) : ℝ) by positivity)
      nlinarith)
  convert hh using 1 <;> simp only [denChar, Nat.cast_one, one_pow, one_mul, mul_one]
  congr 1
  ring

/-- The concrete multiplicities decrease with the weight. -/
lemma den_multiplicity_antitone (n i q : ℕ) (hi : 1 ≤ i) (hiq : i ≤ q) :
    Nat.log 2 (n / q) + 1 ≤ Nat.log 2 (n / i) + 1 := by
  exact Nat.add_le_add_right
    (Nat.log_mono_right (Nat.div_le_div_left hiq (by omega))) 1

/-- A radius-adapted consecutive block yields decay for the actual denominator. -/
theorem denChar_block_decay (n q : ℕ) (r θ : ℝ) (hq : q ≤ n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hrq : 1 / 3 ≤ r ^ q) (hθ : |θ| ≤ Real.pi) :
    ‖denChar n r θ‖ ≤ Real.exp
      (-((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) * (q : ℝ) / 600000 *
        min 1 ((q : ℝ) ^ 2 * θ ^ 2)) := by
  have hblock : ∀ i, 1 ≤ i → i ≤ q →
      ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) / 12 ≤
        ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) * tiltedProbability r i *
          (1 - tiltedProbability r i) := by
    intro i hi hiq
    have hri : 1 / 3 ≤ r ^ i := hrq.trans (pow_le_pow_of_le_one hr hrone hiq)
    have hri1 : r ^ i ≤ 1 := by exact pow_le_one₀ hr hrone
    have hvar : 1 / 12 ≤ tiltedProbability r i * (1 - tiltedProbability r i) := by
      rw [tiltedProbability_variance r i hr]
      apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + r ^ i))).2
      have hsq : (1 + r ^ i) ^ 2 ≤ 4 := by nlinarith [pow_nonneg hr i]
      nlinarith
    have hm : ((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) ≤
        ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) := by
      exact_mod_cast den_multiplicity_antitone n i q hi hiq
    have hh := mul_le_mul_of_nonneg_left hvar
      (show 0 ≤ ((Nat.log 2 (n / i) + 1 : ℕ) : ℝ) by positivity)
    nlinarith
  have h := weightedBernoulliChar_decay (fun i => Nat.log 2 (n / i) + 1)
    (tiltedProbability r) n q θ (((Nat.log 2 (n / q) + 1 : ℕ) : ℝ) / 12)
    hq (by positivity) hθ (fun i _ _ => tiltedProbability_range r i hr) hblock
  convert h using 1
  congr 1
  ring

end DenominatorResearch
