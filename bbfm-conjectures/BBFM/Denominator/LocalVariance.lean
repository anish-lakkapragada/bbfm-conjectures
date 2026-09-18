import BBFM.Denominator.RelativeSaddles

/-! Effective variance bounds from the floor-block square mass and the
minimum t / (1 + t)^2 = 3/16 on [1/3, 1]. -/
noncomputable section
namespace BBFMLocal
open Real Finset DenominatorResearch
set_option maxHeartbeats 0

lemma sum_successor_sq_floor (q : ℕ) (hq : 1 ≤ q) :
    ((q : ℝ)+1)^3 ≤ 8*∑ i ∈ range q, ((i : ℝ)+1)^2 := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    rw [sum_range_succ]
    push_cast
    have hq0 : (0 : ℝ) ≤ q := by positivity
    nlinarith [sq_nonneg (q : ℝ)]

lemma variance_block_square_mass (n q : ℕ) (r : ℝ) (hq : q ≤ n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hrq : 1/3 ≤ r^q) :
    ((Nat.log 2 (n/q)+1 : ℕ) : ℝ)*(3/16 : ℝ)*
      (∑ i ∈ range q, ((i : ℝ)+1)^2) ≤
      tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r := by
  let m := fun i => Nat.log 2 (n/i)+1
  have hblock : (m q : ℝ)*(3/16 : ℝ)*(∑ i ∈ range q, ((i : ℝ)+1)^2) ≤
      ∑ i ∈ range q, (m (i+1) : ℝ)*((i : ℝ)+1)^2*r^(i+1)/(1+r^(i+1))^2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hiq : i+1 ≤ q := by have := mem_range.mp hi; omega
    have hri : 1/3 ≤ r^(i+1) := hrq.trans (pow_le_pow_of_le_one hr hrone hiq)
    have hri1 : r^(i+1) ≤ 1 := pow_le_one₀ hr hrone
    have hvar : (3/16 : ℝ) ≤ r^(i+1)/(1+r^(i+1))^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0<1+r^(i+1)))).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hri) (show 0≤3-r^(i+1) by linarith)]
    have hm : (m q : ℝ) ≤ m (i+1) := by
      exact_mod_cast den_multiplicity_antitone n (i+1) q (by omega) hiq
    have hh := mul_le_mul hm hvar (by norm_num : (0 : ℝ)≤3/16)
      (show 0≤(m (i+1) : ℝ) by positivity)
    have hp := mul_le_mul_of_nonneg_right hh (sq_nonneg ((i : ℝ)+1))
    convert hp using 1 <;> ring
  have hsum : (∑ i ∈ range q, (m (i+1) : ℝ)*((i : ℝ)+1)^2*r^(i+1)/(1+r^(i+1))^2) ≤
      tiltedVariance m n r := by
    apply sum_le_sum_of_subset_of_nonneg (range_mono hq)
    intro i hi _
    positivity
  exact hblock.trans hsum

theorem den_effective_variance_lower (n : ℕ) (r L : ℝ) (hL : 1 ≤ L) (hLn : L ≤ n)
    (hr : 0 ≤ r) (hrone : r ≤ 1) (hrq : 1/3 ≤ r^⌊L⌋₊) :
    (1+Real.logb 2 ((n : ℝ)/L))*L^3 ≤
      100*tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r := by
  let q := ⌊L⌋₊
  have hL0 : 0≤L := by linarith
  have hqL : (q : ℝ) ≤ L := Nat.floor_le hL0
  have hqn : q ≤ n := by exact_mod_cast hqL.trans hLn
  have hq1 : 1 ≤ q := (Nat.one_le_floor_iff L).mpr hL
  have hM := den_profile_lower n q L hq1 hqn hL hqL
  have hv := variance_block_square_mass n q r hqn hr hrone hrq
  have hqadd : L ≤ (q : ℝ)+1 := (Nat.lt_floor_add_one L).le
  have hc := (pow_le_pow_left₀ hL0 hqadd 3).trans (sum_successor_sq_floor q hq1)
  have hm0 : 0≤((Nat.log 2 (n/q)+1 : ℕ) : ℝ) := by positivity
  have hM0 : 0≤1+Real.logb 2 ((n : ℝ)/L) := by
    have hnratio : (1 : ℝ) ≤ (n : ℝ)/L :=
      (le_div_iff₀ (by linarith : 0<L)).mpr (by simpa using hLn)
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ)<2) hnratio
    linarith
  have hh := mul_le_mul hM hc (pow_nonneg hL0 3) hm0
  have hV : 0≤tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r := by
    unfold tiltedVariance; positivity
  nlinarith only [hh,hv,hV]

theorem den_large_radius_variance_lower (n : ℕ) (r : ℝ) (hn : 0<n)
    (hr : 1/2<r) (hrone : r≤1) :
    (1+Real.logb 2 ((n : ℝ)/effectiveScale n r))*(effectiveScale n r)^3 ≤
      100*tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r := by
  obtain ⟨hL,hLn,hs⟩ := effectiveScale_bounds n r hn hr hrone
  apply BBFMLocal.den_effective_variance_lower n r (effectiveScale n r) hL hLn (by linarith) hrone
  exact radius_floor_pow_lower r (effectiveScale n r) (by linarith) hrone (by linarith) hs

#print axioms BBFMLocal.den_large_radius_variance_lower
end BBFMLocal
