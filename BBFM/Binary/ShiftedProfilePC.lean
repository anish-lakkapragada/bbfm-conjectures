import BBFM.Binary.SeriesMask
import BBFM.Binary.LogConcavity.ShiftedProfileBoundary

open PowerSeries BinaryPowerConcavity
namespace BinaryResearch
noncomputable section

lemma refinedShiftedSeries_recurrence_at (p k : ℕ) (hk : 1 ≤ k) (h : ℝ) :
    ((k : ℝ) + 2 * h) * PowerSeries.coeff k (refinedShiftedSeries p h) =
      (k + p + 2 * h) * PowerSeries.coeff (k - 1) (refinedShiftedSeries p h) +
        2 * h * shiftedProfile p h 0 * (p.choose k : ℝ) := by
  have he := refinedShiftedSeries_recurrence p (k - 1) h
  rw [Nat.sub_add_cancel hk, series_one_add_X_pow_coeff] at he
  have hc : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; norm_num
  rw [hc] at he
  convert he using 1 <;> ring

lemma shifted_forcing_ratio (p k : ℕ) (hkp : k ≤ p) (v : ℝ) :
    (k + 1 : ℝ) * (v * (p.choose (k + 1) : ℝ)) =
      (p - k : ℝ) * (v * (p.choose k : ℝ)) := by
  have hn := Nat.choose_succ_right_eq p k
  have hr : (p.choose (k + 1) : ℝ) * (k + 1 : ℝ) =
      (p.choose k : ℝ) * (p - k : ℝ) := by
    rw [← Nat.cast_sub hkp]
    exact_mod_cast hn
  linear_combination v * hr

/-- Uniform in the degree and real shift: the boundary comparison profile is
power-concave after the minimal dyadic refinement. -/
theorem refinedShiftedSeries_pc (p k : ℕ) (hp : 1 ≤ p) (hk : 1 ≤ k)
    (h : ℝ) (hh : 0 ≤ h) :
    PC p (PowerSeries.coeff (k - 1) (refinedShiftedSeries p h))
      (PowerSeries.coeff k (refinedShiftedSeries p h))
      (PowerSeries.coeff (k + 1) (refinedShiftedSeries p h)) := by
  have hprev := refinedShiftedSeries_recurrence_at p k hk h
  have hnext := refinedShiftedSeries_recurrence_at p (k + 1) (by omega) h
  rw [Nat.add_sub_cancel] at hnext
  by_cases hkp : k ≤ p
  · apply shifted_profile_boundary_pc p k (k + 2 * h) _ _ _
      (2 * h * shiftedProfile p h 0 * (p.choose k : ℝ))
      (2 * h * shiftedProfile p h 0 * (p.choose (k + 1) : ℝ))
    · exact_mod_cast hp
    · positivity
    · exact_mod_cast hkp
    · exact refinedShiftedSeries_nonneg p h hh _
    · have ha0 := shiftedProfile_positive p h hh 0
      positivity
    · positivity
    · convert hprev using 1 <;> ring
    · convert hnext using 1 <;> push_cast <;> ring
    · exact shifted_forcing_ratio p k hkp _
    · have hm := refinedShiftedSeries_mask_ratio p (k - 1) h hh
      rw [Nat.sub_add_cancel hk] at hm
      have hc : ((k - 1 : ℕ) : ℝ) = k - 1 := by rw [Nat.cast_sub hk]; norm_num
      rw [hc] at hm
      convert hm using 1 <;> ring
  · have hz : p.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have hz' : p.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, Nat.cast_zero, mul_zero, add_zero] at hprev
    rw [hz', Nat.cast_zero, mul_zero, add_zero] at hnext
    have he := shifted_profile_homogeneous p (k + 2 * h)
      (PowerSeries.coeff (k - 1) (refinedShiftedSeries p h))
      (PowerSeries.coeff k (refinedShiftedSeries p h))
      (PowerSeries.coeff (k + 1) (refinedShiftedSeries p h))
      (by positivity : (k + 2 * h : ℝ) + 1 ≠ 0)
      (by convert hprev using 1 <;> ring)
      (by convert hnext using 1 <;> push_cast <;> ring)
    exact he.ge

lemma refinedShiftedSeries_coeff_zero (p : ℕ) (h : ℝ) :
    PowerSeries.coeff 0 (refinedShiftedSeries p h) = shiftedProfile p h 0 := by
  simp [refinedShiftedSeries, shiftedSeries]

theorem refinedShiftedSeries_first_ratio (p : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    PowerSeries.coeff 1 (refinedShiftedSeries p h) =
      (p + 1 : ℝ) * PowerSeries.coeff 0 (refinedShiftedSeries p h) := by
  have he := refinedShiftedSeries_recurrence p 0 h
  rw [series_one_add_X_pow_coeff, Nat.choose_one_right,
    refinedShiftedSeries_coeff_zero] at he
  rw [refinedShiftedSeries_coeff_zero]
  have hpos : 0 < 1 + 2 * h := by positivity
  apply (mul_left_cancel₀ hpos.ne')
  push_cast at he ⊢
  linear_combination he

#print axioms refinedShiftedSeries_pc
#print axioms refinedShiftedSeries_first_ratio
end
end BinaryResearch
