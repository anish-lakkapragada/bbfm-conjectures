import BBFM.Binary.ShiftedProfile
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! Analytic matching of finite positive mixtures of exact shifted profiles. -/
noncomputable section
open Finset Filter Topology
namespace BinaryProfileMixtures
open BinaryResearch

def weightSum (d : ℕ) (w : ℕ → ℝ) : ℝ := ∑ i ∈ range (d+1), w i

def mix (p d : ℕ) (w : ℕ → ℝ) (h : ℝ) : ℝ :=
  ∑ i ∈ range (d+1), w i * shiftedProfile p h i

theorem continuous_mix (p d : ℕ) (w : ℕ → ℝ) : Continuous (mix p d w) := by
  unfold mix shiftedProfile
  fun_prop

theorem mix_positive (p d : ℕ) (w : ℕ → ℝ)
    (hw : ∀ i ∈ range (d+1), 0 ≤ w i) (hW : 0 < weightSum d w)
    (h : ℝ) (hh : 0 ≤ h) : 0 < mix p d w h := by
  unfold mix
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hw i hi) (shiftedProfile_positive p h hh i).le
  · obtain ⟨i,hi,hwi⟩ := (Finset.sum_pos_iff_of_nonneg hw).mp hW
    exact ⟨i,hi,mul_pos hwi (shiftedProfile_positive p h hh i)⟩

theorem profile_factor_tendsto (k i : ℕ) :
    Tendsto (fun h : ℝ => (h+k+i+1)/(h+1)) atTop (𝓝 1) := by
  have ht : Tendsto (fun h : ℝ => h+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_id
  have hf := (tendsto_const_nhds (x := (1:ℝ))).add (ht.const_div_atTop ((k:ℝ)+i))
  have hh : (fun h : ℝ => 1+((k:ℝ)+i)/(h+1)) =ᶠ[atTop]
      (fun h : ℝ => (h+k+i+1)/(h+1)) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with h hh
    have hne : h+1 ≠ 0 := by linarith
    field_simp
    <;> ring
  simpa only [add_zero] using hf.congr' hh

theorem shiftedProfile_normalized_tendsto (p k : ℕ) :
    Tendsto (fun h : ℝ => shiftedProfile p h k/(h+1)^p) atTop (𝓝 1) := by
  have hp := tendsto_finsetProd (range p) (fun i _ => profile_factor_tendsto k i)
  simpa only [prod_const_one,prod_div_distrib,prod_const,card_range,shiftedProfile] using hp

theorem mix_normalized_tendsto (p d : ℕ) (w : ℕ → ℝ) :
    Tendsto (fun h : ℝ => mix p d w h/(h+1)^p) atTop (𝓝 (weightSum d w)) := by
  have hs := tendsto_finsetSum (range (d+1)) (fun i _ =>
    (tendsto_const_nhds (x := w i)).mul (shiftedProfile_normalized_tendsto p i))
  simpa only [mul_one,← mul_div_assoc,← Finset.sum_div,mix,weightSum] using hs

theorem mix_ratio_tendsto (p dA dB : ℕ) (wA wB : ℕ → ℝ)
    (hWA : weightSum dA wA ≠ 0) :
    Tendsto (fun h : ℝ => mix p dB wB h / mix p dA wA h) atTop
      (𝓝 (weightSum dB wB / weightSum dA wA)) := by
  have hh := (mix_normalized_tendsto p dB wB).div
    (mix_normalized_tendsto p dA wA) hWA
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with h hh
  exact div_div_div_cancel_right₀ (pow_ne_zero p (by linarith : h+1≠0)) _ _

/-- Any strict intermediate ratio between the limit at infinity and the
zero-shift value is attained at a positive finite shift. No monotonicity
assumption is required. -/
theorem exists_positive_shift_ratio (p dA dB : ℕ) (wA wB : ℕ → ℝ)
    (hwA : ∀ i ∈ range (dA+1), 0 ≤ wA i) (hWA : 0 < weightSum dA wA)
    (y : ℝ) (hylo : weightSum dB wB / weightSum dA wA < y)
    (hyhi : y < mix p dB wB 0 / mix p dA wA 0) :
    ∃ h : ℝ, 0 < h ∧ mix p dB wB h / mix p dA wA h = y := by
  let f : ℝ → ℝ := fun h => mix p dB wB h / mix p dA wA h
  have hlim := mix_ratio_tendsto p dA dB wA wB hWA.ne'
  have he : ∀ᶠ h : ℝ in atTop, f h < y := hlim.eventually_lt_const hylo
  obtain ⟨H,hH,hfH⟩ := (he.and (eventually_ge_atTop (0:ℝ))).exists
  have hcont : ContinuousOn f (Set.Icc 0 H) := by
    apply (continuous_mix p dB wB).continuousOn.div (continuous_mix p dA wA).continuousOn
    intro h hh
    exact (mix_positive p dA wA hwA hWA h hh.1).ne'
  obtain ⟨h,hh,hfh⟩ := intermediate_value_Icc' hfH hcont ⟨hH.le,hyhi.le⟩
  refine ⟨h,?_,hfh⟩
  have hn : h ≠ 0 := by
    intro hz
    subst h
    exact (ne_of_lt hyhi) hfh.symm
  exact lt_of_le_of_ne hh.1 hn.symm

#print axioms mix_normalized_tendsto
#print axioms exists_positive_shift_ratio
end BinaryProfileMixtures
