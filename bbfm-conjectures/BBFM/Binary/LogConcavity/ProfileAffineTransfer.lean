import BBFM.Binary.LogConcavity.PowerConcavity
import Mathlib.Topology.Order.IntermediateValue

/-! Local transfer from exact or arbitrarily close comparison-profile ratios.
All profile and cross-product hypotheses remain explicit. -/
namespace BinaryPowerConcavity
open Filter Topology

lemma pc_iff_affine (p a b c : ℝ) (ha : 0 < a) :
    PC p a b c ↔ c*(b/a+p-1) ≤ b*((p+1)*(b/a)-1) := by
  have hid : a*(b*((p+1)*(b/a)-1)-c*(b/a+p-1)) =
      (p+1)*b^2-b*(a+c)-(p-1)*a*c := by
    field_simp
    <;> ring
  unfold PC
  rw [← hid]
  constructor
  · intro h
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h ha)
  · intro h
    exact mul_nonneg ha.le (sub_nonneg.mpr h)

lemma profile_affine_bound (p A B C b c : ℝ) (hp : 1 ≤ p)
    (hA : 0 < A) (hB : 0 < B) (hb : 0 ≤ b)
    (hprofile : PC p A B C) (hcross : c*B ≤ b*C) :
    c*(B/A+p-1) ≤ b*((p+1)*(B/A)-1) := by
  have hu : 0 < B+(p-1)*A := by positivity
  have hf : C*(B+(p-1)*A) ≤ B*((p+1)*B-A) := by
    unfold PC at hprofile
    nlinarith only [hprofile]
  have h1 := mul_le_mul_of_nonneg_right hcross hu.le
  have h2 := mul_le_mul_of_nonneg_left hf hb
  have htotal : c*(B+(p-1)*A) ≤ b*((p+1)*B-A) := by
    apply (mul_le_mul_iff_right₀ hB).mp
    nlinarith only [h1,h2]
  apply (mul_le_mul_iff_right₀ hA).mp
  field_simp
  nlinarith only [htotal]

lemma pc_of_exact_profile_match (p A B C a b c : ℝ) (hp : 1 ≤ p)
    (hA : 0 < A) (hB : 0 < B) (ha : 0 < a) (hb : 0 < b)
    (hprofile : PC p A B C) (hmatch : b*A=a*B) (hcross : c*B ≤ b*C) :
    PC p a b c := by
  have hratio : B/A=b/a := by apply (div_eq_div_iff hA.ne' ha.ne').mpr; nlinarith only [hmatch]
  apply (pc_iff_affine p a b c ha).mpr
  rw [← hratio]
  exact profile_affine_bound p A B C b c hp hA hB hb.le hprofile hcross

/-- An affine upper bound on every ratio strictly above b/a extends to b/a.
This removes any need to assume an exact matching comparison profile exists. -/
theorem pc_of_affine_bounds (p a b c U : ℝ) (ha : 0 < a) (hU : b/a < U)
    (h : ∀ ρ : ℝ, b/a < ρ → ρ < U → c*(ρ+p-1) ≤ b*((p+1)*ρ-1)) :
    PC p a b c := by
  let F : ℝ → ℝ := fun ρ => b*((p+1)*ρ-1)-c*(ρ+p-1)
  have hc : Continuous F := by dsimp [F]; fun_prop
  have ht : Tendsto F (𝓝[>] (b/a)) (𝓝 (F (b/a))) :=
    hc.continuousAt.tendsto.mono_left inf_le_left
  have he : ∀ᶠ ρ in 𝓝[>] (b/a), 0 ≤ F ρ := by
    have hlo : ∀ᶠ ρ in 𝓝[>] (b/a), b/a < ρ := self_mem_nhdsWithin
    have hhi : ∀ᶠ ρ in 𝓝[>] (b/a), ρ < U :=
      Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hU)
    filter_upwards [hlo,hhi] with ρ hlo hhi
    exact sub_nonneg.mpr (h ρ hlo hhi)
  have hlim : 0 ≤ F (b/a) := ge_of_tendsto ht he
  exact (pc_iff_affine p a b c ha).mpr (sub_nonneg.mp hlim)

#print axioms profile_affine_bound
#print axioms pc_of_exact_profile_match
#print axioms pc_of_affine_bounds
end BinaryPowerConcavity
