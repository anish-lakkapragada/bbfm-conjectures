import BBFM.Binary.PowerConcavity
import BBFM.Binary.Unimodality.BinomialSmoothing

open Polynomial
namespace BinaryResearch

lemma powerConcaveAt_reverse (p a b c : ℤ) :
    PowerConcaveAt p a b c ↔ PowerConcaveAt p c b a := by
  unfold PowerConcaveAt
  constructor <;> intro h <;> nlinarith

/-- Reflection and zero extension reduce quantitative concavity to the natural
indices in the lower half, including the first-ratio condition at zero. -/
theorem powerConcave_of_lower_half (p : ℤ) (Q : ℤ[X]) (D : ℕ)
    (hQ : BinaryShape.HasShape Q D)
    (h : ∀ k : ℕ, 2 * k ≤ D →
      PowerConcaveAt p (BinaryShape.intCoeff Q ((k : ℤ) - 1))
        (BinaryShape.intCoeff Q k) (BinaryShape.intCoeff Q ((k : ℤ) + 1))) :
    PowerConcave p Q := by
  have hneg (z : ℤ) (hz : z < 0) :
      PowerConcaveAt p (BinaryShape.intCoeff Q (z - 1))
        (BinaryShape.intCoeff Q z) (BinaryShape.intCoeff Q (z + 1)) := by
    have hleft : BinaryShape.intCoeff Q (z - 1) = 0 := by
      exact if_neg (by omega)
    have hmid : BinaryShape.intCoeff Q z = 0 := by
      exact if_neg (by omega)
    rw [hleft, hmid]
    simp [PowerConcaveAt]
  have hr := BinaryShape.intCoeff_reflection Q D hQ.support hQ.symm
  intro z
  by_cases hz : z < 0
  · exact hneg z hz
  by_cases hhalf : 2 * z ≤ D
  · have hzN : (z.toNat : ℤ) = z := by omega
    simpa only [hzN] using h z.toNat (by omega)
  · have href : PowerConcaveAt p
        (BinaryShape.intCoeff Q ((D : ℤ) - z - 1))
        (BinaryShape.intCoeff Q ((D : ℤ) - z))
        (BinaryShape.intCoeff Q ((D : ℤ) - z + 1)) := by
      by_cases hDz : (D : ℤ) - z < 0
      · exact hneg _ hDz
      · have hzN : (((D : ℤ) - z).toNat : ℤ) = (D : ℤ) - z := by omega
        simpa only [hzN] using h ((D : ℤ) - z).toNat (by omega)
    have he₁ : (D : ℤ) - z - 1 = (D : ℤ) - (z + 1) := by ring
    have he₂ : (D : ℤ) - z + 1 = (D : ℤ) - (z - 1) := by ring
    rw [he₁, he₂, hr, hr, hr] at href
    exact (powerConcaveAt_reverse p _ _ _).mpr href

end BinaryResearch

#print axioms BinaryResearch.powerConcave_of_lower_half
