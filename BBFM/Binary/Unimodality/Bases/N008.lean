import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p008 : List ℕ := [10, 54, 182, 406, 738, 1130, 1594, 2026, 2382, 2560, 2672, 2720, 2764, 2720, 2672, 2560, 2382, 2026, 1594, 1130, 738, 406, 182, 54, 10]

theorem numerator008 : listPoly p008 = numB 8 := by
  exact numB_eq_of_packed 4 (2 ^ 256) p008
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape008 : HasShape (numB 8) (2 * center 8) := by
  rw [← numerator008]
  exact listPoly_shape p008 (2 * center 8)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape008
