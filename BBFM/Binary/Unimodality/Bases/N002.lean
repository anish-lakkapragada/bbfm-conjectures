import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p002 : List ℕ := [2, 2, 2]

theorem numerator002 : listPoly p002 = numB 2 := by
  exact numB_eq_of_packed 1 (2 ^ 256) p002
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape002 : HasShape (numB 2) (2 * center 2) := by
  rw [← numerator002]
  exact listPoly_shape p002 (2 * center 2)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape002
