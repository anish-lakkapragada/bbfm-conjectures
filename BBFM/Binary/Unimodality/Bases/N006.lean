import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p006 : List ℕ := [6, 22, 54, 80, 100, 100, 100, 80, 54, 22, 6]

theorem numerator006 : listPoly p006 = numB 6 := by
  exact numB_eq_of_packed 3 (2 ^ 256) p006
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape006 : HasShape (numB 6) (2 * center 6) := by
  rw [← numerator006]
  exact listPoly_shape p006 (2 * center 6)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape006
