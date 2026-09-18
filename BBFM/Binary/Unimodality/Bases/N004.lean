import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p004 : List ℕ := [4, 10, 18, 18, 20, 18, 18, 10, 4]

theorem numerator004 : listPoly p004 = numB 4 := by
  exact numB_eq_of_packed 2 (2 ^ 256) p004
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape004 : HasShape (numB 4) (2 * center 4) := by
  rw [← numerator004]
  exact listPoly_shape p004 (2 * center 4)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape004
