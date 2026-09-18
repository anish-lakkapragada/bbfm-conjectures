import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p010 : List ℕ := [14, 94, 382, 1040, 2228, 3924, 6100, 8496, 10866, 12722, 13986, 14656, 15064, 15160, 15064, 14656, 13986, 12722, 10866, 8496, 6100, 3924, 2228, 1040, 382, 94, 14]

theorem numerator010 : listPoly p010 = numB 10 := by
  exact numB_eq_of_packed 5 (2 ^ 256) p010
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape010 : HasShape (numB 10) (2 * center 10) := by
  rw [← numerator010]
  exact listPoly_shape p010 (2 * center 10)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def r010 : List ℕ := [14, 80, 302, 738, 1490, 2434, 3666, 4830, 6036, 6686, 7300, 7356, 7708, 7708, 7356, 7300, 6686, 6036, 4830, 3666, 2434, 1490, 738, 302, 80, 14]

theorem residual010 : listPoly r010 = BinaryResearch.residual 10 := by
  exact residual_eq_of_check 10 p010 r010 numerator010 (by decide +kernel)

theorem residualShape010 : HasShape (BinaryResearch.residual 10) (2 * center 10 - 1) := by
  rw [← residual010]
  exact listPoly_shape r010 (2 * center 10 - 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape010
#print axioms BinaryCertificate.Bases.residualShape010
