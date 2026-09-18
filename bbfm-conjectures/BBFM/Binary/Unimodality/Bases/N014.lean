import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p014 : List ℕ := [26, 250, 1402, 5376, 15976, 38792, 80936, 149280, 249304, 381208, 539160, 710048, 879256, 1031736, 1156952, 1246784, 1299964, 1316956, 1299964, 1246784, 1156952, 1031736, 879256, 710048, 539160, 381208, 249304, 149280, 80936, 38792, 15976, 5376, 1402, 250, 26]

theorem numerator014 : listPoly p014 = numB 14 := by
  exact numB_eq_of_packed 7 (2 ^ 256) p014
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape014 : HasShape (numB 14) (2 * center 14) := by
  rw [← numerator014]
  exact listPoly_shape p014 (2 * center 14)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def r014 : List ℕ := [26, 224, 1178, 4198, 11778, 27014, 53922, 95358, 153946, 227262, 311898, 398150, 481106, 550630, 606322, 640462, 659502, 659502, 640462, 606322, 550630, 481106, 398150, 311898, 227262, 153946, 95358, 53922, 27014, 11778, 4198, 1178, 224, 26]

theorem residual014 : listPoly r014 = BinaryResearch.residual 14 := by
  exact residual_eq_of_check 14 p014 r014 numerator014 (by decide +kernel)

theorem residualShape014 : HasShape (BinaryResearch.residual 14) (2 * center 14 - 1) := by
  rw [← residual014]
  exact listPoly_shape r014 (2 * center 14 - 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape014
#print axioms BinaryCertificate.Bases.residualShape014
