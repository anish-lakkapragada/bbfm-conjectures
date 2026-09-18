import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p012 : List ℕ := [20, 166, 814, 2718, 7100, 15298, 28802, 48570, 74984, 106494, 140662, 174038, 204324, 228938, 246746, 256802, 260168, 256802, 246746, 228938, 204324, 174038, 140662, 106494, 74984, 48570, 28802, 15298, 7100, 2718, 814, 166, 20]

theorem numerator012 : listPoly p012 = numB 12 := by
  exact numB_eq_of_packed 6 (2 ^ 256) p012
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape012 : HasShape (numB 12) (2 * center 12) := by
  rw [← numerator012]
  exact listPoly_shape p012 (2 * center 12)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def r012 : List ℕ := [20, 146, 668, 2050, 5050, 10248, 18554, 30016, 44968, 61526, 79136, 94902, 109422, 119516, 127230, 129572, 129572, 127230, 119516, 109422, 94902, 79136, 61526, 44968, 30016, 18554, 10248, 5050, 2050, 668, 146, 20]

theorem residual012 : listPoly r012 = BinaryResearch.residual 12 := by
  exact residual_eq_of_check 12 p012 r012 numerator012 (by decide +kernel)

theorem residualShape012 : HasShape (BinaryResearch.residual 12) (2 * center 12 - 1) := by
  rw [← residual012]
  exact listPoly_shape r012 (2 * center 12 - 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape012
#print axioms BinaryCertificate.Bases.residualShape012
