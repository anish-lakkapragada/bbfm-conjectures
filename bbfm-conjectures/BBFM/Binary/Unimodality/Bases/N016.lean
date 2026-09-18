import BBFM.Binary.Unimodality.ListShapeChecks

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate.Bases
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def p016 : List ℕ := [36, 410, 2682, 12090, 42266, 121250, 298946, 652386, 1289474, 2341210, 3947930, 6233242, 9290634, 13166770, 17864978, 23337106, 29505636, 36261806, 43477230, 50968078, 58505094, 65808294, 72601702, 78625638, 83708958, 87785694, 90931774, 93290526, 95038934, 96310278, 97203078, 97741862, 97927344, 97741862, 97203078, 96310278, 95038934, 93290526, 90931774, 87785694, 83708958, 78625638, 72601702, 65808294, 58505094, 50968078, 43477230, 36261806, 29505636, 23337106, 17864978, 13166770, 9290634, 6233242, 3947930, 2341210, 1289474, 652386, 298946, 121250, 42266, 12090, 2682, 410, 36]

theorem numerator016 : listPoly p016 = numB 16 := by
  exact numB_eq_of_packed 8 (2 ^ 256) p016
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem shape016 : HasShape (numB 16) (2 * center 16) := by
  rw [← numerator016]
  exact listPoly_shape p016 (2 * center 16)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

def r016 : List ℕ := [36, 374, 2308, 9782, 32484, 88766, 210180, 442206, 847268, 1493942, 2453988, 3779254, 5511380, 7655390, 10209588, 13127518, 16378118, 19883688, 23593542, 27374536, 31130558, 34677736, 37923966, 40701672, 43007286, 44778408, 46153366, 47137160, 47901774, 48408504, 48794574, 48947288, 48947288, 48794574, 48408504, 47901774, 47137160, 46153366, 44778408, 43007286, 40701672, 37923966, 34677736, 31130558, 27374536, 23593542, 19883688, 16378118, 13127518, 10209588, 7655390, 5511380, 3779254, 2453988, 1493942, 847268, 442206, 210180, 88766, 32484, 9782, 2308, 374, 36]

theorem residual016 : listPoly r016 = BinaryResearch.residual 16 := by
  exact residual_eq_of_check 16 p016 r016 numerator016 (by decide +kernel)

theorem residualShape016 : HasShape (BinaryResearch.residual 16) (2 * center 16 - 1) := by
  rw [← residual016]
  exact listPoly_shape r016 (2 * center 16 - 1)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BinaryCertificate.Bases

#print axioms BinaryCertificate.Bases.shape016
#print axioms BinaryCertificate.Bases.residualShape016
