import BBFM.Binary.Unimodality.Bases.N002
import BBFM.Binary.Unimodality.Bases.N004
import BBFM.Binary.Unimodality.Bases.N006
import BBFM.Binary.Unimodality.Bases.N008
import BBFM.Binary.Unimodality.Bases.N010
import BBFM.Binary.Unimodality.Bases.N012
import BBFM.Binary.Unimodality.Bases.N014
import BBFM.Binary.Unimodality.Bases.N016
import BBFM.Binary.Unimodality.Bases.N018
import BBFM.Binary.Unimodality.Bases.N020
import BBFM.Binary.Unimodality.Bases.N022
import BBFM.Binary.Unimodality.Bases.N024
import BBFM.Binary.Unimodality.Bases.N026
import BBFM.Binary.Unimodality.Bases.N028
import BBFM.Binary.Unimodality.Bases.N030
import BBFM.Binary.Unimodality.Bases.N032
import BBFM.Binary.Unimodality.Bases.N034
import BBFM.Binary.Unimodality.Bases.N036
import BBFM.Binary.Unimodality.Bases.N038
import BBFM.Binary.Unimodality.Bases.N040
import BBFM.Binary.Unimodality.Bases.N042
import BBFM.Binary.Unimodality.Bases.N044
import BBFM.Binary.Unimodality.Bases.N046
import BBFM.Binary.Unimodality.Bases.N048
import BBFM.Binary.Unimodality.Bases.N050
import BBFM.Binary.Unimodality.Bases.N052
import BBFM.Binary.Unimodality.Bases.N054
import BBFM.Binary.Unimodality.Bases.N056
import BBFM.Binary.Unimodality.Bases.N058
import BBFM.Binary.Unimodality.Bases.N060
import BBFM.Binary.Unimodality.Bases.N062
import BBFM.Binary.Unimodality.Bases.N064
import BBFM.Binary.Unimodality.Bases.N066
import BBFM.Binary.Unimodality.Bases.N068
import BBFM.Binary.Unimodality.Bases.N070
import BBFM.Binary.Unimodality.Bases.N072
import BBFM.Binary.Unimodality.Bases.N074
import BBFM.Binary.Unimodality.Bases.N076
import BBFM.Binary.Unimodality.Bases.N078
import BBFM.Binary.Unimodality.Bases.N080
import BBFM.Binary.Unimodality.Bases.N082
import BBFM.Binary.Unimodality.Bases.N084
import BBFM.Binary.Unimodality.Bases.N086
import BBFM.Binary.Unimodality.Bases.N088
import BBFM.Binary.Unimodality.Bases.N090
import BBFM.Binary.Unimodality.Bases.N092
import BBFM.Binary.Unimodality.Bases.N094
import BBFM.Binary.Unimodality.Bases.N096

open Polynomial BinaryResearch BinaryShape
namespace BinaryCertificate

theorem numB_shape_even_le96 (m : ℕ) (hm : 1 ≤ m) (hm48 : m ≤ 48) :
    HasShape (numB (2 * m)) (2 * center (2 * m)) := by
  interval_cases m
  · exact Bases.shape002
  · exact Bases.shape004
  · exact Bases.shape006
  · exact Bases.shape008
  · exact Bases.shape010
  · exact Bases.shape012
  · exact Bases.shape014
  · exact Bases.shape016
  · exact Bases.shape018
  · exact Bases.shape020
  · exact Bases.shape022
  · exact Bases.shape024
  · exact Bases.shape026
  · exact Bases.shape028
  · exact Bases.shape030
  · exact Bases.shape032
  · exact Bases.shape034
  · exact Bases.shape036
  · exact Bases.shape038
  · exact Bases.shape040
  · exact Bases.shape042
  · exact Bases.shape044
  · exact Bases.shape046
  · exact Bases.shape048
  · exact Bases.shape050
  · exact Bases.shape052
  · exact Bases.shape054
  · exact Bases.shape056
  · exact Bases.shape058
  · exact Bases.shape060
  · exact Bases.shape062
  · exact Bases.shape064
  · exact Bases.shape066
  · exact Bases.shape068
  · exact Bases.shape070
  · exact Bases.shape072
  · exact Bases.shape074
  · exact Bases.shape076
  · exact Bases.shape078
  · exact Bases.shape080
  · exact Bases.shape082
  · exact Bases.shape084
  · exact Bases.shape086
  · exact Bases.shape088
  · exact Bases.shape090
  · exact Bases.shape092
  · exact Bases.shape094
  · exact Bases.shape096

theorem residual_shape_even_le96 (m : ℕ) (hm : 5 ≤ m) (hm48 : m ≤ 48) :
    HasShape (residual (2 * m)) (2 * center (2 * m) - 1) := by
  interval_cases m
  · exact Bases.residualShape010
  · exact Bases.residualShape012
  · exact Bases.residualShape014
  · exact Bases.residualShape016
  · exact Bases.residualShape018
  · exact Bases.residualShape020
  · exact Bases.residualShape022
  · exact Bases.residualShape024
  · exact Bases.residualShape026
  · exact Bases.residualShape028
  · exact Bases.residualShape030
  · exact Bases.residualShape032
  · exact Bases.residualShape034
  · exact Bases.residualShape036
  · exact Bases.residualShape038
  · exact Bases.residualShape040
  · exact Bases.residualShape042
  · exact Bases.residualShape044
  · exact Bases.residualShape046
  · exact Bases.residualShape048
  · exact Bases.residualShape050
  · exact Bases.residualShape052
  · exact Bases.residualShape054
  · exact Bases.residualShape056
  · exact Bases.residualShape058
  · exact Bases.residualShape060
  · exact Bases.residualShape062
  · exact Bases.residualShape064
  · exact Bases.residualShape066
  · exact Bases.residualShape068
  · exact Bases.residualShape070
  · exact Bases.residualShape072
  · exact Bases.residualShape074
  · exact Bases.residualShape076
  · exact Bases.residualShape078
  · exact Bases.residualShape080
  · exact Bases.residualShape082
  · exact Bases.residualShape084
  · exact Bases.residualShape086
  · exact Bases.residualShape088
  · exact Bases.residualShape090
  · exact Bases.residualShape092
  · exact Bases.residualShape094
  · exact Bases.residualShape096

theorem numB_slope_even_le96 (m : ℕ) (hm : 24 ≤ m) (hm48 : m ≤ 48)
    (k : ℕ) (hklo : center (2 * m) - (2 * m + 2) ≤ k) (hkhi : k ≤ center (2 * m)) :
    (3 : ℤ) ^ (2 * m) ≤ (numB (2 * m)).coeff k - (numB (2 * m)).coeff (k - 1) := by
  interval_cases m
  · exact Bases.slopes048 k hklo hkhi
  · exact Bases.slopes050 k hklo hkhi
  · exact Bases.slopes052 k hklo hkhi
  · exact Bases.slopes054 k hklo hkhi
  · exact Bases.slopes056 k hklo hkhi
  · exact Bases.slopes058 k hklo hkhi
  · exact Bases.slopes060 k hklo hkhi
  · exact Bases.slopes062 k hklo hkhi
  · exact Bases.slopes064 k hklo hkhi
  · exact Bases.slopes066 k hklo hkhi
  · exact Bases.slopes068 k hklo hkhi
  · exact Bases.slopes070 k hklo hkhi
  · exact Bases.slopes072 k hklo hkhi
  · exact Bases.slopes074 k hklo hkhi
  · exact Bases.slopes076 k hklo hkhi
  · exact Bases.slopes078 k hklo hkhi
  · exact Bases.slopes080 k hklo hkhi
  · exact Bases.slopes082 k hklo hkhi
  · exact Bases.slopes084 k hklo hkhi
  · exact Bases.slopes086 k hklo hkhi
  · exact Bases.slopes088 k hklo hkhi
  · exact Bases.slopes090 k hklo hkhi
  · exact Bases.slopes092 k hklo hkhi
  · exact Bases.slopes094 k hklo hkhi
  · exact Bases.slopes096 k hklo hkhi

end BinaryCertificate

#print axioms BinaryCertificate.numB_shape_even_le96
#print axioms BinaryCertificate.residual_shape_even_le96
#print axioms BinaryCertificate.numB_slope_even_le96
