import BBFM.Denominator.Bridge.FinalCertificates
namespace BBFMSeptember
open C4Search
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem certificates_17_32 : ∀ n ∈ List.range 33, 17 ≤ n → fastChecks (coefficients n) = true := by
   decide +kernel
 theorem denominator_classification_through_32 (n : ℕ) (hn : n ≤ 32) :
     DenLC n ↔ n ≠ 3 ∧ n ≠ 5 ∧ n ≠ 6 ∧ n ≠ 7 := by
   by_cases h16 : n ≤ 16
   · exact denominator_classification_through_16 n h16
   · have hc := certificates_17_32 n (List.mem_range.mpr (by omega)) (by omega)
     have hl : DenLC n := fun k hk => denominator_logconcave_of_fastChecks n hc k hk
     exact ⟨fun _ => by omega, fun _ => hl⟩
#print axioms denominator_classification_through_32
end BBFMSeptember
