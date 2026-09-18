import BBFM.Denominator.RelativeDerivatives
import BBFM.Denominator.LinearSupport.SharpTaylor

/-! Variance-relative Taylor bounds for the denominator, using the
SmallRadiusTaylor, LargeRadiusTaylor, and SharpTaylor lemmas. -/

noncomputable section
namespace BBFMRelative
open Finset Complex Real DenominatorResearch
set_option maxHeartbeats 0

lemma den_step_antitone (n i : ℕ) (hi : 1 ≤ i) :
    Nat.log 2 (n/(i+1))+1 ≤ Nat.log 2 (n/i)+1 :=
  den_multiplicity_antitone n i (i+1) hi (by omega)

theorem den_small_radius_relative_taylor (n k : ℕ) (r θ : ℝ)
    (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) (hθ : 0 ≤ θ)
    (hmean : tiltedMean (fun i => Nat.log 2 (n/i)+1) n r = (k : ℝ)) :
    ∃ R : ℂ,
      centeredDenChar n k r θ = Complex.exp
        (-((tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r*θ^2/2 : ℝ) : ℂ)+R) ∧
      ‖R‖ ≤ 64*tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r*θ^3 := by
  let m := fun i => Nat.log 2 (n/i)+1
  let V := tiltedVariance m n r
  have hV : 0 ≤ V := by unfold V tiltedVariance; positivity
  have hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i :=
    fun i hi _ => den_step_antitone n i hi
  have hslit : ∀ u i, 1 ≤ i → i ≤ n → 1+factorPhase r u i ∈ Complex.slitPlane :=
    fun u i hi _ => factorPhase_slitPlane_small r u i hr hrhalf hi
  have hne : ∀ u i, 1 ≤ i → i ≤ n → 1+factorPhase r u i ≠ 0 :=
    fun u i hi hin => Complex.slitPlane_ne_zero (hslit u i hi hin)
  have ht := BBFMSharp.cubic_taylor_bound_sharp
    (logProduct m n r) (logProductDeriv m n r) (logProductDerivTwo m n r)
    (thirdLogSum m n r) θ (384*V) hθ (by positivity)
    (fun u _ => logProduct_hasDerivAt m n r u (hslit u))
    (fun u _ => logProductDeriv_hasDerivAt m n r u (hne u))
    (fun u _ => logProductDerivTwo_hasDerivAt m n r u (hne u))
    (fun u _ => thirdLogSum_relative_small m n r u hr hrhalf hm) θ ⟨hθ,le_rfl⟩
  let R := logProduct m n r θ - logProduct m n r 0 -
    (θ : ℂ)*logProductDeriv m n r 0 - ((θ : ℂ)^2/2)*logProductDerivTwo m n r 0
  refine ⟨R,?_,?_⟩
  · unfold centeredDenChar denChar
    rw [weightedBernoulliChar_eq_exp_logProduct _ n r θ hr hrhalf,← Complex.exp_add]
    congr 1
    dsimp [R]
    rw [logProductDeriv_zero,logProductDerivTwo_zero]
    change logProduct m n r θ - logProduct m n r 0 + -(k : ℂ)*(θ : ℂ)*Complex.I = _
    have hm' : tiltedMean m n r = (k : ℝ) := hmean
    rw [hm']
    push_cast
    ring
  · change ‖R‖ ≤ _ at ht
    change ‖R‖ ≤ 64*V*θ^3
    nlinarith only [ht]

theorem den_large_radius_relative_taylor (n k : ℕ) (r θ : ℝ) (hn : 0 < n)
    (hr : 1/2 < r) (hrone : r ≤ 1) (hθ : 0 ≤ θ)
    (hθL : θ ≤ 1/(4*effectiveScale n r))
    (hmean : tiltedMean (fun i => Nat.log 2 (n/i)+1) n r = (k : ℝ)) :
    ∃ R : ℂ,
      centeredDenChar n k r θ = Complex.exp
        (-((tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r*θ^2/2 : ℝ) : ℂ)+R) ∧
      ‖R‖ ≤ 64*tiltedVariance (fun i => Nat.log 2 (n/i)+1) n r*
        effectiveScale n r*θ^3 := by
  let m := fun i => Nat.log 2 (n/i)+1
  let L := effectiveScale n r
  let V := tiltedVariance m n r
  have hV : 0 ≤ V := by unfold V tiltedVariance; positivity
  have hL : 0 ≤ L := by
    have hh := (effectiveScale_bounds n r hn hr hrone).1
    dsimp [L]
    linarith
  have hm : ∀ i, 1 ≤ i → i ≤ n → m (i+1) ≤ m i :=
    fun i hi _ => den_step_antitone n i hi
  have hlocal (u : ℝ) (hu : u ∈ Set.Icc 0 θ) (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :=
    factorPhase_large_local n i r u hn hr hrone hi hin
      (by rw [abs_of_nonneg hu.1]; exact hu.2.trans hθL)
  have hslit (u : ℝ) (hu : u ∈ Set.Icc 0 θ) :
      ∀ i, 1 ≤ i → i ≤ n → 1+factorPhase r u i ∈ Complex.slitPlane :=
    fun i hi hin => (hlocal u hu i hi hin).1
  have hne (u : ℝ) (hu : u ∈ Set.Icc 0 θ) :
      ∀ i, 1 ≤ i → i ≤ n → 1+factorPhase r u i ≠ 0 :=
    fun i hi hin => Complex.slitPlane_ne_zero (hslit u hu i hi hin)
  have ht := BBFMSharp.cubic_taylor_bound_sharp
    (logProduct m n r) (logProductDeriv m n r) (logProductDerivTwo m n r)
    (thirdLogSum m n r) θ (384*L*V) hθ (by positivity)
    (fun u hu => logProduct_hasDerivAt m n r u (hslit u hu))
    (fun u hu => logProductDeriv_hasDerivAt m n r u (hne u hu))
    (fun u hu => logProductDerivTwo_hasDerivAt m n r u (hne u hu))
    (fun u hu => thirdLogSum_relative_large m n r u hn hr hrone hm
      (by rw [abs_of_nonneg hu.1]; exact hu.2.trans hθL)) θ ⟨hθ,le_rfl⟩
  let R := logProduct m n r θ - logProduct m n r 0 -
    (θ : ℂ)*logProductDeriv m n r 0 - ((θ : ℂ)^2/2)*logProductDerivTwo m n r 0
  refine ⟨R,?_,?_⟩
  · unfold centeredDenChar denChar
    rw [weightedBernoulliChar_eq_exp_logProduct_local _ n r θ (by linarith) (hne θ ⟨hθ,le_rfl⟩),
      ← Complex.exp_add]
    congr 1
    dsimp [R]
    rw [logProductDeriv_zero,logProductDerivTwo_zero]
    change logProduct m n r θ - logProduct m n r 0 + -(k : ℂ)*(θ : ℂ)*Complex.I = _
    have hm' : tiltedMean m n r = (k : ℝ) := hmean
    rw [hm']
    push_cast
    ring
  · change ‖R‖ ≤ _ at ht
    change ‖R‖ ≤ 64*V*L*θ^3
    nlinarith only [ht]

#print axioms den_small_radius_relative_taylor
#print axioms den_large_radius_relative_taylor
end BBFMRelative
