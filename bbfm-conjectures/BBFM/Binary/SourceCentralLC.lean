import BBFM.Binary.GeometricShape

/-! A partial source LC theorem: the two coefficients immediately beside the
central coefficient satisfy LC for every even source index at least100. This
uses no source LC or PC hypothesis and does not settle the full coefficient range. -/
open Polynomial Finset BinaryShape
namespace BinaryResearch
set_option maxHeartbeats 1000000

lemma binomial_sq_coeff (Q : ℤ[X]) (k : ℕ) (hk : 2 ≤ k) :
    (((1+X)^2 : ℤ[X])*Q).coeff k =
      Q.coeff k + 2*Q.coeff (k-1) + Q.coeff (k-2) := by
  have he : ((1+X)^2 : ℤ[X])*Q = Q + C 2*(X^1*Q) + X^2*Q := by
    norm_num
    ring
  rw [he, coeff_add, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul',
    if_pos (by omega : 1 ≤ k), if_pos hk]

/-- Two Bernoulli factors turn symmetric unimodality into concavity at the
coefficient immediately below the new center. -/
lemma binomial_sq_lower_central_concavity (Q : ℤ[X]) (c : ℕ) (hc : 3 ≤ c)
    (hQ : HasShape Q (2*c)) :
    0 ≤ curvature (((1+X)^2 : ℤ[X])*Q) c := by
  have hs := hQ.symm (c-1) (by omega)
  rw [show 2*c-(c-1)=c+1 by omega] at hs
  have hm1 := hQ.mono (c-3) (by omega)
  have hm2 := hQ.mono (c-2) (by omega)
  rw [show c-3+1=c-2 by omega] at hm1
  rw [show c-2+1=c-1 by omega] at hm2
  dsimp only [curvature]
  rw [show (c:ℤ)-1=((c-1:ℕ):ℤ) by omega,
    show (c:ℤ)+1=((c+1:ℕ):ℤ) by omega,
    intCoeff_nat, intCoeff_nat, intCoeff_nat]
  rw [binomial_sq_coeff _ _ (by omega : 2 ≤ c),
    binomial_sq_coeff _ _ (by omega : 2 ≤ c-1),
    binomial_sq_coeff _ _ (by omega : 2 ≤ c+1)]
  rw [show c-1-1=c-2 by omega, show c-1-2=c-3 by omega,
    show c+1-1=c by omega, show c+1-2=c-1 by omega, ← hs]
  omega

/-- The actual smoothing summand is concave immediately below its center. -/
theorem source_smoothing_lower_central_concavity (m : ℕ) (hm : 3 ≤ m) :
    0 ≤ curvature ((1+X)^(2*m+2)*(numB (m+1)).comp (X^2))
      ((center (2*m+2)-1:ℕ):ℤ) := by
  have hc := center_double (m+1)
  rw [show 2*(m+1)=2*m+2 by omega] at hc
  have hsh := binomial_comp_square_shape (numB (m+1)) (2*center (m+1))
    (2*m) (by omega) (numB_shape (m+1) (by omega))
  have hd : 2*(2*center (m+1))+2*m=2*(center (2*m+2)-1) := by omega
  rw [hd] at hsh
  have he : (1+X)^(2*m+2)*(numB (m+1)).comp (X^2) =
      ((1+X)^2 : ℤ[X])*((1+X)^(2*m)*(numB (m+1)).comp (X^2)) := by
    rw [pow_add]
    ring
  rw [he]
  exact binomial_sq_lower_central_concavity _ _ (by omega) hsh

/-- Unconditional concavity at the source coefficient immediately below center.
This is a partial coefficient-range result, not revised BBFM C7. -/
theorem source_lower_central_concavity (m : ℕ) (hm : 49 ≤ m) :
    0 ≤ curvature (numB (2*m+2)) ((center (2*m+2)-1:ℕ):ℤ) := by
  have hstep := center_step m
  have hq := jumpLength_two_le m
  have hc := center_window (2*m) (by omega)
  have hg := source_geometric_central_concavity m hm (center (2*m+2)-1)
    (by omega) (by omega)
  have hb := source_smoothing_lower_central_concavity m (by omega)
  rw [numB_even_recurrence, curvature_add]
  exact add_nonneg hg hb

/-- Actual source Turan inequality immediately below center for every even n≥100. -/
theorem source_lower_central_logconcavity (m : ℕ) (hm : 49 ≤ m) :
    (numB (2*m+2)).coeff (center (2*m+2)-2) *
      (numB (2*m+2)).coeff (center (2*m+2)) ≤
        ((numB (2*m+2)).coeff (center (2*m+2)-1))^2 := by
  have hc := center_window (2*m+2) (by omega)
  have hh := source_lower_central_concavity m hm
  dsimp only [curvature] at hh
  rw [show ((center (2*m+2)-1:ℕ):ℤ)-1=((center (2*m+2)-2:ℕ):ℤ) by omega,
    show ((center (2*m+2)-1:ℕ):ℤ)+1=(center (2*m+2):ℤ) by omega,
    intCoeff_nat, intCoeff_nat, intCoeff_nat] at hh
  exact concavity_implies_turan _ _ _ (numB_nonneg _ _) (numB_nonneg _ _) (by omega)

/-- A partial all-n theorem at the two coefficients immediately beside center.
The interior range away from these two indices remains an open LC obligation. -/
theorem source_adjacent_to_center_logconcavity (n : ℕ) (hn : 100 ≤ n) :
    (numB n).coeff (center n-2)*(numB n).coeff (center n) ≤
      ((numB n).coeff (center n-1))^2 ∧
    (numB n).coeff (center n)*(numB n).coeff (center n+2) ≤
      ((numB n).coeff (center n+1))^2 := by
  have hlo : (numB n).coeff (center n-2)*(numB n).coeff (center n) ≤
      ((numB n).coeff (center n-1))^2 := by
    rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
    · have hh := source_lower_central_logconcavity (m-1) (by omega)
      have he : 2*(m-1)+2=n := by omega
      rw [he] at hh
      exact hh
    · have hh := source_lower_central_logconcavity (m-1) (by omega)
      have he : 2*(m-1)+2=2*m := by omega
      rw [he] at hh
      rw [hm, numB_odd, center_odd]
      exact hh
  refine ⟨hlo, ?_⟩
  have hc := center_window n (by omega)
  have h := numB_shape n (by omega)
  have h1 := h.symm (center n-1) (by omega)
  have h2 := h.symm (center n-2) (by omega)
  rw [show 2*center n-(center n-1)=center n+1 by omega] at h1
  rw [show 2*center n-(center n-2)=center n+2 by omega] at h2
  rw [← h1, ← h2, mul_comm]
  exact hlo

#print axioms binomial_sq_lower_central_concavity
#print axioms source_lower_central_concavity
#print axioms source_lower_central_logconcavity
#print axioms source_adjacent_to_center_logconcavity
end BinaryResearch
