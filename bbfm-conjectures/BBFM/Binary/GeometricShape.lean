import BBFM.Binary.UniformProducts

/-! Unconditional shape of each of the two exact recurrence summands. This
isolates a source sign invariant for the first differences; no LC is inferred. -/
open Polynomial Finset BinaryShape
namespace BinaryResearch

lemma lower_mono_of_central_concavity (f : ℕ → ℤ) (L c : ℕ) (hc : 1 ≤ c)
    (hsymm : f (c-1)=f (c+1))
    (hconcave : ∀ j, L+1 ≤ j → j ≤ c → f (j-1)+f (j+1) ≤ 2*f j)
    (k : ℕ) (hkL : L ≤ k) (hkc : k<c) : f k ≤ f (k+1) := by
  apply Nat.decreasingInduction (n:=c-1)
    (motive:=fun j _ => L ≤ j → f j ≤ f (j+1)) _ _ (by omega) hkL
  · intro j hj ih hjL
    have hn := ih (by omega)
    have hh := hconcave (j+1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at hh
    omega
  · intro hL
    have hh := hconcave c (by omega) le_rfl
    rw [← hsymm] at hh
    rw [Nat.sub_add_cancel hc]
    omega

/-- The actual geometric source term is symmetric unimodal at every even
previous source index at least98, without a residual LC premise. -/
theorem geometric_source_shape (m : ℕ) (hm : 49 ≤ m) :
    HasShape (jump m*numB (2*m)) (2*center (2*m+2)) := by
  have hc := center_window (2*m) (by omega)
  have hq := jumpLength_two_le m
  have hcenter := center_step m
  have hcore := uniform_product_shape (residual (2*m)) (2*center (2*m)-1)
    (2*jumpLength m) (by omega) (strong_even m (by omega)).residualShape
    (residual_coeff_pos_even m (by omega) 0 (by omega))
  have hdegree : (2*center (2*m)-1)+2*jumpLength m-1=2*center (2*m+2) := by omega
  rw [hdegree, mul_comm (residual (2*m))] at hcore
  constructor
  · exact geometric_source_support m
  · exact geometric_source_symmetry m
  · exact coeff_mul_nonneg _ _ (fun k => (jump_coeff_bounded m k).1) (numB_nonneg _)
  · intro k hk
    by_cases hlo : k+1<center (2*m)
    · have heq (j : ℕ) (hj : j<center (2*m)) :
          (jump m*numB (2*m)).coeff j =
            (uniform (2*jumpLength m)*residual (2*m)).coeff j := by
        rw [geometric_source_coeff_decomposition, geometricCorrection_coeff_low _ _ hj, add_zero]
      rw [heq k (by omega), heq (k+1) hlo]
      exact hcore.mono k hk
    · apply lower_mono_of_central_concavity
        (fun j => (jump m*numB (2*m)).coeff j) (center (2*m)-1)
        (center (2*m+2)) (by omega) _ _ k (by omega) (by omega)
      · have hh := geometric_source_symmetry m (center (2*m+2)-1) (by omega)
        rw [show 2*center (2*m+2)-(center (2*m+2)-1)=center (2*m+2)+1 by omega] at hh
        exact hh
      · intro j hjlo hjhi
        have hh := source_geometric_central_concavity m hm j (by omega) (by omega)
        dsimp only [curvature] at hh
        rw [show (j:ℤ)-1=((j-1:ℕ):ℤ) by omega,
          show (j:ℤ)+1=((j+1:ℕ):ℤ) by omega,
          intCoeff_nat, intCoeff_nat, intCoeff_nat] at hh
        omega

/-- Both exact source recurrence terms have nonnegative first differences up to
their common center, and both have full symmetric nonnegative support. -/
theorem source_recurrence_summands_shape (m : ℕ) (hm : 49 ≤ m) :
    HasShape (jump m*numB (2*m)) (2*center (2*m+2)) ∧
      HasShape ((1+X)^(2*m+2)*(numB (m+1)).comp (X^2)) (2*center (2*m+2)) := by
  refine ⟨geometric_source_shape m hm, ?_⟩
  have hh := binomial_comp_square_shape (numB (m+1)) (2*center (m+1)) (2*m+2)
    (by omega) (numB_shape (m+1) (by omega))
  have hc := center_double (m+1)
  rw [show 2*(m+1)=2*m+2 by omega] at hc
  have he : 2*(2*center (m+1))+(2*m+2)=2*center (2*m+2) := by omega
  rwa [he] at hh

#print axioms geometric_source_shape
#print axioms source_recurrence_summands_shape
end BinaryResearch
