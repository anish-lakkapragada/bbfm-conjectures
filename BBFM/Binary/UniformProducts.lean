import BBFM.Binary.RefinementSmoothing
import BBFM.Binary.LogConcavity.UniformPowerPolynomial

open Polynomial Finset BinaryShape BinaryUniformPower
namespace BinaryResearch

theorem uniform_product_shape (P : ℤ[X]) (d L : ℕ) (hL : 1 ≤ L)
    (h : HasShape P d) (hzero : 0 < P.coeff 0) :
    HasShape (P * uniform L) (d + L - 1) := by
  let f : ℤ → ℝ := fun z => (intCoeff P z : ℝ)
  have hf : SymmetricPositive f d := shape_realification P d h hzero
  have he (z : ℤ) : window f L z = (intCoeff (P * uniform L) z : ℝ) := by
    rw [intCoeff_mul_uniform]
    simp [window, f]
  constructor
  · intro k hk
    have hz : window f L k = 0 := by
      apply sum_eq_zero
      intro j hj
      exact hf.zero_right _ (by have hmem := mem_range.mp hj; omega)
    rw [he, intCoeff_nat] at hz
    exact_mod_cast hz
  · intro k hk
    have hr := window_reflection f d L hf.reflection (k : ℤ)
    have hi : (d : ℤ) + L - 1 - k = ((d + L - 1 - k : ℕ) : ℤ) := by omega
    rw [hi, he, he, intCoeff_nat, intCoeff_nat] at hr
    exact_mod_cast hr.symm
  · intro k
    have hn := window_nonneg f L hf.nonneg (k : ℤ)
    rw [he, intCoeff_nat] at hn
    exact_mod_cast hn
  · intro k hk
    have hm := window_lower_increasing f d L hf ((k + 1 : ℕ) : ℤ) (by omega)
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega,
      he, he, intCoeff_nat, intCoeff_nat] at hm
    exact_mod_cast hm

/-- Each positive-length ordinary interval factor costs one PC parameter.
The degree witness is internal; the polynomial in the conclusion is exact. -/
theorem uniform_factors_powerConcave (P : ℤ[X]) (d : ℕ) (p : ℤ)
    (hp : 1 ≤ p) (h : HasShape P d) (hzero : 0 < P.coeff 0) (hpc : PowerConcave p P)
    (s : Finset ℕ) (L : ℕ → ℕ) (hL : ∀ i ∈ s, 1 ≤ L i) :
    ∃ D : ℕ, HasShape (P * ∏ i ∈ s, uniform (L i)) D ∧
      0 < (P * ∏ i ∈ s, uniform (L i)).coeff 0 ∧
      PowerConcave (p + (s.card : ℤ)) (P * ∏ i ∈ s, uniform (L i)) := by
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨d, by simpa using h, by simpa using hzero, by simpa using hpc⟩
  | @insert i s hi ih =>
      obtain ⟨D, hs, hz, hc⟩ := ih (fun j hj => hL j (mem_insert_of_mem hj))
      have hiL := hL i (mem_insert_self i s)
      let Q : ℤ[X] := P * ∏ j ∈ s, uniform (L j)
      have hshape := uniform_product_shape Q D (L i) hiL hs hz
      have hzero' : 0 < (Q * uniform (L i)).coeff 0 := by
        rw [mul_coeff_zero, uniform_coeff, if_pos (by omega : 0 < L i), mul_one]
        exact hz
      have hpc' := uniform_preserves_powerConcave Q D (L i) (p + (s.card : ℤ))
        (by omega) hiL hs hz hc
      have he : P * ∏ j ∈ insert i s, uniform (L j) = Q * uniform (L i) := by
        rw [prod_insert hi]
        dsimp only [Q]
        ring
      rw [he]
      refine ⟨D + L i - 1, hshape, hzero', ?_⟩
      simpa only [card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_assoc] using hpc'

#print axioms uniform_product_shape
#print axioms uniform_factors_powerConcave
end BinaryResearch
