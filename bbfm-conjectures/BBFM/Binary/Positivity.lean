import BBFM.Binary.AllUnimodal

open Polynomial BinaryShape
namespace BinaryResearch

lemma shape_coeff_pos (P : ℤ[X]) (d : ℕ) (h : HasShape P d) (h0 : 0 < P.coeff 0)
    (k : ℕ) (hk : k ≤ d) : 0 < P.coeff k := by
  have hlo (j : ℕ) (hj : 2 * j ≤ d) : 0 < P.coeff j := by
    induction j with
    | zero => exact h0
    | succ j ih => exact lt_of_lt_of_le (ih (by omega)) (h.mono j (by omega))
  by_cases hhalf : 2 * k ≤ d
  · exact hlo k hhalf
  · rw [h.symm k hk]
    exact hlo _ (by omega)

lemma b_pos (n : ℕ) : 0 < b n := by
  unfold b
  exact_mod_cast Fintype.card_pos_iff.mpr (⟨allOnes n⟩ : Nonempty (Part n))

theorem numB_coeff_pos (n : ℕ) (hn : 2 ≤ n) (k : ℕ) (hk : k ≤ 2 * center n) :
    0 < (numB n).coeff k := by
  exact shape_coeff_pos _ _ (numB_shape n hn) (by rw [numB_coeff_zero]; exact b_pos n) k hk

theorem residual_coeff_pos_even (m : ℕ) (hm : 5 ≤ m)
    (k : ℕ) (hk : k ≤ 2 * center (2 * m) - 1) : 0 < (residual (2 * m)).coeff k := by
  have hshape : HasShape (residual (2 * m)) (2 * center (2 * m) - 1) := by
    by_cases hsmall : m ≤ 48
    · exact BinaryCertificate.residual_shape_even_le96 m hm hsmall
    · exact (strong_even m (by omega)).residualShape
  have hc : 0 < center (2 * m) := by
    rw [center_double]
    omega
  exact shape_coeff_pos _ _ hshape (by rw [residual_coeff_zero _ hc]; exact b_pos _) k hk

#print axioms numB_coeff_pos
#print axioms residual_coeff_pos_even
end BinaryResearch
