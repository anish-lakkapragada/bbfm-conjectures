import BBFM.Binary.LogConcavity.UniformPowerShape

open Finset BinaryPowerConcavity
namespace BinaryUniformPower

lemma pc_decrease_right (p a b c C : ℝ) (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ C) (hpc : PC p a b C) : PC p a b c := by
  have hh := mul_nonneg (show 0 ≤ C - c by linarith)
    (show 0 ≤ b + (p - 1) * a by positivity)
  unfold PC at *
  nlinarith only [hh, hpc]

/-- Lower-half quantitative concavity of every uniform moving sum. -/
theorem window_lower_powerConcave (p : ℝ) (f : ℤ → ℝ) (D L k : ℕ)
    (hp : 1 ≤ p) (hL : 1 ≤ L) (hf : SymmetricPositive f D)
    (hpc : ∀ z : ℤ, PC p (f (z - 1)) (f z) (f (z + 1)))
    (hk : 2 * (k : ℤ) ≤ (D : ℤ) + L - 1) :
    PC (p + 1) (window f L ((k : ℤ) - 1)) (window f L k)
      (window f L ((k : ℤ) + 1)) := by
  let W := window f L k
  have hW : 0 ≤ W := window_nonneg f L hf.nonneg k
  have hleft := window_difference f L ((k : ℤ) - 1)
  have he : (k : ℤ) - 1 + 1 = k := by omega
  rw [he] at hleft
  have hright := window_difference f L k
  by_cases hconc : window f L ((k : ℤ) - 1) + window f L ((k : ℤ) + 1) ≤ 2 * W
  · exact pc_of_nonnegative_concave (p + 1) _ _ _ (by linarith)
      (window_nonneg f L hf.nonneg _) hW (window_nonneg f L hf.nonneg _) hconc
  have hinleft := hf.mono ((k : ℤ) - L) (by omega)
  have heleft : (k : ℤ) - L + 1 = (k : ℤ) + 1 - L := by omega
  rw [heleft] at hinleft
  have hconv : f ((k : ℤ) + 1 - L) - f ((k : ℤ) - L) < f ((k : ℤ) + 1) - f k := by
    dsimp only [W] at hconc
    linarith
  have hlast : f k < f ((k : ℤ) + 1) := by linarith
  have hkD : k + 1 ≤ D := by
    by_contra hn
    have hz := hf.zero_right ((k : ℤ) + 1) (by omega)
    have hn := hf.nonneg k
    linarith
  let F : ℕ → ℝ := fun i => f ((i : ℤ) - 1)
  have hFpc : ∀ i ≤ k, PC p (F i) (F (i + 1)) (F (i + 2)) := by
    intro i hi
    convert hpc i using 1 <;> dsimp [F] <;> congr 1 <;> omega
  have hFpos : ∀ i ≤ k, 0 < F (i + 1) := by
    intro i hi
    apply hf.positive
    · omega
    · omega
  have hFend : F (k + 1) < F (k + 2) := by
    convert hlast using 1 <;> dsimp [F] <;> congr 1 <;> omega
  have hinc := increasing_prefix_of_final_increase p F k hp hFpos hFpc hFend
  by_cases hlong : k + 1 ≤ L
  · have heW : W = ∑ i ∈ range (k + 1), F (i + 1) := by
      rw [show W = window f L k by rfl, window_eq_prefix f L k hlong hf.zero_left]
      apply sum_congr rfl
      intro i hi
      dsimp [F]
      congr 1
      omega
    have hcum := increasing_prefix_powerConcave p F (k + 1) hp
      (hf.zero_left _ (by norm_num)) (fun i _ => hf.nonneg _) hinc
      (fun i hi => hFpc i (by omega))
    dsimp only at hcum
    rw [← heW] at hcum
    have hFk : F (k + 1) = f k := by dsimp [F]; congr 1; omega
    have hFk1 : F (k + 1 + 1) = f ((k : ℤ) + 1) := by dsimp [F]; congr 1; omega
    rw [hFk, hFk1] at hcum
    have hu : f ((k : ℤ) - L) = 0 := hf.zero_left _ (by omega)
    rw [hu] at hleft
    have ha : window f L ((k : ℤ) - 1) = W - f k := by dsimp [W]; linarith
    rw [← ha] at hcum
    have hcbound : window f L ((k : ℤ) + 1) ≤ W + f ((k : ℤ) + 1) := by
      have htail := hf.nonneg ((k : ℤ) + 1 - L)
      dsimp [W]
      linarith
    exact pc_decrease_right (p + 1) _ _ _ _ (by linarith)
      (window_nonneg f L hf.nonneg _) hW hcbound hcum
  · let Fw : ℕ → ℝ := fun i => f ((k : ℤ) - L + i)
    have hFwinc : ∀ i ≤ L, Fw i < Fw (i + 1) := by
      intro i hi
      have hj : (k : ℤ) - L + i + 1 ≥ 0 := by omega
      let j : ℕ := ((k : ℤ) - L + i + 1).toNat
      have hjcast : (j : ℤ) = (k : ℤ) - L + i + 1 := by dsimp [j]; omega
      have hh := hinc j (by omega)
      convert hh using 1 <;> dsimp [Fw, F] <;> congr 1 <;> omega
    have hFwpc : ∀ i < L, PC p (Fw i) (Fw (i + 1)) (Fw (i + 2)) := by
      intro i hi
      convert hpc ((k : ℤ) - L + i + 1) using 1 <;> dsimp [Fw] <;> congr 1 <;> omega
    have hFw0 : Fw 0 = f ((k : ℤ) - L) := by simp [Fw]
    have hFw1 : Fw 1 = f ((k : ℤ) + 1 - L) := by dsimp [Fw] <;> congr 1 <;> omega
    have hFwL : Fw L = f k := by dsimp [Fw]; congr 1; omega
    have hFwL1 : Fw (L + 1) = f ((k : ℤ) + 1) := by dsimp [Fw]; congr 1; omega
    have heW : W = ∑ i ∈ range L, Fw (i + 1) := by
      rw [show W = window f L k by rfl, window_reverse_sum]
      apply sum_congr rfl
      intro i hi
      rfl
    have hwin := increasing_window_powerConcave p Fw L hp (fun i _ => hf.nonneg _) hFwinc hFwpc
      (by rw [hFw0, hFw1, hFwL, hFwL1]; exact hconv)
    dsimp only at hwin
    rw [← heW, hFwL, hFw0, hFwL1, hFw1] at hwin
    have ha : W - f k + f ((k : ℤ) - L) = window f L ((k : ℤ) - 1) := by dsimp [W]; linarith
    have hc : W + f ((k : ℤ) + 1) - f ((k : ℤ) + 1 - L) = window f L ((k : ℤ) + 1) := by dsimp [W]; linarith
    rw [ha, hc] at hwin
    exact hwin

lemma pc_reverse (p a b c : ℝ) : PC p a b c ↔ PC p c b a := by
  unfold PC
  constructor <;> intro h <;> nlinarith

/-- Uniform convolution costs one unit of quantitative power-concavity,
independently of the interval length. All zero-extended indices are covered. -/
theorem window_powerConcave (p : ℝ) (f : ℤ → ℝ) (D L : ℕ)
    (hp : 1 ≤ p) (hL : 1 ≤ L) (hf : SymmetricPositive f D)
    (hpc : ∀ z : ℤ, PC p (f (z - 1)) (f z) (f (z + 1))) :
    ∀ z : ℤ, PC (p + 1) (window f L (z - 1)) (window f L z) (window f L (z + 1)) := by
  have hneg (z : ℤ) (hz : z < 0) :
      PC (p + 1) (window f L (z - 1)) (window f L z) (window f L (z + 1)) := by
    rw [window_zero_left f L hf.zero_left _ (by omega), window_zero_left f L hf.zero_left z hz]
    simp [PC]
  have hlow (z : ℤ) (hz : 2 * z ≤ (D : ℤ) + L - 1) :
      PC (p + 1) (window f L (z - 1)) (window f L z) (window f L (z + 1)) := by
    by_cases hz0 : z < 0
    · exact hneg z hz0
    · have he : (z.toNat : ℤ) = z := by omega
      simpa only [he] using window_lower_powerConcave p f D L z.toNat hp hL hf hpc (by omega)
  have hr := window_reflection f D L hf.reflection
  intro z
  by_cases hz : 2 * z ≤ (D : ℤ) + L - 1
  · exact hlow z hz
  · have hh := hlow ((D : ℤ) + L - 1 - z) (by omega)
    have he₁ : (D : ℤ) + L - 1 - z - 1 = (D : ℤ) + L - 1 - (z + 1) := by omega
    have he₂ : (D : ℤ) + L - 1 - z + 1 = (D : ℤ) + L - 1 - (z - 1) := by omega
    rw [he₁, he₂, hr, hr, hr] at hh
    exact (pc_reverse _ _ _ _).mpr hh

end BinaryUniformPower

#print axioms BinaryUniformPower.window_lower_powerConcave
#print axioms BinaryUniformPower.window_powerConcave
