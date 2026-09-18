import BBFM.Binary.LogConcavity.PowerConcavity
import BBFM.Binary.PowerConcavity

open BinaryResearch
namespace BinaryPowerClosure

def IntervalPositive (f : ℤ → ℤ) (lo hi : ℤ) : Prop :=
  lo ≤ hi ∧ (∀ z, 0 ≤ f z) ∧ (∀ z, 0 < f z ↔ lo ≤ z ∧ z ≤ hi)

def SequencePC (p : ℤ) (f : ℤ → ℤ) : Prop :=
  ∀ z, PowerConcaveAt p (f (z - 1)) (f z) (f (z + 1))

def bernoulli (f : ℤ → ℤ) (z : ℤ) : ℤ := f (z - 1) + f z

theorem int_bernoulli_pos (p a b c d : ℤ) (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (hd : 0 ≤ d)
    (h1 : PowerConcaveAt p a b c) (h2 : PowerConcaveAt p b c d) :
    PowerConcaveAt (p + 1) (a + b) (b + c) (c + d) := by
  unfold PowerConcaveAt at *
  have h1' : BinaryPowerConcavity.PC (p : ℝ) a b c :=
    (BinaryPowerConcavity.pc_iff_turan _ _ _ _).mpr (by exact_mod_cast h1)
  have h2' : BinaryPowerConcavity.PC (p : ℝ) b c d :=
    (BinaryPowerConcavity.pc_iff_turan _ _ _ _).mpr (by exact_mod_cast h2)
  have h := BinaryPowerConcavity.bernoulli_pos (p : ℝ) a b c d
    (by exact_mod_cast hp) (by exact_mod_cast ha) (by exact_mod_cast hb)
    (by exact_mod_cast hc) (by exact_mod_cast hd) h1' h2'
  have h' := (BinaryPowerConcavity.pc_iff_turan _ _ _ _).mp h
  exact_mod_cast h'

lemma zero_outside {f : ℤ → ℤ} {lo hi z : ℤ}
    (h : IntervalPositive f lo hi) (hz : z < lo ∨ hi < z) : f z = 0 := by
  have hn := h.2.1 z
  have hp := h.2.2 z
  omega

theorem bernoulli_interval {f : ℤ → ℤ} {lo hi : ℤ}
    (h : IntervalPositive f lo hi) : IntervalPositive (bernoulli f) lo (hi + 1) := by
  have hlohi := h.1
  refine ⟨by omega, ?_, ?_⟩
  · intro z
    exact add_nonneg (h.2.1 _) (h.2.1 _)
  · intro z
    have ha := h.2.1 (z - 1)
    have hb := h.2.1 z
    have hpa := h.2.2 (z - 1)
    have hpb := h.2.2 z
    change 0 < f (z - 1) + f z ↔ lo ≤ z ∧ z ≤ hi + 1
    omega

/-- Quantitative power-concavity is preserved globally, including both finite
support boundaries, by convolution with the Bernoulli coefficient sequence. -/
theorem bernoulli_pc {f : ℤ → ℤ} {lo hi p : ℤ} (hp : 1 ≤ p)
    (hs : IntervalPositive f lo hi) (h : SequencePC p f) :
    SequencePC (p + 1) (bernoulli f) := by
  intro z
  have h1 := h (z - 1)
  have h2 := h z
  have hz1 : z - 1 + 1 = z := by omega
  have hz2 : z + 1 - 1 = z := by omega
  rw [hz1] at h1
  simp only [bernoulli, hz2]
  by_cases hb : 0 < f (z - 1)
  · by_cases hc : 0 < f z
    · exact int_bernoulli_pos p _ _ _ _ hp (hs.2.1 _) hb hc (hs.2.1 _) h1 h2
    · have hc0 : f z = 0 := by have := hs.2.1 z; omega
      have hb' := (hs.2.2 (z - 1)).mp hb
      have hd0 : f (z + 1) = 0 := zero_outside hs (Or.inr (by
        have := hs.2.2 z
        omega))
      unfold PowerConcaveAt at h1 ⊢
      rw [hc0] at h1
      rw [hc0, hd0]
      nlinarith
  · have hb0 : f (z - 1) = 0 := by have := hs.2.1 (z - 1); omega
    by_cases hc : 0 < f z
    · have hc' := (hs.2.2 z).mp hc
      have ha0 : f (z - 1 - 1) = 0 := zero_outside hs (Or.inl (by
        have := hs.2.2 (z - 1)
        omega))
      unfold PowerConcaveAt at h2 ⊢
      rw [hb0] at h2
      rw [ha0, hb0]
      nlinarith
    · have hc0 : f z = 0 := by have := hs.2.1 z; omega
      unfold PowerConcaveAt
      rw [hb0, hc0]
      by_cases hz : z < lo
      · have ha0 : f (z - 1 - 1) = 0 := zero_outside hs (Or.inl (by omega))
        simp [ha0]
      · have hd0 : f (z + 1) = 0 := zero_outside hs (Or.inr (by
          have := hs.2.2 z
          omega))
        simp [hd0]

#print axioms bernoulli_interval
#print axioms bernoulli_pc
end BinaryPowerClosure
