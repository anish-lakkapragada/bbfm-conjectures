import BBFM.Binary.PrefixBudget
import BBFM.Binary.SourceEdge

open Polynomial Finset
namespace BinaryResearch

/-- An integral quantitative strengthening of a Turan inequality. -/
def PowerConcaveAt (p a b c : ℤ) : Prop :=
  (b - a) * (c - b) ≤ p * (b ^ 2 - a * c)

/-- Zero-extended coefficient version; index zero includes a first-ratio bound. -/
def PowerConcave (p : ℤ) (P : ℤ[X]) : Prop :=
  ∀ z : ℤ, PowerConcaveAt p (BinaryShape.intCoeff P (z - 1))
    (BinaryShape.intCoeff P z) (BinaryShape.intCoeff P (z + 1))

lemma powerConcaveAt_iff (p a b c : ℤ) :
    PowerConcaveAt p a b c ↔
      c * (b + (p - 1) * a) ≤ b * ((p + 1) * b - a) := by
  unfold PowerConcaveAt
  constructor <;> intro h <;> nlinarith

lemma power_defect_identity (p a b c : ℤ) :
    p * (b ^ 2 - a * c) - (b - a) * (c - b) =
      p * b * (2 * b - a - c) + (p - 1) * (b - a) * (c - b) := by ring

/-- Positivity excludes the isolated-zero degeneracy at parameter one. -/
theorem powerConcaveAt_logconcave (p a b c : ℤ) (hp : 1 ≤ p)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c)
    (h : PowerConcaveAt p a b c) : a * c ≤ b ^ 2 := by
  unfold PowerConcaveAt at h
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · have hprod := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc)
      have hp0 : 0 < p := by omega
      nlinarith
    · have h1 := mul_nonneg (sub_nonneg.mpr hab) (le_of_lt hb)
      have h2 := mul_nonneg ha (sub_nonneg.mpr (by omega : c ≤ b))
      nlinarith
  · by_cases hcb : c ≤ b
    · have hprod := mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (by omega : b ≤ a)) (sub_nonpos.mpr hcb)
      have hp0 : 0 < p := by omega
      nlinarith
    · have hsum : 0 < a + c - 2 * b := by omega
      have hpos := mul_pos hb hsum
      have hneg : b ^ 2 - a * c < 0 := by
        have hmul := mul_pos (show 0 < a - b by omega) (show 0 < c by omega)
        nlinarith [mul_pos hb (show 0 < c - b by omega)]
      have hscale := mul_nonpos_of_nonneg_of_nonpos
        (show 0 ≤ p - 1 by omega) (le_of_lt hneg)
      nlinarith

lemma powerConcaveAt_mono (p q a b c : ℤ) (hpq : p ≤ q)
    (hlc : a * c ≤ b ^ 2) (h : PowerConcaveAt p a b c) :
    PowerConcaveAt q a b c := by
  unfold PowerConcaveAt at h ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr hpq) (sub_nonneg.mpr hlc)]

theorem numB_first_ratio_bound (n : ℕ) :
    (numB n).coeff 1 ≤ (n : ℤ) * (numB n).coeff 0 := by
  rw [numB_coeff_zero]
  have h := first_balance n
  have hs : 0 ≤ ∑ j ∈ range n, b j := sum_nonneg fun j _ => b_nonneg j
  omega

/-- The boundary requirement for the proposed source dimension `n - 1`
already holds unconditionally for the exact source numerator. -/
theorem numB_power_boundary (n : ℕ) :
    PowerConcaveAt ((n : ℤ) - 1) 0 ((numB n).coeff 0) ((numB n).coeff 1) := by
  have h := numB_first_ratio_bound n
  have h0 := numB_nonneg n 0
  unfold PowerConcaveAt
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr h)]

/-- Unproved strengthening under investigation. No assertion of this proposition
is used by any completed theorem. -/
def SourcePowerConcavity : Prop :=
  ∀ n : ℕ, 6 ≤ n → PowerConcave ((n : ℤ) - 1) (numB n)

#print axioms powerConcaveAt_logconcave
#print axioms numB_first_ratio_bound
#print axioms numB_power_boundary
end BinaryResearch
