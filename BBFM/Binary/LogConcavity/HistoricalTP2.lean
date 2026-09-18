import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Int.Interval
import Mathlib.Tactic


-- Source component: TotalPositivity

noncomputable section
namespace BBFMCombinatorics
open Finset

/-- The order-two Cauchy--Binet identity, with an ordered double sum. -/
theorem cauchyBinet_two {ι : Type*} (s : Finset ι) (f g h l : ι → ℝ) :
    (∑ i ∈ s, ∑ j ∈ s,
      (f i * g j - f j * g i) * (h i * l j - h j * l i)) =
    2 * ((∑ i ∈ s, f i * h i) * (∑ i ∈ s, g i * l i) -
      (∑ i ∈ s, f i * l i) * (∑ i ∈ s, g i * h i)) := by
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s,
        ((f i * h i) * (g j * l j) - (f i * l i) * (g j * h j) -
        (g i * h i) * (f j * l j) + (g i * l i) * (f j * h j)) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by
      simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul]
      ring

/-- Two families of ordered minors with matching signs give a nonnegative
minor after contraction. This requires no positivity of the entries. -/
theorem ordered_sum_minor_nonneg {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f g h l : ι → ℝ)
    (hfg : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → 0 ≤ f i * g j - f j * g i)
    (hhl : ∀ i ∈ s, ∀ j ∈ s, i ≤ j → 0 ≤ h i * l j - h j * l i) :
    (∑ i ∈ s, f i * l i) * (∑ i ∈ s, g i * h i) ≤
      (∑ i ∈ s, f i * h i) * (∑ i ∈ s, g i * l i) := by
  have hn : 0 ≤ ∑ i ∈ s, ∑ j ∈ s,
      (f i * g j - f j * g i) * (h i * l j - h j * l i) := by
    apply sum_nonneg
    intro i hi
    apply sum_nonneg
    intro j hj
    rcases le_total i j with hij | hji
    · exact mul_nonneg (hfg i hi j hj hij) (hhl i hi j hj hij)
    · apply mul_nonneg_of_nonpos_of_nonpos <;>
        linarith [hfg j hj i hi hji, hhl j hj i hi hji]
  rw [cauchyBinet_two] at hn
  linarith

/-- Toeplitz total positivity of order two, including zero extension. -/
def TP2 (a : ℤ → ℝ) : Prop :=
  ∀ r₁ r₂ c₁ c₂ : ℤ, r₁ ≤ r₂ → c₁ ≤ c₂ →
    a (c₂ - r₁) * a (c₁ - r₂) ≤ a (c₁ - r₁) * a (c₂ - r₂)

/-- Discrete convolution; finite support will justify the uses below. -/
def conv (a b : ℤ → ℝ) (k : ℤ) : ℝ := ∑' t : ℤ, a t * b (k - t)

lemma conv_shift (a b : ℤ → ℝ) (r c : ℤ) :
    conv a b (c - r) = ∑' t : ℤ, a (t - r) * b (c - t) := by
  have h := (Equiv.addRight r).tsum_eq (fun t : ℤ => a (t - r) * b (c - t))
  simpa [conv, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/-- Convolution preserves TP2 when the first factor has finite support. -/
theorem TP2_conv {a b : ℤ → ℝ} (ha : TP2 a) (hb : TP2 b)
    (hfin : (Function.support a).Finite) : TP2 (conv a b) := by
  classical
  intro r₁ r₂ c₁ c₂ hr hc
  let s : Finset ℤ := hfin.toFinset.image (fun t => t + r₁) ∪
    hfin.toFinset.image (fun t => t + r₂)
  have hsum (r c : ℤ) (hr' : r = r₁ ∨ r = r₂) :
      conv a b (c - r) = ∑ t ∈ s, a (t - r) * b (c - t) := by
    rw [conv_shift]
    apply tsum_eq_sum
    intro t ht
    have hz : a (t - r) = 0 := by
      by_contra hn
      have hm : t - r ∈ hfin.toFinset := by simpa using hn
      have him : t ∈ hfin.toFinset.image (fun u => u + r) := by
        exact mem_image.mpr ⟨t-r, hm, by omega⟩
      apply ht
      rcases hr' with rfl | rfl
      · exact mem_union_left _ him
      · exact mem_union_right _ him
    simp [hz]
  rw [hsum r₁ c₂ (Or.inl rfl), hsum r₂ c₁ (Or.inr rfl),
    hsum r₁ c₁ (Or.inl rfl), hsum r₂ c₂ (Or.inr rfl)]
  apply ordered_sum_minor_nonneg s
    (fun t => a (t-r₁)) (fun t => a (t-r₂))
    (fun t => b (c₁-t)) (fun t => b (c₂-t))
  · intro i hi j hj hij
    exact sub_nonneg.mpr (ha r₁ r₂ i j hr hij)
  · intro i hi j hj hij
    simpa only [mul_comm] using sub_nonneg.mpr (hb i j c₁ c₂ hij hc)

/-- In particular, every adjacent coefficient comparison follows from TP2. -/
theorem TP2_logConcave {a : ℤ → ℝ} (ha : TP2 a) (k : ℤ) :
    a (k-1) * a (k+1) ≤ a k ^ 2 := by
  have h := ha 0 1 k (k+1) (by omega) (by omega)
  simpa [pow_two, mul_comm] using h

/-- The uniform distribution on any integer interval has TP2. -/
theorem interval_TP2 (L U : ℤ) :
    TP2 (fun k => if L ≤ k ∧ k ≤ U then (1 : ℝ) else 0) := by
  intro r₁ r₂ c₁ c₂ hr hc
  dsimp only
  split_ifs <;> norm_num at * <;> omega

end BBFMCombinatorics

-- Source component: IntervalProducts

noncomputable section
namespace BBFMCombinatorics
open Finset Polynomial

/-- Polynomial coefficients extended by zero to negative integer indices. -/
def coeffZ (P : ℝ[X]) (k : ℤ) : ℝ := if 0 ≤ k then P.coeff k.toNat else 0

@[simp] lemma coeffZ_nat (P : ℝ[X]) (k : ℕ) : coeffZ P k = P.coeff k := by
  simp [coeffZ]

lemma coeffZ_neg (P : ℝ[X]) {k : ℤ} (hk : k < 0) : coeffZ P k = 0 := by
  simp [coeffZ, not_le.mpr hk]

lemma coeffZ_finite (P : ℝ[X]) : (Function.support (coeffZ P)).Finite := by
  apply (Set.finite_Icc (0 : ℤ) P.natDegree).subset
  intro k hk
  have hn : coeffZ P k ≠ 0 := hk
  have hk0 : 0 ≤ k := by
    by_contra h
    exact hn (coeffZ_neg P (lt_of_not_ge h))
  have hkn : k.toNat ≤ P.natDegree := by
    by_contra h
    apply hn
    simp [coeffZ, hk0, coeff_eq_zero_of_natDegree_lt (lt_of_not_ge h)]
  exact ⟨hk0, by omega⟩

/-- Ordinary polynomial multiplication is discrete convolution after zero extension. -/
theorem coeffZ_mul (P Q : ℝ[X]) : coeffZ (P*Q) = conv (coeffZ P) (coeffZ Q) := by
  funext k
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    rw [coeffZ_nat, conv]
    let s : Finset ℤ := (range (k+1)).image (fun i : ℕ => (i : ℤ))
    have hs : (∑' t : ℤ, coeffZ P t * coeffZ Q ((k : ℤ)-t)) =
        ∑ t ∈ s, coeffZ P t * coeffZ Q ((k : ℤ)-t) := by
      apply tsum_eq_sum
      intro t ht
      by_cases ht0 : 0 ≤ t
      · have htk : (k : ℤ) < t := by
          by_contra h
          apply ht
          exact mem_image.mpr ⟨t.toNat, by simp only [mem_range]; omega,
            by omega⟩
        rw [coeffZ_neg Q (by omega), mul_zero]
      · rw [coeffZ_neg P (lt_of_not_ge ht0), zero_mul]
    rw [hs]
    rw [show s = (range (k+1)).image (fun i : ℕ => (i : ℤ)) from rfl,
      Finset.sum_image (by intro i hi j hj hij; exact Int.ofNat.inj hij)]
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => P.coeff i * Q.coeff j)]
    apply sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
    have heq : (k : ℤ) - i = ((k-i : ℕ) : ℤ) := by omega
    rw [heq, coeffZ_nat, coeffZ_nat]
  · rw [coeffZ_neg (P*Q) (lt_of_not_ge hk), conv]
    symm
    calc
      _ = ∑' t : ℤ, (0 : ℝ) := by
        apply tsum_congr
        intro t
        by_cases ht : t < 0
        · rw [coeffZ_neg P ht, zero_mul]
        · rw [coeffZ_neg Q (by omega), mul_zero]
      _ = 0 := by simp

/-- TP2 is closed under ordinary polynomial multiplication. -/
theorem coeffZ_TP2_mul {P Q : ℝ[X]} (hP : TP2 (coeffZ P)) (hQ : TP2 (coeffZ Q)) :
    TP2 (coeffZ (P*Q)) := by
  rw [coeffZ_mul]
  exact TP2_conv hP hQ (coeffZ_finite P)

/-- The interval polynomial 1+x+...+x^(m-1), including the empty interval. -/
def intervalPoly (m : ℕ) : ℝ[X] := ∑ i ∈ range m, X^i

lemma intervalPoly_coeff (m k : ℕ) :
    (intervalPoly m).coeff k = if k < m then 1 else 0 := by
  simp [intervalPoly, coeff_X_pow]

lemma coeffZ_intervalPoly (m : ℕ) :
    coeffZ (intervalPoly m) = fun k : ℤ =>
      if 0 ≤ k ∧ k ≤ (m : ℤ)-1 then (1 : ℝ) else 0 := by
  funext k
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    rw [coeffZ_nat, intervalPoly_coeff]
    by_cases hkm : k < m
    · have h : (0 : ℤ) ≤ k ∧ (k : ℤ) ≤ (m : ℤ)-1 := by omega
      simp [hkm, h]
    · have h : ¬ ((0 : ℤ) ≤ k ∧ (k : ℤ) ≤ (m : ℤ)-1) := by omega
      simp [hkm, h]
  · simp [coeffZ, hk]

lemma intervalPoly_TP2 (m : ℕ) : TP2 (coeffZ (intervalPoly m)) := by
  rw [coeffZ_intervalPoly]
  exact interval_TP2 0 ((m : ℤ)-1)

lemma one_TP2 : TP2 (coeffZ (1 : ℝ[X])) := by
  have h : intervalPoly 1 = (1 : ℝ[X]) := by simp [intervalPoly]
  rw [← h]
  exact intervalPoly_TP2 1

/-- Every product of interval polynomials has TP2 coefficients. -/
theorem interval_product_TP2 {ι : Type*} (s : Finset ι) (m : ι → ℕ) :
    TP2 (coeffZ (∏ i ∈ s, intervalPoly (m i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one_TP2
  | @insert i s hi ih =>
    rw [prod_insert hi]
    exact coeffZ_TP2_mul (intervalPoly_TP2 _) ih

/-- A coefficientwise log-concavity endpoint for arbitrary products of intervals. -/
theorem interval_product_logConcave {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (k : ℕ) (hk : 1 ≤ k) :
    (∏ i ∈ s, intervalPoly (m i)).coeff (k-1) *
      (∏ i ∈ s, intervalPoly (m i)).coeff (k+1) ≤
        (∏ i ∈ s, intervalPoly (m i)).coeff k ^ 2 := by
  have h := TP2_logConcave (interval_product_TP2 s m) (k : ℤ)
  have heq : (k : ℤ)-1 = ((k-1 : ℕ) : ℤ) := by omega
  have heq2 : (k : ℤ)+1 = ((k+1 : ℕ) : ℤ) := by omega
  simpa only [heq, heq2, coeffZ_nat] using h

end BBFMCombinatorics

