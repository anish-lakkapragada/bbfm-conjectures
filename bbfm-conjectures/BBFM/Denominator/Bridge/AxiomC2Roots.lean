/- Source: AxiomMath/PartitionPolynomial b2a9e8d75cc76e5c432f15f668c18826a9abab80.
Prefix through rootMultiplicity_gCommon; only imports narrowed, later coprimality proof omitted. -/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

/- Root multiplicities and the common polynomial factor in the partition denominator. -/

open Polynomial Finset

noncomputable section

/-- Multiplicity of `i` in a partition. -/
def Nat.Partition.mult {n : ℕ} (p : n.Partition) (i : ℕ) : ℕ :=
  Multiset.count i p.parts

/-- Subsum polynomial of a partition λ: ∏ (1 + X^{λ_j}). -/
def subsumPoly {n : ℕ} (p : n.Partition) : Polynomial ℚ :=
  (p.parts.map (fun i => (1 : Polynomial ℚ) + X ^ i)).prod

/-- Common denominator den*(n, x) = ∏_{i=1}^{n} (1 + x^i)^{⌊n/i⌋}. -/
def denStar (n : ℕ) : Polynomial ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (n / i)

/-- Per-partition summand h_λ^{(n)}(x) = ∏_{i=1}^{n} (1 + x^i)^{⌊n/i⌋ - m_λ(i)}. -/
def hSummand {n : ℕ} (p : n.Partition) : Polynomial ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (n / i - p.mult i)

/-- Unreduced numerator num*(n, x) = ∑_{λ ⊢ n} h_λ^{(n)}(x). -/
def numStar (n : ℕ) : Polynomial ℚ :=
  ∑ p : n.Partition, hSummand p

/-- Common factor G(n, x) = gcd of the family {h_λ^{(n)}(x) : λ ⊢ n}. -/
def gCommon (n : ℕ) : Polynomial ℚ :=
  (Finset.univ : Finset n.Partition).gcd hSummand

/-- Reduced numerator num(n, x) = num*(n, x) / G(n, x), with num(0, x) = 1 by convention. -/
def numReduced (n : ℕ) : Polynomial ℚ :=
  if n = 0 then 1 else numStar n / gCommon n

/-- Reduced denominator den(n, x) = den*(n, x) / G(n, x). -/
def denReduced (n : ℕ) : Polynomial ℚ :=
  denStar n / gCommon n

/-! ## Helper lemmas -/

/-- For any partition `p` of `n`, summing `i * (multiplicity of i in p)` over `i ∈ [1,n]`
gives `n`. -/
lemma sum_mult_eq_n {n : ℕ} (p : n.Partition) :
    ∑ i ∈ Finset.Icc 1 n, i * p.mult i = n := by
  have hsub : p.parts.toFinset ⊆ Finset.Icc 1 n := by
    intro x hx
    rw [Multiset.mem_toFinset] at hx
    have hpos : 0 < x := p.parts_pos hx
    have hle : x ≤ n := by
      have := Multiset.le_sum_of_mem hx
      rw [p.parts_sum] at this
      exact this
    exact Finset.mem_Icc.mpr ⟨hpos, hle⟩
  have hsum : p.parts.sum =
      ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i :=
    Finset.sum_multiset_count_of_subset p.parts (Finset.Icc 1 n) hsub
  have heq : ∑ i ∈ Finset.Icc 1 n, i * p.mult i
      = ∑ i ∈ Finset.Icc 1 n, Multiset.count i p.parts • i := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [Nat.Partition.mult, Nat.mul_comm, smul_eq_mul]
  rw [heq, ← hsum, p.parts_sum]

lemma subset_Icc_of_partition_parts {n : ℕ} (p : n.Partition) :
    p.parts.toFinset ⊆ Finset.Icc 1 n := by
  intro x hx
  have h₂ : x ∈ p.parts := by grind
  have h₃ : 1 ≤ x := by grind
  have h₄ : x ≤ n := by grind
  grind

lemma mult_eq_zero_of_not_mem_toFinset {n : ℕ} (p : n.Partition) (i : ℕ)
    (h : i ∉ p.parts.toFinset) : p.mult i = 0 := by
  have h₁ : i ∉ p.parts := by
    intro h₂
    have h₃ : i ∈ p.parts.toFinset := Multiset.mem_toFinset.mpr h₂
    contradiction
  simp_all [Nat.Partition.mult]

/-- Step 1: Reformulate `subsumPoly p` as a product over `Icc 1 n` weighted by `p.mult i`. -/
lemma subsumPoly_eq_prod_Icc {n : ℕ} (p : n.Partition) :
    subsumPoly p =
      ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (p.mult i) := by
  unfold subsumPoly
  rw [Finset.prod_multiset_map_count]
  show ∏ m ∈ p.parts.toFinset, ((1 : Polynomial ℚ) + X ^ m) ^ p.mult m =
      ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ p.mult i
  apply Finset.prod_subset (subset_Icc_of_partition_parts p) ?_
  intro i _hi hni
  have hmult : p.mult i = 0 := mult_eq_zero_of_not_mem_toFinset p i hni
  rw [hmult, pow_zero]

lemma i_mul_mult_le_n {n : ℕ} (p : n.Partition) {i : ℕ}
    (_hi1 : 1 ≤ i) (_hi2 : i ≤ n) : i * p.mult i ≤ n := by
  have h₁ : (p.parts.filter (· = i)) = Multiset.replicate (p.mult i) i := by
    grind only [Nat.Partition.mult.eq_def, Multiset.filter_eq']
  have h₂ : (p.parts.filter (· = i)).sum = p.mult i * i := by
    simp [Multiset.sum_replicate, smul_eq_mul, h₁]
  have h₃ : (p.parts.filter (· = i)) ≤ p.parts := by simp
  have h₄ : (p.parts.filter (· = i)).sum ≤ p.parts.sum := by
    grind only [Nat.Partition.parts_sum, Multiset.filter_add_not, = Multiset.sum_add]
  have h₅ : p.mult i * i ≤ n := by
    grind only [Nat.Partition.parts_sum]
  grind

/-- Step 2: For every partition `p ⊢ n` and every `i`, `p.mult i ≤ n / i`. -/
lemma mult_le_div {n : ℕ} (p : n.Partition) (i : ℕ) : p.mult i ≤ n / i := by
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    rw [Nat.div_zero]
    have h0 : (0 : ℕ) ∉ p.parts.toFinset := by
      intro hmem
      have := subset_Icc_of_partition_parts p hmem
      simp [Finset.mem_Icc] at this
    exact (mult_eq_zero_of_not_mem_toFinset p 0 h0).le
  · by_cases hin : i ≤ n
    · rw [Nat.le_div_iff_mul_le hi]
      have := i_mul_mult_le_n p hi hin
      rw [Nat.mul_comm] at this
      exact this
    · push_neg at hin
      have hi_notin : i ∉ p.parts.toFinset := by
        intro hmem
        have := subset_Icc_of_partition_parts p hmem
        simp [Finset.mem_Icc] at this
        omega
      rw [mult_eq_zero_of_not_mem_toFinset p i hi_notin]
      exact Nat.zero_le _

/-- Step 1.1: For every partition `p ⊢ n`, the polynomial `denStar n` factors as
`hSummand p * subsumPoly p`. -/
lemma denStar_eq_hSummand_mul_subsumPoly {n : ℕ} (p : n.Partition) :
    denStar n = hSummand p * subsumPoly p := by
  rw [subsumPoly_eq_prod_Icc p]
  unfold denStar hSummand
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _hi
  rw [← pow_add]
  congr 1
  exact (Nat.sub_add_cancel (mult_le_div p i)).symm

/-- `gCommon n` divides `hSummand p` for every partition `p` of `n`, since
`gCommon n` is defined as the gcd of the family `hSummand` over all partitions.
Uses `Finset.gcd_dvd : ∀ {α β : Type*} [inst : CommGCDMonoid α] {s : Finset β} {f : β → α}
{b : β}, b ∈ s → f b ∣ s.gcd f` or rather the symmetric `Finset.dvd_gcd` direction;
here we use that for `Finset.univ`, `p ∈ univ`, so `s.gcd f ∣ f p`. -/
lemma gCommon_dvd_hSummand {n : ℕ} (p : n.Partition) :
    gCommon n ∣ hSummand p := by
  have h₁ : gCommon n = (Finset.univ : Finset n.Partition).gcd hSummand := rfl
  rw [h₁]
  apply Finset.gcd_dvd
  simp_all

/-- `gCommon n` divides `denStar n`. For `n ≥ 1`, there exists a partition `p` of `n`
(at least the all-ones partition), and `gCommon n ∣ hSummand p ∣ denStar n` by
`gCommon_dvd_hSummand` and `denStar_eq_hSummand_mul_subsumPoly`. -/
lemma gCommon_dvd_denStar (n : ℕ) (hn : 1 ≤ n) : gCommon n ∣ denStar n := by
  have _hn := hn
  let p0 : n.Partition := Nat.Partition.indiscrete n
  have h1 : gCommon n ∣ hSummand p0 := gCommon_dvd_hSummand p0
  have h2 : hSummand p0 ∣ denStar n := by
    refine ⟨subsumPoly p0, ?_⟩
    exact denStar_eq_hSummand_mul_subsumPoly p0
  exact h1.trans h2

/-- `gCommon n` divides `numStar n` because `numStar n = ∑_{p} hSummand p` and
`gCommon n` divides each summand. -/
lemma gCommon_dvd_numStar (n : ℕ) : gCommon n ∣ numStar n := by
  have h₁ : gCommon n = (Finset.univ : Finset n.Partition).gcd hSummand := rfl
  rw [h₁]
  have h₂ : ∀ (p : n.Partition), (Finset.univ : Finset n.Partition).gcd hSummand ∣ hSummand p := by
    intro p
    apply Finset.gcd_dvd
    simp [Finset.mem_univ]
  have h₃ : (Finset.univ : Finset n.Partition).gcd hSummand ∣ ∑ p : n.Partition, hSummand p := by
    apply Finset.dvd_sum
    intro p _
    exact h₂ p
  simpa [numStar] using h₃

/-- For `n ≥ 1`, `gCommon n` is nonzero: each `hSummand p` is a product of
nonzero polynomials `(1 + X^i)`, so it is nonzero, and at least one such `p` exists. -/
lemma one_add_X_pow_ne_zero (i : ℕ) (hi : 1 ≤ i) :
    ((1 : Polynomial ℚ) + X ^ i) ≠ 0 := by
  have h : Polynomial.coeff ((1 : Polynomial ℚ) + X ^ i) 0 = (1 : ℚ) := by
    grind only [X_dvd_iff, coeff_add, coeff_inj, coeff_one, = coeff_X_pow]
  have h₀ : Polynomial.coeff (0 : Polynomial ℚ) 0 = (0 : ℚ) := by simp
  have h₁ : ((1 : Polynomial ℚ) + X ^ i) ≠ 0 := by grind
  exact h₁

lemma hSummand_ne_zero {n : ℕ} (p : n.Partition) : hSummand p ≠ 0 := by
  unfold hSummand
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact pow_ne_zero _ (one_add_X_pow_ne_zero i hi.1)

lemma gCommon_ne_zero (n : ℕ) (hn : 1 ≤ n) : gCommon n ≠ 0 := by
  have _h := hn
  intro h
  rw [gCommon, Finset.gcd_eq_zero_iff] at h
  have hp : hSummand (Nat.Partition.indiscrete n) = 0 :=
    h (Nat.Partition.indiscrete n) (Finset.mem_univ _)
  exact hSummand_ne_zero (Nat.Partition.indiscrete n) hp

/-- For `n ≥ 1`, the equation `numStar n = numReduced n * gCommon n` holds.
This follows from `numReduced n = numStar n / gCommon n` (since `n ≠ 0`) and
divisibility `gCommon n ∣ numStar n`. -/
lemma numStar_eq_numReduced_mul_gCommon (n : ℕ) (hn : 1 ≤ n) :
    numStar n = numReduced n * gCommon n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hg_ne : gCommon n ≠ 0 := gCommon_ne_zero n hn
  have hg_dvd : gCommon n ∣ numStar n := gCommon_dvd_numStar n
  have h_red : numReduced n = numStar n / gCommon n := by
    unfold numReduced
    exact if_neg hn0
  rw [h_red]
  rw [mul_comm]
  exact (EuclideanDomain.mul_div_cancel' hg_ne hg_dvd).symm

/-- For `n ≥ 1`, the equation `denStar n = denReduced n * gCommon n` holds.
Uses `denReduced n = denStar n / gCommon n` and `gCommon n ∣ denStar n`. -/
lemma denStar_eq_denReduced_mul_gCommon (n : ℕ) (hn : 1 ≤ n) :
    denStar n = denReduced n * gCommon n := by
  have hdvd : gCommon n ∣ denStar n := gCommon_dvd_denStar n hn
  have hmod : denStar n % gCommon n = 0 := EuclideanDomain.mod_eq_zero.mpr hdvd
  have hdam : gCommon n * (denStar n / gCommon n) + denStar n % gCommon n = denStar n :=
    EuclideanDomain.div_add_mod (denStar n) (gCommon n)
  rw [hmod, add_zero] at hdam
  show denStar n = denStar n / gCommon n * gCommon n
  rw [mul_comm]
  exact hdam.symm

/-- `denStar n` is nonzero, since it is a product of nonzero polynomials of the form
`(1 + X^i)^k` in `ℚ[X]`. -/
lemma denStar_ne_zero (n : ℕ) : denStar n ≠ 0 := by
  unfold denStar
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  rw [Finset.mem_Icc] at hi
  exact pow_ne_zero _ (one_add_X_pow_ne_zero i hi.1)

/-! ### Reduction to common-root statement over ℂ

We use the embedding `Polynomial ℚ →+* Polynomial ℂ`. The key fact is that
two polynomials in `ℚ[X]` are coprime iff their images in `ℂ[X]` are coprime, iff
they have no common complex root.
-/

/-- If two polynomials in `ℚ[X]` have no common complex root (after embedding into
`ℂ[X]`), and the second is nonzero, then they are coprime in `ℚ[X]`.
This packages the standard fact that `ℚ[X]` is a UFD/PID where coprimality is
equivalent to having no common irreducible factor, and over the algebraically closed
field `ℂ`, an irreducible polynomial has a root.

Uses: `EuclideanDomain.isCoprime_iff_gcd_eq_one` and `Polynomial.IsAlgClosed.exists_root`
applied to a nonzero common factor over `ℂ`. -/
lemma degree_pos_of_ne_zero_of_not_isUnit
    (p : Polynomial ℚ) (hne : p ≠ 0) (hnu : ¬ IsUnit p) : 0 < p.degree := by
  have h1 : p.degree ≠ 0 := by
    intro h
    have h₂ : IsUnit p := by
      rw [Polynomial.isUnit_iff_degree_eq_zero]
      simp_all
    contradiction
  have h2 : p.natDegree ≠ 0 := by
    have h₂ : p.degree = ↑(p.natDegree) := by
      rw [Polynomial.degree_eq_natDegree hne]
    have h₃ : (p.degree : WithBot ℕ) ≠ 0 := by simpa using h1
    have h₄ : (↑(p.natDegree) : WithBot ℕ) ≠ 0 := by
      rw [h₂] at h₃
      exact h₃
    have h₅ : p.natDegree ≠ 0 := by
      intro h₅
      simp [h₅] at h₄
    exact h₅
  have h3 : 0 < p.natDegree := by
    by_contra h
    have h₄ : p.natDegree = 0 := by
      omega
    exact h2 h₄
  have h4 : 0 < p.degree := by
    have h₅ : p.degree = ↑(p.natDegree) := by
      rw [Polynomial.degree_eq_natDegree hne]
    rw [h₅]
    exact WithBot.coe_lt_coe.mpr h3
  exact h4

lemma degree_map_pos (p : Polynomial ℚ) (hp : 0 < p.degree) :
    0 < (p.map (algebraMap ℚ ℂ)).degree := by
  have h_degree_eq : (p.map (algebraMap ℚ ℂ)).degree = p.degree := by simp
  have h_main : 0 < (p.map (algebraMap ℚ ℂ)).degree := by grind
  grind

lemma eval_map_eq_zero_of_dvd_of_eval_eq_zero
    (g P : Polynomial ℚ) (h : g ∣ P) (α : ℂ)
    (hg : (g.map (algebraMap ℚ ℂ)).eval α = 0) :
    (P.map (algebraMap ℚ ℂ)).eval α = 0 := by
  have h₁ : ∃ (Q : Polynomial ℚ), P = g * Q := by assumption
  have h₂ : ∀ (Q : Polynomial ℚ), P = g * Q → (P.map (algebraMap ℚ ℂ)).eval α = 0 := by simp_all
  have h₃ : (P.map (algebraMap ℚ ℂ)).eval α = 0 := by grind
  grind

lemma isCoprime_of_no_common_complex_root (P Q : Polynomial ℚ)
    (hQ : Q ≠ 0)
    (h : ∀ α : ℂ, (P.map (algebraMap ℚ ℂ)).eval α = 0 →
      (Q.map (algebraMap ℚ ℂ)).eval α ≠ 0) :
    IsCoprime P Q := by
  apply EuclideanDomain.isCoprime_of_dvd
  · rintro ⟨_, hQ0⟩
    exact hQ hQ0
  · intro z hzNonUnit hzNeZero hzP hzQ
    have hzDegPos : 0 < z.degree :=
      degree_pos_of_ne_zero_of_not_isUnit z hzNeZero hzNonUnit
    have hZDegPos : 0 < (z.map (algebraMap ℚ ℂ)).degree := degree_map_pos z hzDegPos
    have hDegNeZero : (z.map (algebraMap ℚ ℂ)).degree ≠ 0 := ne_of_gt hZDegPos
    obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (z.map (algebraMap ℚ ℂ)) hDegNeZero
    have hZα : (z.map (algebraMap ℚ ℂ)).eval α = 0 := hα
    have hPα : (P.map (algebraMap ℚ ℂ)).eval α = 0 :=
      eval_map_eq_zero_of_dvd_of_eval_eq_zero z P hzP α hZα
    have hQα : (Q.map (algebraMap ℚ ℂ)).eval α = 0 :=
      eval_map_eq_zero_of_dvd_of_eval_eq_zero z Q hzQ α hZα
    exact h α hPα hQα

/-! ### Vanishing order analysis -/

/-- If `α : ℂ` is a root of `denStar n` mapped to `ℂ[X]`, then there exists `i` with
`1 ≤ i ≤ n` such that `α^i = -1`. This follows from the factorization
`denStar n = ∏ (1 + X^i)^(n/i)` and the fact that `ℂ[X]` is an integral domain. -/
lemma eval_map_denStar (n : ℕ) (α : ℂ) :
    ((denStar n).map (algebraMap ℚ ℂ)).eval α =
      ∏ i ∈ Finset.Icc 1 n, (1 + α ^ i) ^ (n / i) := by
  unfold denStar
  simp [Polynomial.map_prod, Polynomial.eval_prod, Polynomial.map_pow, Polynomial.eval_pow,
        Polynomial.map_add, Polynomial.eval_add, Polynomial.map_one, Polynomial.eval_one,
        Polynomial.map_X, Polynomial.eval_X]

lemma exists_pow_eq_neg_one_of_denStar_eval {n : ℕ} (α : ℂ)
    (h : ((denStar n).map (algebraMap ℚ ℂ)).eval α = 0) :
    ∃ i ∈ Finset.Icc 1 n, α ^ i = -1 := by
  rw [eval_map_denStar] at h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨i, hi, hzero⟩ := h
  refine ⟨i, hi, ?_⟩
  rw [pow_eq_zero_iff'] at hzero
  have h1 : (1 : ℂ) + α ^ i = 0 := hzero.1
  linear_combination h1

/-- If `α^i = -1` for some `i ≥ 1`, then `α` is a root of unity of even order `2s`
for some `s ≥ 1`. Specifically, `α^(2i) = 1` and `α ≠ 0` (since `α^i = -1 ≠ 0`),
so `α` is a torsion element with order dividing `2i`. Then this order is even
because `α^i = -1 ≠ 1`. -/
lemma pow_two_mul_eq_one_of_pow_eq_neg_one
    {α : ℂ} {i : ℕ} (h : α ^ i = -1) : α ^ (2 * i) = 1 := by
  have h₁ : α ^ (2 * i) = (α ^ i) ^ 2 := pow_mul' α 2 i
  have h₂ : (α ^ i) ^ 2 = 1 := by grind
  grind

lemma exists_minimal_pow_eq_one (α : ℂ) (N : ℕ) (hN : 1 ≤ N) (hαN : α ^ N = 1) :
    ∃ d : ℕ, 1 ≤ d ∧ α ^ d = 1 ∧
      (∀ m : ℕ, 1 ≤ m → m < d → α ^ m ≠ 1) := by
  classical
  have h : ∃ d : ℕ, 1 ≤ d ∧ α ^ d = 1 := by
    refine' ⟨N, _⟩
    exact ⟨by linarith, hαN⟩
  use Nat.find h
  have h₁ : 1 ≤ Nat.find h ∧ α ^ Nat.find h = 1 := Nat.find_spec h
  have h₂ : ∀ m : ℕ, 1 ≤ m → m < Nat.find h → α ^ m ≠ 1 := by
    intro m hm₁ hm₂
    by_contra h₃
    have h₄ : 1 ≤ m ∧ α ^ m = 1 := ⟨hm₁, h₃⟩
    have h₆ : Nat.find h ≤ m := Nat.find_min' h h₄
    linarith
  exact ⟨h₁.1, h₁.2, h₂⟩

lemma two_le_minimal_pow_of_pow_eq_neg_one
    {α : ℂ} {i d : ℕ} (_hi : 1 ≤ i) (hd : 1 ≤ d) (hα_neg : α ^ i = -1)
    (hαd : α ^ d = 1) : 2 ≤ d := by
  by_contra! h
  have h₁ : d = 1 := by
    linarith
  rw [h₁] at hαd
  have h₂ : α ^ 1 = 1 := hαd
  have h₃ : α = 1 := by
    simpa using h₂
  have h₄ : (1 : ℂ) ^ i = 1 := by simp
  rw [h₃] at hα_neg
  have h₅ : (1 : ℂ) ^ i = -1 := by simpa using hα_neg
  have h₆ : (1 : ℂ) ^ i = 1 := by simp
  rw [h₆] at h₅
  norm_num at h₅

lemma even_minimal_pow_of_pow_eq_neg_one
    {α : ℂ} {i d : ℕ} (_hi : 1 ≤ i) (hα_neg : α ^ i = -1)
    (hαd : α ^ d = 1) : Even d := by
  have h1 : (-1 : ℂ) ^ d = 1 := by
    calc
      (-1 : ℂ) ^ d = (α ^ i) ^ d := by rw [hα_neg]
      _ = α ^ (i * d) := by rw [← pow_mul]
      _ = (α ^ d) ^ i := by
        rw [← pow_mul]
        ring_nf
      _ = 1 ^ i := by rw [hαd]
      _ = 1 := by simp
  have h2 : Even d := by
    by_contra h
    have h3 : ¬Even d := h
    have h4 : Odd d := by
      simp [Nat.even_iff, Nat.odd_iff] at h3 ⊢
      omega
    have h5 : (-1 : ℂ) ^ d = -1 := by
      have h6 : d % 2 = 1 := by
        cases' h4 with k hk
        omega
      have h7 : (-1 : ℂ) ^ d = -1 := by
        rw [← Nat.mod_add_div d 2]
        simp [h6, pow_add, pow_mul, pow_one, pow_two]
      exact h7
    rw [h5] at h1
    norm_num at h1
  exact h2

lemma exists_even_order_of_pow_eq_neg_one (α : ℂ) (i : ℕ) (hi : 1 ≤ i)
    (h : α ^ i = -1) :
    ∃ s : ℕ, 1 ≤ s ∧ α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0 := by
  have h2i : α ^ (2 * i) = 1 := pow_two_mul_eq_one_of_pow_eq_neg_one h
  have h2i_pos : 1 ≤ 2 * i := by linarith
  obtain ⟨d, hd_pos, hαd, hd_min⟩ := exists_minimal_pow_eq_one α (2 * i) h2i_pos h2i
  have hd_even : Even d := even_minimal_pow_of_pow_eq_neg_one hi h hαd
  obtain ⟨s, hs_eq⟩ := hd_even
  have hds : d = 2 * s := by rw [hs_eq]; ring
  have hd_ge_two : 2 ≤ d := two_le_minimal_pow_of_pow_eq_neg_one hi hd_pos h hαd
  have hs_pos : 1 ≤ s := by
    by_contra h0
    push_neg at h0
    interval_cases s
    omega
  refine ⟨s, hs_pos, ?_, ?_⟩
  · rw [← hds]; exact hαd
  · intro k hk hαk
    by_contra hne
    have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hne
    have hkd : k < d := by rw [hds]; exact hk
    exact hd_min k hk_pos hkd hαk

/-- For `α` of exact order `2s` and `j : ℕ`, we have `α^j = -1 ↔ j ≡ s (mod 2s)`. -/
lemma pow_eq_neg_one_iff_aux {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (j : ℕ) :
    α ^ j = -1 ↔ j % (2 * s) = s := by
  obtain ⟨hpow, hmin⟩ := hord
  have hs_lt : s < 2 * s := by omega
  have h2s_pos : 0 < 2 * s := by omega
  have hαs : α ^ s = -1 := by
    have hsq : (α ^ s) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm]; exact hpow
    rcases sq_eq_one_iff.mp hsq with h1 | hn1
    · exfalso; have := hmin s hs_lt h1; omega
    · exact hn1
  have hchar1 : ∀ k : ℕ, α ^ k = 1 ↔ 2 * s ∣ k := by
    intro k
    constructor
    · intro hk
      have hkeq : k = 2 * s * (k / (2 * s)) + k % (2 * s) := (Nat.div_add_mod k (2 * s)).symm
      have hr_lt : k % (2 * s) < 2 * s := Nat.mod_lt k h2s_pos
      have hαr : α ^ (k % (2 * s)) = 1 := by
        have : α ^ k = α ^ (2 * s * (k / (2 * s))) * α ^ (k % (2 * s)) := by
          rw [← pow_add, ← hkeq]
        rw [this, pow_mul, hpow, one_pow, one_mul] at hk
        exact hk
      have hr0 : k % (2 * s) = 0 := hmin _ hr_lt hαr
      exact Nat.dvd_of_mod_eq_zero hr0
    · rintro ⟨q, rfl⟩
      rw [pow_mul, hpow, one_pow]
  constructor
  · intro hj
    set r := j % (2 * s) with hr_def
    set q := j / (2 * s) with hq_def
    have hjeq : j = 2 * s * q + r := by rw [hq_def, hr_def]; exact (Nat.div_add_mod j (2*s)).symm
    have hr_lt : r < 2 * s := Nat.mod_lt j h2s_pos
    have hαr : α ^ r = -1 := by
      have : α ^ j = α ^ (2 * s * q) * α ^ r := by rw [← pow_add, ← hjeq]
      rw [this, pow_mul, hpow, one_pow, one_mul] at hj
      exact hj
    have h2r : α ^ (2 * r) = 1 := by
      rw [mul_comm 2 r, pow_mul, hαr]; ring
    have hdvd : 2 * s ∣ 2 * r := (hchar1 (2 * r)).mp h2r
    obtain ⟨m, hm⟩ := hdvd
    have h2r_lt : 2 * r < 4 * s := by omega
    have hm_lt : m < 2 := by
      by_contra h
      push_neg at h
      have : 2 * s * 2 ≤ 2 * s * m := Nat.mul_le_mul_left _ h
      omega
    interval_cases m
    · have hr0 : r = 0 := by omega
      rw [hr0, pow_zero] at hαr
      exfalso
      have : (1 : ℂ) ≠ -1 := by norm_num
      exact this hαr
    · omega
  · intro hjs
    have hjeq : j = 2 * s * (j / (2 * s)) + s := by
      have := (Nat.div_add_mod j (2 * s)).symm
      rw [hjs] at this; exact this
    calc α ^ j = α ^ (2 * s * (j / (2 * s)) + s) := by rw [← hjeq]
      _ = α ^ (2 * s * (j / (2 * s))) * α ^ s := by rw [pow_add]
      _ = (α ^ (2 * s)) ^ (j / (2 * s)) * α ^ s := by rw [pow_mul]
      _ = 1 * (-1) := by rw [hpow, one_pow, hαs]
      _ = -1 := by ring

/-- The "bad set" `B = {j ∈ [1,n] : α^j = -1}`. For `α` of order `2s`, this equals
`{s, 3s, 5s, ...} ∩ [1,n]`. -/
def badSet (α : ℂ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun j => α ^ j = -1)

/-- For `α` of exact order `2s`, the count `c(λ) = ∑_{j ∈ B} m_λ(j)`. -/
def cCount (α : ℂ) (n : ℕ) (p : n.Partition) : ℕ :=
  ∑ j ∈ badSet α n, p.mult j

/-- The "C" quantity: `C = ∑_{j ∈ B} ⌊n/j⌋`. This is the vanishing order of
`denStar n` at `α`. -/
def cC (α : ℂ) (n : ℕ) : ℕ :=
  ∑ j ∈ badSet α n, n / j

/-! ### Order of vanishing computations

We use `Polynomial.rootMultiplicity` for the vanishing order. We package the
needed facts as helper lemmas.
-/

lemma rootMultiplicity_prod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*}
    (S : Finset ι) (f : ι → Polynomial R) (x : R) (hf : ∀ i ∈ S, f i ≠ 0) :
    Polynomial.rootMultiplicity x (∏ i ∈ S, f i) = ∑ i ∈ S, Polynomial.rootMultiplicity x (f i) := by
  classical
  have h₂ : ∀ s : Finset ι, (∀ i ∈ s, f i ≠ 0) → Polynomial.rootMultiplicity x (∏ i ∈ s, f i) = ∑ i ∈ s, Polynomial.rootMultiplicity x (f i) := by
    intro s
    induction' s using Finset.induction_on with i s his ih
    · simp
    · intro h
      have h₃ : f i ≠ 0 := h i (Finset.mem_insert_self i s)
      have h₄ : ∀ i ∈ s, f i ≠ 0 := fun j hj => h j (Finset.mem_insert_of_mem hj)
      have h₅ : Polynomial.rootMultiplicity x (∏ j ∈ s, f j) = ∑ j ∈ s, Polynomial.rootMultiplicity x (f j) := ih h₄
      calc
        Polynomial.rootMultiplicity x (∏ j ∈ (insert i s), f j) = Polynomial.rootMultiplicity x ((f i) * (∏ j ∈ s, f j)) := by
          rw [Finset.prod_insert his]
        _ = Polynomial.rootMultiplicity x (f i) + Polynomial.rootMultiplicity x (∏ j ∈ s, f j) := by
          have h₆ : f i ≠ 0 := h₃
          have h₇ : (∏ j ∈ s, f j) ≠ 0 := by
            apply Finset.prod_ne_zero_iff.mpr
            intro j hj
            exact h₄ j hj
          rw [rootMultiplicity_mul]
          simp_all
        _ = (Polynomial.rootMultiplicity x (f i)) + ∑ j ∈ s, Polynomial.rootMultiplicity x (f j) := by rw [h₅]
        _ = ∑ j ∈ insert i s, Polynomial.rootMultiplicity x (f j) := by
          rw [Finset.sum_insert his]
  exact h₂ S (fun i hi => hf i hi)

lemma rootMultiplicity_pow {R : Type*} [CommRing R] [IsDomain R]
    (g : Polynomial R) (k : ℕ) (x : R) (hg : g ≠ 0) :
    Polynomial.rootMultiplicity x (g ^ k) = k * Polynomial.rootMultiplicity x g := by
  have h₁ : ∀ n : ℕ, Polynomial.rootMultiplicity x (g ^ n) = n * Polynomial.rootMultiplicity x g := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      calc
        Polynomial.rootMultiplicity x (g ^ (n + 1)) = Polynomial.rootMultiplicity x (g ^ n * g) :=
          by
            ring_nf
        _ = Polynomial.rootMultiplicity x (g ^ n) + Polynomial.rootMultiplicity x g :=
          by
            have h₂ : g ^ n ≠ 0 := by
              exact pow_ne_zero _ hg
            have h₃ : g ≠ 0 := hg
            have h₄ : Polynomial.rootMultiplicity x (g ^ n * g) = Polynomial.rootMultiplicity x (g ^ n) + Polynomial.rootMultiplicity x g := by
              apply Polynomial.rootMultiplicity_mul
              simp_all
            rw [h₄]
        _ = n * Polynomial.rootMultiplicity x g + Polynomial.rootMultiplicity x g := by
          rw [ih]
        _ = (n + 1) * Polynomial.rootMultiplicity x g := by
          ring
  rw [h₁ k]

lemma one_add_X_pow_ne_zero_complex (i : ℕ) :
    ((1 : Polynomial ℂ) + Polynomial.X ^ i) ≠ 0 := by
  intro h
  have h₁ := congr_arg (fun p => Polynomial.eval 0 p) h
  simp [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X] at h₁
  cases i <;> simp_all [pow_succ]

lemma rootMultiplicity_one_add_X_pow_complex_zero_case
    (α : ℂ) (i : ℕ) (h : α ^ i ≠ -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
  have h₁ : ¬Polynomial.IsRoot ((1 : Polynomial ℂ) + Polynomial.X ^ i) α := by
    intro h₂
    have h₃ : Polynomial.eval α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
      simpa [Polynomial.IsRoot] using h₂
    have h₄ : Polynomial.eval α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = (1 : ℂ) + α ^ i := by
      simp [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
    rw [h₄] at h₃
    have h₅ : (1 : ℂ) + α ^ i = 0 := by simpa using h₃
    have h₆ : α ^ i = -1 := by
      have h₇ : (1 : ℂ) + α ^ i = 0 := h₅
      linear_combination h₇
    exact h h₆
  have h₂ : Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 0 := by
    rw [Polynomial.rootMultiplicity_eq_zero]
    simp_all [Polynomial.IsRoot]
  exact h₂

lemma rootMultiplicity_one_add_X_pow_complex_one_case_le
    (α : ℂ) (i : ℕ) (hi : 1 ≤ i) (h : α ^ i = -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) ≤ 1 := by
  set p : Polynomial ℂ := 1 + Polynomial.X ^ i with hp
  have hp_ne : p ≠ 0 := one_add_X_pow_ne_zero_complex i
  rw [Polynomial.rootMultiplicity_le_iff hp_ne α 1]
  intro hdvd
  have hderiv_dvd : (Polynomial.X - Polynomial.C α) ∣ Polynomial.derivative p := by
    have := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hdvd
    simpa using this
  have hderiv : Polynomial.derivative p =
      Polynomial.C (i : ℂ) * Polynomial.X ^ (i - 1) := by
    simp [hp, Polynomial.derivative_add, Polynomial.derivative_one,
          Polynomial.derivative_X_pow]
  rw [hderiv] at hderiv_dvd
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def] at hderiv_dvd
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X] at hderiv_dvd
  have hi_pos : 0 < i := hi
  have hi_ne_nat : i ≠ 0 := Nat.pos_iff_ne_zero.mp hi_pos
  have hi_ne : (i : ℂ) ≠ 0 := by exact_mod_cast hi_ne_nat
  have hα_ne : α ≠ 0 := by
    intro hα0
    rw [hα0, zero_pow hi_ne_nat] at h
    exact absurd h (by norm_num)
  have hα_pow_ne : α ^ (i - 1) ≠ 0 := pow_ne_zero _ hα_ne
  rcases mul_eq_zero.mp hderiv_dvd with h1 | h2
  · exact hi_ne h1
  · exact hα_pow_ne h2

lemma rootMultiplicity_one_add_X_pow_complex_one_case
    (α : ℂ) (i : ℕ) (hi : 1 ≤ i) (h : α ^ i = -1) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i) = 1 := by
  set p : Polynomial ℂ := (1 : Polynomial ℂ) + Polynomial.X ^ i with hp_def
  have hp_ne : p ≠ 0 := one_add_X_pow_ne_zero_complex i
  have hroot : p.IsRoot α := by
    show p.eval α = 0
    simp [hp_def, h]
  have h_ge : 1 ≤ Polynomial.rootMultiplicity α p :=
    (Polynomial.rootMultiplicity_pos hp_ne).mpr hroot
  have h_le : Polynomial.rootMultiplicity α p ≤ 1 :=
    rootMultiplicity_one_add_X_pow_complex_one_case_le α i hi h
  omega

lemma rootMultiplicity_one_add_X_pow_complex (α : ℂ) (i : ℕ) (hi : 1 ≤ i) :
    Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + Polynomial.X ^ i)
      = if α ^ i = -1 then 1 else 0 := by
  by_cases h : α ^ i = -1
  · rw [if_pos h]
    exact rootMultiplicity_one_add_X_pow_complex_one_case α i hi h
  · rw [if_neg h]
    exact rootMultiplicity_one_add_X_pow_complex_zero_case α i h

lemma map_one_add_X_pow (i : ℕ) :
    Polynomial.map (algebraMap ℚ ℂ) ((1 : Polynomial ℚ) + Polynomial.X ^ i)
      = ((1 : Polynomial ℂ) + Polynomial.X ^ i) := by
  have h₁ : Polynomial.map (algebraMap ℚ ℂ) ((1 : Polynomial ℚ) + Polynomial.X ^ i) =
      Polynomial.map (algebraMap ℚ ℂ) (1 : Polynomial ℚ) + Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X ^ i) := by
    rw [Polynomial.map_add]
  have h₂ : Polynomial.map (algebraMap ℚ ℂ) (1 : Polynomial ℚ) = (1 : Polynomial ℂ) := by
    simp [Polynomial.map_one]
  have h₃ : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X ^ i : Polynomial ℚ) = (Polynomial.X : Polynomial ℂ) ^ i := by
    have h₄ : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X ^ i : Polynomial ℚ) =
        (Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X : Polynomial ℚ)) ^ i := by
      rw [Polynomial.map_pow]
    rw [h₄]
    have h₅ : Polynomial.map (algebraMap ℚ ℂ) (Polynomial.X : Polynomial ℚ) = (Polynomial.X : Polynomial ℂ) := by
      simp [Polynomial.map_X]
    rw [h₅]
  rw [h₁, h₂, h₃]

lemma map_denStar (n : ℕ) :
    Polynomial.map (algebraMap ℚ ℂ) (denStar n)
      = ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℂ) + X ^ i) ^ (n / i) := by
  classical
  unfold denStar
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Polynomial.map_pow, map_one_add_X_pow]

/-- The vanishing order of `denStar n` at `α` (after mapping to `ℂ[X]`) equals `cC α n`. -/
lemma rootMultiplicity_denStar (n : ℕ) (α : ℂ) :
    Polynomial.rootMultiplicity α ((denStar n).map (algebraMap ℚ ℂ)) = cC α n := by
  classical
  rw [map_denStar]
  rw [rootMultiplicity_prod (R := ℂ) _ _ _
        (fun i _ => pow_ne_zero _ (one_add_X_pow_ne_zero_complex i))]
  have hpow :
      ∀ i ∈ Finset.Icc 1 n,
        Polynomial.rootMultiplicity α (((1 : Polynomial ℂ) + X ^ i) ^ (n / i))
          = (n / i) * Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + X ^ i) := by
    intro i _
    exact rootMultiplicity_pow _ _ _ (one_add_X_pow_ne_zero_complex i)
  rw [Finset.sum_congr rfl hpow]
  have hbase :
      ∀ i ∈ Finset.Icc 1 n,
        (n / i) * Polynomial.rootMultiplicity α ((1 : Polynomial ℂ) + X ^ i)
          = (if α ^ i = -1 then n / i else 0) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_one_add_X_pow_complex α i hi1]
    by_cases h : α ^ i = -1
    · simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl hbase]
  unfold cC badSet
  rw [Finset.sum_filter]

/-- The vanishing order of `subsumPoly p` at `α` equals `cCount α n p`. -/
lemma rootMultiplicity_subsumPoly {n : ℕ} (p : n.Partition) (α : ℂ) :
    Polynomial.rootMultiplicity α ((subsumPoly p).map (algebraMap ℚ ℂ)) = cCount α n p := by
  classical
  rw [subsumPoly_eq_prod_Icc p]
  have hmap :
      Polynomial.map (algebraMap ℚ ℂ)
          (∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℚ) + X ^ i) ^ (p.mult i)) =
        ∏ i ∈ Finset.Icc 1 n, ((1 : Polynomial ℂ) + X ^ i) ^ (p.mult i) := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Polynomial.map_pow, map_one_add_X_pow i]
  rw [hmap]
  have hne :
      ∀ i ∈ Finset.Icc 1 n,
        ((1 : Polynomial ℂ) + X ^ i) ^ (p.mult i) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (one_add_X_pow_ne_zero_complex i)
  rw [rootMultiplicity_prod _ _ α hne]
  have hsum :
      ∑ i ∈ Finset.Icc 1 n,
          Polynomial.rootMultiplicity α (((1 : Polynomial ℂ) + X ^ i) ^ (p.mult i))
        = ∑ i ∈ Finset.Icc 1 n,
            p.mult i * (if α ^ i = -1 then 1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_pow _ _ α (one_add_X_pow_ne_zero_complex i),
        rootMultiplicity_one_add_X_pow_complex α i hi1]
  rw [hsum]
  unfold cCount badSet
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : α ^ i = -1
  · simp [h]
  · simp [h]

/-- For each partition `p ⊢ n`, the vanishing order of `hSummand p` at `α` equals
`cC α n - cCount α n p`. (We need that `cCount α n p ≤ cC α n`, which holds termwise
because `p.mult i ≤ n / i` for partitions of `n`.) -/
lemma finset_sum_sub_distrib_of_le {ι : Type*} (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, b i ≤ a i) :
    (∑ i ∈ S, a i) - (∑ i ∈ S, b i) = ∑ i ∈ S, (a i - b i) := by
  have h_main : (∑ i ∈ S, a i) - (∑ i ∈ S, b i) = ∑ i ∈ S, (a i - b i) :=
    Eq.symm (sum_tsub_distrib S h)
  grind

lemma rootMultiplicity_hSummand {n : ℕ} (p : n.Partition) (α : ℂ) :
    Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) =
      cC α n - cCount α n p := by
  have hmap :
      (hSummand p).map (algebraMap ℚ ℂ)
        = ∏ i ∈ Finset.Icc 1 n,
            ((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i) := by
    unfold hSummand
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [Polynomial.map_pow, map_one_add_X_pow]
  rw [hmap]
  have hne : ∀ i ∈ Finset.Icc 1 n,
      (((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i)) ≠ 0 := by
    intro i _
    exact pow_ne_zero _ (one_add_X_pow_ne_zero_complex i)
  rw [rootMultiplicity_prod (Finset.Icc 1 n)
        (fun i => ((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i)) α hne]
  have hstep :
      ∀ i ∈ Finset.Icc 1 n,
        Polynomial.rootMultiplicity α
            (((1 : Polynomial ℂ) + Polynomial.X ^ i) ^ (n / i - p.mult i))
          = (n / i - p.mult i)
              * (if α ^ i = -1 then 1 else 0) := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [rootMultiplicity_pow _ _ _ (one_add_X_pow_ne_zero_complex i),
        rootMultiplicity_one_add_X_pow_complex α i hi1]
  rw [Finset.sum_congr rfl hstep]
  have hrestrict :
      (∑ i ∈ Finset.Icc 1 n,
          (n / i - p.mult i) * (if α ^ i = -1 then 1 else 0))
        = ∑ i ∈ badSet α n, (n / i - p.mult i) := by
    rw [badSet]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i _
    split_ifs <;> simp
  rw [hrestrict]
  have hbound : ∀ i ∈ badSet α n, p.mult i ≤ n / i := by
    intro i _
    exact mult_le_div p i
  rw [show (∑ i ∈ badSet α n, (n / i - p.mult i))
        = (∑ i ∈ badSet α n, n / i) - (∑ i ∈ badSet α n, p.mult i) from
      (finset_sum_sub_distrib_of_le (badSet α n) (fun i => n / i) (fun i => p.mult i) hbound).symm]
  rfl

/-- For α of exact order `2s` with `α^i = -1` for some `1 ≤ i ≤ n`, and for any
partition `p ⊢ n`, every `j ∈ badSet α n` is ≥ `s`. Therefore
`cCount α n p * s ≤ n`, i.e. `cCount α n p ≤ n / s = M`. -/
lemma s_le_of_pow_eq_neg_one {α : ℂ} {s : ℕ} (_hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    {j : ℕ} (hj : 1 ≤ j) (hpow : α ^ j = -1) : s ≤ j := by
  by_contra h
  have h₂ : 2 * j < 2 * s := by
    omega
  have h₃ : α ^ (2 * j) = 1 := by
    calc
      α ^ (2 * j) = (α ^ j) ^ 2 := by
        calc
          α ^ (2 * j) = α ^ (j + j) := by ring_nf
          _ = (α ^ j) * (α ^ j) := by rw [pow_add]
          _ = (α ^ j) ^ 2 := by ring_nf
      _ = (-1 : ℂ) ^ 2 := by rw [hpow]
      _ = 1 := by norm_num
  have h₄ : 2 * j = 0 := by
    apply hord.2
    · exact h₂
    · exact h₃
  omega

lemma cCount_le_M {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (p : n.Partition) :
    cCount α n p ≤ n / s := by
  rw [Nat.le_div_iff_mul_le hs]
  have h_badSet_subset : badSet α n ⊆ Finset.Icc 1 n := by
    intro j hj
    simp [badSet, Finset.mem_filter] at hj
    exact Finset.mem_Icc.mpr ⟨hj.1.1, hj.1.2⟩
  have h_s_le : ∀ j ∈ badSet α n, s ≤ j := by
    intro j hj
    simp [badSet, Finset.mem_filter, Finset.mem_Icc] at hj
    exact s_le_of_pow_eq_neg_one hs hord hj.1.1 hj.2
  calc cCount α n p * s
      = (∑ j ∈ badSet α n, p.mult j) * s := by rfl
    _ = ∑ j ∈ badSet α n, p.mult j * s := by rw [Finset.sum_mul]
    _ = ∑ j ∈ badSet α n, s * p.mult j := by
          apply Finset.sum_congr rfl; intros; ring
    _ ≤ ∑ j ∈ badSet α n, j * p.mult j := by
          apply Finset.sum_le_sum
          intro j hj
          exact Nat.mul_le_mul_right _ (h_s_le j hj)
    _ ≤ ∑ i ∈ Finset.Icc 1 n, i * p.mult i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_badSet_subset
          intros; exact Nat.zero_le _
    _ = n := sum_mult_eq_n p

/-- If `α^(2s) = 1` and the only `k < 2s` with `α^k = 1` is `k = 0`, then `α^s = -1`. -/
lemma pow_s_eq_neg_one {α : ℂ} {s : ℕ} (hs : 1 ≤ s)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    α ^ s = -1 := by
  have h3 : α ^ s = 1 ∨ α ^ s = -1 := by
    have h4 : (α ^ s) ^ 2 = 1 := by
      calc
        (α ^ s) ^ 2 = α ^ (2 * s) := by
          rw [← pow_mul]
          ring_nf
        _ = 1 := h1
    have h5 : α ^ s = 1 ∨ α ^ s = -1 := by
      have h6 : (α ^ s - 1) * (α ^ s + 1) = 0 := by
        calc
          (α ^ s - 1) * (α ^ s + 1) = (α ^ s) ^ 2 - 1 := by
            ring_nf
          _ = 0 := by
            rw [h4]
            simp [sub_self]
      have h7 : α ^ s - 1 = 0 ∨ α ^ s + 1 = 0 := by
        simpa [sub_eq_zero, add_eq_zero_iff_eq_neg] using eq_zero_or_eq_zero_of_mul_eq_zero h6
      cases h7 with
      | inl h7 =>
        have h8 : α ^ s = 1 := by
          have h9 : α ^ s - 1 = 0 := h7
          have h10 : α ^ s = 1 := by
            rw [sub_eq_zero] at h9
            exact h9
          exact h10
        exact Or.inl h8
      | inr h7 =>
        have h8 : α ^ s = -1 := by
          have h9 : α ^ s + 1 = 0 := h7
          have h10 : α ^ s = -1 := by
            rw [add_eq_zero_iff_eq_neg] at h9
            exact h9
          exact h10
        exact Or.inr h8
    exact h5
  cases h3 with
  | inl h3 =>
    have h4 : s = 0 := by
      have h6 : s < 2 * s := by
        have h8 : s < 2 * s := by
          nlinarith
        exact h8
      have h9 : s = 0 := by
        have h10 : α ^ s = 1 := h3
        have h11 : s < 2 * s := h6
        have h12 : s = 0 := by
          have h13 := h2 s h11 h10
          exact h13
        exact h12
      exact h9
    have h10 : s ≠ 0 := by
      omega
    contradiction
  | inr h3 =>
    exact h3

/-- For `α` of exact order `2s` with `1 ≤ s ≤ n`, the index `s` belongs to `badSet α n`. -/
lemma s_mem_badSet {α : ℂ} {n s : ℕ} (hs : 1 ≤ s) (hsn : s ≤ n)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0) :
    s ∈ badSet α n := by
  unfold badSet
  rw [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hs, hsn⟩, pow_s_eq_neg_one hs h1 h2⟩

/-- Main computation for the constructed partition. -/
lemma cCount_constructed_eq_M (α : ℂ) (s n M r : ℕ)
    (l : Multiset ℕ) (hsum : l.sum = n)
    (hs : 1 ≤ s) (hsn : s ≤ n)
    (h1 : α ^ (2 * s) = 1) (h2 : ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hr : r < s) (_hM_eq : M = n / s)
    (hl : l = Multiset.replicate M s + {r}) :
    cCount α n (Nat.Partition.ofSums n l hsum) = n / s := by
  unfold cCount Nat.Partition.mult
  have hpos : ∀ j ∈ badSet α n, j ≠ 0 := by
    intro j hj
    unfold badSet at hj
    rw [Finset.mem_filter, Finset.mem_Icc] at hj
    omega
  have step1 : ∀ j ∈ badSet α n,
      Multiset.count j (Nat.Partition.ofSums n l hsum).parts = Multiset.count j l := by
    intro j hj
    exact Nat.Partition.count_ofSums_of_ne_zero hsum (hpos j hj)
  rw [Finset.sum_congr rfl step1]
  have hsmem : s ∈ badSet α n := s_mem_badSet hs hsn h1 h2
  have key : ∑ j ∈ badSet α n, Multiset.count j l = Multiset.count s l := by
    refine Finset.sum_eq_single s ?_ ?_
    · intro j hj hjs
      rw [hl, Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton]
      have hjr : j ≠ r := by
        unfold badSet at hj
        rw [Finset.mem_filter, Finset.mem_Icc] at hj
        obtain ⟨⟨hj1, _⟩, hjpow⟩ := hj
        have hsj : s ≤ j := s_le_of_pow_eq_neg_one hs ⟨h1, h2⟩ hj1 hjpow
        have hsj' : s < j := lt_of_le_of_ne hsj (Ne.symm hjs)
        omega
      have hsne : s ≠ j := Ne.symm hjs
      rw [if_neg hsne, if_neg hjr]
      rfl
    · intro h; exact absurd hsmem h
  rw [key]
  rw [hl, Multiset.count_add, Multiset.count_replicate, Multiset.count_singleton]
  have hsr : s ≠ r := by omega
  rw [if_pos rfl, if_neg hsr]
  omega

/-- The maximum value `M = ⌊n/s⌋` is achieved: take a partition consisting of `M`
parts equal to `s` together with any partition of the remainder `r = n - M*s`. -/
lemma exists_partition_cCount_eq_M {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    ∃ p : n.Partition, cCount α n p = n / s := by
  obtain ⟨h1, h2⟩ := hord
  set M : ℕ := n / s with hMdef
  set r : ℕ := n - M * s with hrdef
  let l : Multiset ℕ := Multiset.replicate M s + {r}
  have hMs_le : M * s ≤ n := by
    rw [hMdef]; exact Nat.div_mul_le_self n s
  have hsum : l.sum = n := by
    simp [l, Multiset.sum_replicate]
    rw [hrdef]
    omega
  have hr_lt : r < s := by
    have hspos : 0 < s := hs
    have hmod : n % s < s := Nat.mod_lt _ hspos
    have hreq : r = n % s := by
      rw [hrdef, hMdef, Nat.sub_eq_iff_eq_add (Nat.div_mul_le_self n s)]
      rw [add_comm]
      exact (Nat.div_add_mod n s).symm.trans (by ring_nf)
    rw [hreq]; exact hmod
  refine ⟨Nat.Partition.ofSums n l hsum, ?_⟩
  exact cCount_constructed_eq_M α s n M r l hsum hs hsn h1 h2 hr_lt hMdef rfl

/-- The mapped `gCommon n` divides the mapped `hSummand p` in `ℂ[X]`. -/
lemma gCommon_map_dvd_hSummand_map {n : ℕ} (p : n.Partition) :
    (gCommon n).map (algebraMap ℚ ℂ) ∣ (hSummand p).map (algebraMap ℚ ℂ) :=
  Polynomial.map_dvd _ (gCommon_dvd_hSummand p)

/-- The mapped polynomial `(hSummand p).map (algebraMap ℚ ℂ)` is non-zero. -/
lemma hSummand_map_ne_zero {n : ℕ} (p : n.Partition) :
    (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := by
  have h : hSummand p ≠ 0 := hSummand_ne_zero p
  intro hcontra
  apply h
  have hinj : Function.Injective (algebraMap ℚ ℂ) :=
    (algebraMap ℚ ℂ).injective
  exact (Polynomial.map_eq_zero_iff hinj).mp hcontra

/-- For `n ≥ 1`, the mapped `gCommon n` is non-zero. -/
lemma gCommon_map_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := by
  have h : gCommon n ≠ 0 := gCommon_ne_zero n hn
  intro hcontra
  apply h
  have hinj : Function.Injective (algebraMap ℚ ℂ) :=
    (algebraMap ℚ ℂ).injective
  exact (Polynomial.map_eq_zero_iff hinj).mp hcontra

/-- Upper bound: the root multiplicity of the mapped `gCommon n` at `α` is at most
the root multiplicity of the mapped `hSummand p` at `α`, for any partition `p`. -/
lemma rootMultiplicity_gCommon_le {n : ℕ} (p : n.Partition) (α : ℂ) (hn : 1 ≤ n) :
    Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) ≤
      Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ)) := by
  have _hG : (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := gCommon_map_ne_zero n hn
  have hH : (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := hSummand_map_ne_zero p
  have hdvd : (gCommon n).map (algebraMap ℚ ℂ) ∣ (hSummand p).map (algebraMap ℚ ℂ) :=
    gCommon_map_dvd_hSummand_map p
  have h1 : (Polynomial.X - Polynomial.C α) ^
      (Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ))) ∣
      (gCommon n).map (algebraMap ℚ ℂ) := Polynomial.pow_rootMultiplicity_dvd _ _
  have h2 : (Polynomial.X - Polynomial.C α) ^
      (Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ))) ∣
      (hSummand p).map (algebraMap ℚ ℂ) := dvd_trans h1 hdvd
  exact (Polynomial.le_rootMultiplicity_iff hH).mpr h2

/-- Key computational lemma: for a nonzero polynomial `q : ℚ[X]`, we have
`normalize q = C (leadingCoeff q)⁻¹ * q`. -/
lemma normalize_polynomial_rat_eq (q : Polynomial ℚ) (hq : q ≠ 0) :
    normalize q = Polynomial.C (q.leadingCoeff)⁻¹ * q := by
  rw [normalize_apply, Polynomial.coe_normUnit_of_ne_zero hq, mul_comm]

/-- Singleton base case for the linear-combination form of `Finset.gcd`. -/
lemma finset_gcd_lc_singleton {β : Type*} [DecidableEq β]
    (f : β → Polynomial ℚ) (b : β) (hb : f b ≠ 0) :
    ∃ a : β → Polynomial ℚ, ({b} : Finset β).gcd f = ∑ c ∈ ({b} : Finset β), a c * f c := by
  refine ⟨fun c => if c = b then Polynomial.C (f b).leadingCoeff⁻¹ else 0, ?_⟩
  rw [Finset.gcd_singleton, Finset.sum_singleton]
  simp only [↓reduceIte]
  exact normalize_polynomial_rat_eq (f b) hb

/-- Bezout identity for the normalized `gcd` in `Polynomial ℚ`. -/
lemma gcd_eq_linear_combination_poly (x y : Polynomial ℚ) :
    ∃ A B : Polynomial ℚ, gcd x y = A * x + B * y := by
  obtain ⟨a, b, hab⟩ := IsBezout.gcd_eq_sum x y
  obtain ⟨u, hu⟩ := IsBezout.associated_gcd_gcd (R := Polynomial ℚ) (x := x) (y := y)
  refine ⟨a * u, b * u, ?_⟩
  rw [← hu, ← hab]
  ring

/-- Inductive step for linear-combination form of `Finset.gcd`. -/
lemma finset_gcd_lc_insert {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → Polynomial ℚ) (b : β) (hb : b ∉ s)
    (_hfb : f b ≠ 0)
    (ih : ∃ a : β → Polynomial ℚ, s.gcd f = ∑ c ∈ s, a c * f c) :
    ∃ a : β → Polynomial ℚ, (insert b s).gcd f = ∑ c ∈ insert b s, a c * f c := by
  obtain ⟨a0, ha0⟩ := ih
  obtain ⟨A, B, hAB⟩ := gcd_eq_linear_combination_poly (f b) (s.gcd f)
  classical
  refine ⟨fun c => if c = b then A else B * a0 c, ?_⟩
  rw [Finset.sum_insert hb]
  simp only [if_true]
  have hsum : ∑ c ∈ s, (if c = b then A else B * a0 c) * f c
      = ∑ c ∈ s, (B * a0 c) * f c := by
    apply Finset.sum_congr rfl
    intro c hc
    have : c ≠ b := fun h => hb (h ▸ hc)
    simp [this]
  rw [hsum]
  have hBsum : ∑ c ∈ s, (B * a0 c) * f c = B * s.gcd f := by
    rw [ha0, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hBsum]
  rw [← hAB]
  exact Finset.gcd_insert

/-- Linear combination form of `Finset.gcd` over `Polynomial ℚ`. -/
lemma finset_gcd_eq_linear_combination {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → Polynomial ℚ) (hs : s.Nonempty)
    (hf : ∀ b ∈ s, f b ≠ 0) :
    ∃ a : β → Polynomial ℚ, s.gcd f = ∑ c ∈ s, a c * f c := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
      have hfa : f a ≠ 0 := hf a (by simp)
      exact finset_gcd_lc_singleton f a hfa
  | cons a t ha _ht ih =>
      have hft : ∀ b ∈ t, f b ≠ 0 := fun b hbt => hf b (by
        rw [Finset.cons_eq_insert]; exact Finset.mem_insert_of_mem hbt)
      have hfa : f a ≠ 0 := hf a (by
        rw [Finset.cons_eq_insert]; exact Finset.mem_insert_self _ _)
      have ih' := ih hft
      rw [Finset.cons_eq_insert]
      exact finset_gcd_lc_insert t f a ha hfa ih'

/-- Lower bound: if every `hSummand p` has multiplicity ≥ m at α, then so does `gCommon n`. -/
lemma rootMultiplicity_gCommon_ge {n : ℕ} (α : ℂ) (hn : 1 ≤ n) (m : ℕ)
    (hm : ∀ p : n.Partition, m ≤
      Polynomial.rootMultiplicity α ((hSummand p).map (algebraMap ℚ ℂ))) :
    m ≤ Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) := by
  have hG : (gCommon n).map (algebraMap ℚ ℂ) ≠ 0 := gCommon_map_ne_zero n hn
  rw [Polynomial.le_rootMultiplicity_iff hG]
  have hne : (Finset.univ : Finset n.Partition).Nonempty := by
    refine ⟨default, Finset.mem_univ _⟩
  have hfne : ∀ p ∈ (Finset.univ : Finset n.Partition), hSummand p ≠ 0 := fun p _ =>
    hSummand_ne_zero p
  obtain ⟨a, ha⟩ := finset_gcd_eq_linear_combination Finset.univ hSummand hne hfne
  have h_eq : (gCommon n).map (algebraMap ℚ ℂ) =
      ∑ p ∈ (Finset.univ : Finset n.Partition),
        (a p).map (algebraMap ℚ ℂ) * (hSummand p).map (algebraMap ℚ ℂ) := by
    unfold gCommon
    rw [ha]
    simp [Polynomial.map_sum, Polynomial.map_mul]
  rw [h_eq]
  apply Finset.dvd_sum
  intro p _
  have hH : (hSummand p).map (algebraMap ℚ ℂ) ≠ 0 := hSummand_map_ne_zero p
  have hdvd : (Polynomial.X - Polynomial.C α) ^ m ∣ (hSummand p).map (algebraMap ℚ ℂ) :=
    (Polynomial.le_rootMultiplicity_iff hH).mp (hm p)
  exact Dvd.dvd.mul_left hdvd _

/-- The vanishing order of `gCommon n` at `α` is `cC α n - n / s` (= C - M).
Since `gCommon n = gcd_{p} hSummand p`, its `rootMultiplicity` at `α` is the min
over partitions of `rootMultiplicity` of `hSummand p` at `α`, which equals
`cC α n - max_{p} cCount α n p = cC α n - n/s` (using `cCount_le_M` and
`exists_partition_cCount_eq_M`). -/
lemma rootMultiplicity_gCommon {n : ℕ} (α : ℂ) (s : ℕ) (hs : 1 ≤ s)
    (hord : α ^ (2 * s) = 1 ∧ ∀ k : ℕ, k < 2 * s → α ^ k = 1 → k = 0)
    (hsn : s ≤ n) :
    Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) =
      cC α n - n / s := by
  have hn : 1 ≤ n := le_trans hs hsn
  apply le_antisymm
  · obtain ⟨p₀, hp₀⟩ := exists_partition_cCount_eq_M α s hs hord hsn
    have h1 : Polynomial.rootMultiplicity α ((gCommon n).map (algebraMap ℚ ℂ)) ≤
        Polynomial.rootMultiplicity α ((hSummand p₀).map (algebraMap ℚ ℂ)) :=
      rootMultiplicity_gCommon_le p₀ α hn
    rw [rootMultiplicity_hSummand p₀ α, hp₀] at h1
    exact h1
  · apply rootMultiplicity_gCommon_ge α hn
    intro p
    rw [rootMultiplicity_hSummand p α]
    have hp_le : cCount α n p ≤ n / s := cCount_le_M α s hs hord p
    exact Nat.sub_le_sub_left hp_le _


end
#print axioms rootMultiplicity_gCommon
