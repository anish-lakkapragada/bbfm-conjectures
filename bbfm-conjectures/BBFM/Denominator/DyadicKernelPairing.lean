import BBFM.Denominator.DyadicLogKernel
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Prime.Basic

/-! Exact pairing of the first even dyadic stratum. These identities isolate
cancellation in the source recurrence; they do not assume or establish LC. -/
noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear
set_option maxHeartbeats 0

lemma weighted_logD_divisors (m : ℕ → ℕ) (n j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n) :
    coeff (j-1) (logD (weightedSeries m n)) =
      ∑ i ∈ j.divisors, (m i : ℝ)*i*(-1 : ℝ)^(j/i-1) := by
  rw [weighted_logD_divisor_sum m n j hj]
  have he : (∑ i ∈ range n, if i+1 ∣ j then
      (m (i+1) : ℝ)*(i+1)*(-1 : ℝ)^(j/(i+1)-1) else 0) =
      ∑ i ∈ range j, if i+1 ∣ j then
      (m (i+1) : ℝ)*(i+1)*(-1 : ℝ)^(j/(i+1)-1) else 0 := by
    symm
    apply sum_subset (range_mono hjn)
    intro i hin hij
    have hij' : ¬i+1 ∣ j := by
      intro hd
      have := Nat.le_of_dvd (by omega : 0<j) hd
      simp only [mem_range] at hij
      omega
    simp [hij']
  rw [he,Nat.divisors,sum_filter,Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

lemma divisors_twice_odd (u : ℕ) (hu : Odd u) :
    (2*u).divisors = u.divisors ∪ u.divisors.image (fun d => 2*d) := by
  ext d
  simp only [Nat.mem_divisors,mem_union,mem_image]
  have hu0 : u ≠ 0 := by have := hu.pos; omega
  constructor
  · intro ⟨hd,hne⟩
    by_cases he : Even d
    · obtain ⟨e,he⟩ := he
      have hde : d=2*e := by omega
      rw [hde] at hd ⊢
      right
      refine ⟨e,⟨?_,hu0⟩,rfl⟩
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0<2)).mp hd
    · left
      exact ⟨(Nat.coprime_two_right.mpr (Nat.not_even_iff_odd.mp he)).dvd_mul_left.mp hd,hu0⟩
  · rintro (⟨hd,hne⟩ | ⟨e,⟨he,hne⟩,rfl⟩)
    · exact ⟨hd.trans (dvd_mul_left u 2),by omega⟩
    · exact ⟨Nat.mul_dvd_mul_left 2 he,by omega⟩

lemma divisors_twice_odd_disjoint (u : ℕ) (hu : Odd u) :
    Disjoint u.divisors (u.divisors.image (fun d => 2*d)) := by
  rw [disjoint_left]
  intro d hd he
  obtain ⟨e,he,rfl⟩ := mem_image.mp he
  have hod : Odd (2*e) := hu.of_dvd_nat (Nat.mem_divisors.mp hd).1
  have hev : Even (2*e) := ⟨e,by omega⟩
  obtain ⟨a,ha⟩ := hod
  obtain ⟨b,hb⟩ := hev
  omega

/-- The exact paired kernel on indices congruent to two modulo four. -/
theorem weighted_logD_twice_odd (m : ℕ → ℕ) (n u : ℕ) (hu : Odd u)
    (hun : 2*u ≤ n) :
    coeff (2*u-1) (logD (weightedSeries m n)) =
      ∑ d ∈ u.divisors, (d : ℝ)*(2*(m (2*d) : ℝ)-m d) := by
  have hu0 := hu.pos
  rw [weighted_logD_divisors m n (2*u) (by omega) hun,
    divisors_twice_odd u hu,sum_union (divisors_twice_odd_disjoint u hu),sum_image]
  · rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    have hdu := (Nat.mem_divisors.mp hd).1
    have hd0 := Nat.pos_of_mem_divisors hd
    have ho : Odd (u/d) := hu.of_dvd_nat (Nat.div_dvd_of_dvd hdu)
    have hdquot : 2*u/d=2*(u/d) := Nat.mul_div_assoc 2 hdu
    have hdquot2 : 2*u/(2*d)=u/d := Nat.mul_div_mul_left u d (by decide : 0<2)
    rw [hdquot,hdquot2]
    have hex : Odd (2*(u/d)-1) := by
      obtain ⟨t,ht⟩ := ho
      refine ⟨2*t,?_⟩
      omega
    have hev : Even (u/d-1) := by
      obtain ⟨t,ht⟩ := ho
      exact ⟨t,by omega⟩
    rw [hex.neg_one_pow,hev.neg_one_pow]
    push_cast
    ring
  · intro a ha b hb hab
    dsimp at hab
    omega

theorem weighted_logD_twice_odd_nonnegative (m : ℕ → ℕ) (n u : ℕ) (hu : Odd u)
    (hun : 2*u ≤ n) (hm : ∀ d ∈ u.divisors, m d ≤ 2*m (2*d)) :
    0 ≤ coeff (2*u-1) (logD (weightedSeries m n)) := by
  rw [weighted_logD_twice_odd m n u hu hun]
  apply sum_nonneg
  intro d hd
  apply mul_nonneg (by positivity)
  have hh : (m d : ℝ) ≤ 2*m (2*d) := by exact_mod_cast hm d hd
  linarith

#print axioms weighted_logD_twice_odd
#print axioms weighted_logD_twice_odd_nonnegative
end BBFMKernel
