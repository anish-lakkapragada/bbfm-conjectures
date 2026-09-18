import BBFM.Denominator.DyadicKernelPairing

/-! Source-specific signs of the logarithmic-derivative kernel, using
the dyadic exponent identity to prove the paired divisor inequality. -/
noncomputable section
namespace BBFMKernel
open PowerSeries Finset BBFMLinear
set_option maxHeartbeats 0

lemma source_exponent_twice (n d : ℕ) (hd : 0<d) (hdn : 2*d ≤ n) :
    Nat.log 2 (n/d)+1 = (Nat.log 2 (n/(2*d))+1)+1 := by
  have hq : 2 ≤ n/d := (Nat.le_div_iff_mul_le hd).mpr hdn
  have hp : 0 < Nat.log 2 (n/d) := Nat.log_pos (by decide) hq
  rw [show n/(2*d)=n/d/2 by rw [Nat.div_div_eq_div_mul,Nat.mul_comm d 2],Nat.log_div_base]
  omega

/-- At every odd index the source logarithmic derivative has a nonnegative kernel. -/
theorem source_logD_odd_nonnegative (n j : ℕ) (hj : Odd j) :
    0 ≤ coeff (j-1) (logD (weightedSeries (fun i => Nat.log 2 (n/i)+1) n)) :=
  weighted_logD_odd_nonnegative _ n j hj

/-- Every index congruent to two modulo four is also nonnegative, provided
it lies in the source's initial range. -/
theorem source_logD_twice_odd_nonnegative (n u : ℕ) (hu : Odd u) (hun : 2*u ≤ n) :
    0 ≤ coeff (2*u-1) (logD (weightedSeries (fun i => Nat.log 2 (n/i)+1) n)) := by
  apply weighted_logD_twice_odd_nonnegative _ n u hu hun
  intro d hd
  have hd0 := Nat.pos_of_mem_divisors hd
  have hdu := Nat.divisor_le hd
  have hd2 : 2*d ≤ n := by omega
  have he := source_exponent_twice n d hd0 hd2
  omega

/-- In the entire initial source range, a negative kernel coefficient must
come from an index divisible by four. This is not a coefficient LC claim. -/
theorem source_logD_nonnegative_of_not_four_dvd (n j : ℕ)
    (hj : 1≤j) (hjn : j≤n) (hfour : ¬4∣j) :
    0 ≤ coeff (j-1) (logD (weightedSeries (fun i => Nat.log 2 (n/i)+1) n)) := by
  by_cases he : Even j
  · obtain ⟨u,hu⟩ := he
    have hju : j=2*u := by omega
    have hou : Odd u := by
      apply Nat.not_even_iff_odd.mp
      rintro ⟨v,hv⟩
      apply hfour
      exact ⟨v,by omega⟩
    rw [hju]
    exact source_logD_twice_odd_nonnegative n u hou (by omega)
  · exact source_logD_odd_nonnegative n j (Nat.not_even_iff_odd.mp he)

#print axioms source_logD_twice_odd_nonnegative
#print axioms source_logD_nonnegative_of_not_four_dvd
end BBFMKernel
