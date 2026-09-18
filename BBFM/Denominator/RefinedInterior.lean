import BBFM.Denominator.RefinedEventual

noncomputable section
namespace BBFMRefined
open Finset Polynomial Real DenominatorResearch

/-- A first-moment estimate controlling the saddle coefficient index by the square of effective size. -/
theorem den_large_radius_mean (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1/2 < r) (hrone : r ≤ 1) :
    let L := effectiveScale n r
    let M := 1+Real.logb 2 ((n : ℝ)/L)
    tiltedMean (fun i => Nat.log 2 (n/i)+1) n r ≤ 6*M*L^2 := by
  dsimp only
  let L := effectiveScale n r
  let M := 1+Real.logb 2 ((n : ℝ)/L)
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨hL,hLn,_⟩ := effectiveScale_bounds n r hn hr hrone
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hM : 1 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ)/L := (le_div_iff₀ hL0).2 (by simpa using hLn)
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  apply (tiltedMean_le_moment (fun i => Nat.log 2 (n/i)+1) n r hr0).trans
  change _ ≤ 6*M*L^2
  by_cases heq : L = (n : ℝ)
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hMeq : M = 1 := by simp [M,heq,div_self hn0.ne']
    rw [heq,hMeq]
    have hh := den_global_moment_bound n 0 r hr0 hrone
    norm_num at hh
    nlinarith [sq_nonneg (n : ℝ)]
  · have hunsat := effectiveScale_unsaturated n r hr hrone heq
    have hgap := effectiveScale_geometric_gap n r hn hr hrone heq
    have hnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hr0] using hunsat.1
    have hgeom := geometric_moments_effective r L hr0 hunsat.1 hL0.le hgap
    have hfirst := den_moment_le_profile_sums n 0 r L _ _ hr0 hL0 hLn
      (by simpa only [Nat.zero_add,pow_one] using hasSum_coe_mul_geometric_of_norm_lt_one hnorm)
      (by simpa only [pow_zero,one_mul] using hasSum_geometric_of_norm_lt_one hnorm)
    change _ ≤ M*_+L*_ at hfirst
    have hM0 : 0 ≤ M := by linarith
    have ha := mul_le_mul_of_nonneg_left hgeom.1 hM0
    have hb := mul_le_mul_of_nonneg_left hgap hL0.le
    have hc := mul_le_mul_of_nonneg_right hM (sq_nonneg L)
    simp only [one_div] at hb
    nlinarith

theorem den_large_radius_mean_le_size_square (n : ℕ) (r : ℝ) (hn : 0 < n)
    (hr : 1/2 < r) (hrone : r ≤ 1) :
    tiltedMean (fun i => Nat.log 2 (n/i)+1) n r ≤
      6*((1+Real.logb 2 ((n : ℝ)/effectiveScale n r))*effectiveScale n r)^2 := by
  let L := effectiveScale n r
  let M := 1+Real.logb 2 ((n : ℝ)/L)
  obtain ⟨hL,hLn,_⟩ := effectiveScale_bounds n r hn hr hrone
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hM : 1 ≤ M := by
    have hrat : (1 : ℝ) ≤ (n : ℝ)/L := (le_div_iff₀ hL0).2 (by simpa using hLn)
    have hh := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
    dsimp [M]
    linarith
  have hm := den_large_radius_mean n r hn hr hrone
  change _ ≤ 6*M*L^2 at hm
  have hh := mul_le_mul_of_nonneg_right hM (show 0 ≤ M*L^2 by positivity)
  change _ ≤ 6*(M*L)^2
  nlinarith

/-- Uniform in n: every sufficiently distant lower-half coefficient is
strictly log-concave. This has no lower bound on log n. -/
theorem den_lower_interior_strict (n k : ℕ) (hn : 0 < n)
    (hbig : 6*((10 : ℕ)^28)^2 ≤ k)
    (hmid : 2*k ≤ (den n).natDegree) :
    (den n).coeff (k-1)*(den n).coeff (k+1) < (den n).coeff k^2 := by
  have hk : 1 ≤ k := by norm_num at hbig; omega
  have hmidR : (k : ℝ) ≤ ((den n).natDegree : ℝ)/2 := by
    have hh : 2*(k : ℝ) ≤ ((den n).natDegree : ℝ) := by exact_mod_cast hmid
    linarith
  obtain ⟨r,hr,hrone,hmean⟩ := den_exists_saddle_radius n k
    (by exact_mod_cast (show 0 < k by omega)) hmidR
  have hkd : k+1 ≤ (den n).natDegree := by omega
  have hbigR : 6*((10 : ℝ)^28)^2 ≤ (k : ℝ) := by exact_mod_cast hbig
  by_cases hrhalf : r ≤ 1/2
  · have hp := den_small_radius_parameters n r hn hr.le hrhalf
    dsimp only at hp
    rw [hmean] at hp
    have hN : (10 : ℝ)^28 ≤ ((Nat.log 2 n+1 : ℕ) : ℝ)*r := by linarith [hp.1]
    exact BBFMRefined.den_logconcave_of_small_saddle n k r hn hk hkd hr hrhalf hmean hN
  · have hrlarge : 1/2 < r := lt_of_not_ge hrhalf
    have hp := den_large_radius_mean_le_size_square n r hn hrlarge hrone
    rw [hmean] at hp
    let N : ℝ := (1+Real.logb 2 ((n : ℝ)/effectiveScale n r))*effectiveScale n r
    have hN0 : 0 ≤ N := by
      obtain ⟨hL,hLn,_⟩ := effectiveScale_bounds n r hn hrlarge hrone
      have hLp : 0 < effectiveScale n r := by linarith
      have hrat : (1 : ℝ) ≤ (n : ℝ)/effectiveScale n r := (le_div_iff₀ hLp).2 (by simpa using hLn)
      have hm := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
      dsimp [N]
      positivity
    have hN : (10 : ℝ)^28 ≤ N := by
      apply (sq_le_sq₀ (by positivity) hN0).mp
      change _ ≤ N^2
      change (k : ℝ) ≤ 6*N^2 at hp
      nlinarith only [hbigR,hp]
    exact BBFMRefined.den_logconcave_of_large_saddle n k r hn hk hkd hrlarge hrone hmean hN

/-- An absolute edge width suffices for every n. No exceptional small n can
violate this statement because the index must lie this far from both ends. -/
theorem den_interior_strict (n k : ℕ) (hn : 0 < n)
    (hleft : 6*((10 : ℕ)^28)^2 ≤ k)
    (hright : 6*((10 : ℕ)^28)^2 ≤ (den n).natDegree-k) :
    (den n).coeff (k-1)*(den n).coeff (k+1) < (den n).coeff k^2 := by
  have hk : 1 ≤ k := by norm_num at hleft; omega
  have hkd : k+1 ≤ (den n).natDegree := by norm_num at hright; omega
  by_cases hmid : 2*k ≤ (den n).natDegree
  · exact den_lower_interior_strict n k hn hleft hmid
  · let j := (den n).natDegree-k
    have hjmid : 2*j ≤ (den n).natDegree := by dsimp [j]; omega
    have hh := den_lower_interior_strict n j hn hright hjmid
    have hl := den_coeff_reflect n (k+1) hkd
    have hc := den_coeff_reflect n k (by omega)
    have hr := den_coeff_reflect n (k-1) (by omega)
    have hej : j-1 = (den n).natDegree-(k+1) := by dsimp [j]; omega
    have her : j+1 = (den n).natDegree-(k-1) := by dsimp [j]; omega
    rw [hej,her,hl,hr] at hh
    change _ < (den n).coeff ((den n).natDegree-k)^2 at hh
    rw [hc] at hh
    simpa only [mul_comm] using hh

#print axioms den_large_radius_mean
#print axioms den_interior_strict
end BBFMRefined
