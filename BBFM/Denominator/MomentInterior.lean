import BBFM.Denominator.MomentSaddles
import BBFM.Denominator.RefinedInterior

/-! First-moment coverage and reflection for the denominator interior. -/
noncomputable section
namespace BBFMMoment
open Finset Polynomial Real DenominatorResearch

/-- Uniform in n: every sufficiently distant lower-half coefficient is
strictly log-concave. This has no lower bound on log n. -/
theorem den_lower_interior_strict (n k : ℕ) (hn : 0 < n)
    (hbig : 6*(12*(10 : ℕ)^6)^2 ≤ k)
    (hmid : 2*k ≤ (den n).natDegree) :
    (den n).coeff (k-1)*(den n).coeff (k+1) < (den n).coeff k^2 := by
  have hk : 1 ≤ k := by norm_num at hbig; omega
  have hmidR : (k : ℝ) ≤ ((den n).natDegree : ℝ)/2 := by
    have hh : 2*(k : ℝ) ≤ ((den n).natDegree : ℝ) := by exact_mod_cast hmid
    linarith
  obtain ⟨r,hr,hrone,hmean⟩ := den_exists_saddle_radius n k
    (by exact_mod_cast (show 0 < k by omega)) hmidR
  have hkd : k+1 ≤ (den n).natDegree := by omega
  have hbigR : 6*(12*(10 : ℝ)^6)^2 ≤ (k : ℝ) := by exact_mod_cast hbig
  by_cases hrhalf : r ≤ 1/2
  · have hp := den_small_radius_parameters n r hn hr.le hrhalf
    dsimp only at hp
    rw [hmean] at hp
    have hN : 12*(10 : ℝ)^6 ≤ 14*(((Nat.log 2 n+1 : ℕ) : ℝ)*r) := by linarith [hp.1]
    exact BBFMMoment.den_logconcave_of_small_saddle n k r hn hk hkd hr hrhalf hmean hN
  · have hrlarge : 1/2 < r := lt_of_not_ge hrhalf
    have hp := BBFMRefined.den_large_radius_mean_le_size_square n r hn hrlarge hrone
    rw [hmean] at hp
    let N : ℝ := (1+Real.logb 2 ((n : ℝ)/effectiveScale n r))*effectiveScale n r
    have hN0 : 0 ≤ N := by
      obtain ⟨hL,hLn,_⟩ := effectiveScale_bounds n r hn hrlarge hrone
      have hLp : 0 < effectiveScale n r := by linarith
      have hrat : (1 : ℝ) ≤ (n : ℝ)/effectiveScale n r := (le_div_iff₀ hLp).2 (by simpa using hLn)
      have hm := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hrat
      dsimp [N]
      positivity
    have hN : 12*(10 : ℝ)^6 ≤ N := by
      apply (sq_le_sq₀ (by positivity) hN0).mp
      change _ ≤ N^2
      change (k : ℝ) ≤ 6*N^2 at hp
      nlinarith only [hbigR,hp]
    exact BBFMMoment.den_logconcave_of_large_saddle n k r hn hk hkd hrlarge hrone hmean hN

/-- An absolute edge width suffices for every n. No exceptional small n can
violate this statement because the index must lie this far from both ends. -/
theorem den_interior_strict (n k : ℕ) (hn : 0 < n)
    (hleft : 6*(12*(10 : ℕ)^6)^2 ≤ k)
    (hright : 6*(12*(10 : ℕ)^6)^2 ≤ (den n).natDegree-k) :
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

#print axioms BBFMMoment.den_interior_strict
end BBFMMoment
