import BBFM.Denominator.Analytic.Edge

noncomputable section
namespace BBFMRefined
open Finset

/-- Comparing first-order approximations to adjacent normalized ratios.
The cubic condition improves the old elementary quadratic-index bound. -/
theorem ratio_comparison (r s k u v : ℝ) (hk : 1 ≤ k) (hr : 0 < r)
    (hs : 0 ≤ s) (hsr : s ≤ r) (hsize : 10000*k^3 ≤ r^2)
    (hlow : r-k ≤ u)
    (hu : |r*u-(r^2-r*(k-1)+2*s*(k-1))| ≤ 1000*(k-1)^2)
    (hv : |r*v-(r^2-r*k+2*s*k)| ≤ 1000*k^2) :
    k*v ≤ (k+1)*u := by
  have hk0 : 0 ≤ k := by linarith
  have hk2 : k^2 ≤ k^3 := by nlinarith [sq_nonneg (k-1)]
  have hrk : 10*k ≤ r := by
    by_contra hh
    have hh' : r < 10*k := lt_of_not_ge hh
    have hh2 : r^2 < (10*k)^2 := (sq_lt_sq₀ hr.le (by positivity)).2 hh'
    nlinarith
  have hkr := mul_le_mul_of_nonneg_left hrk hr.le
  have hua := (abs_le.mp hu).1
  have hva := (abs_le.mp hv).2
  have hd : r*(v-u) ≤ r+2000*k^2 := by nlinarith
  have hd' := mul_le_mul_of_nonneg_left hd hk0
  have hlow' := mul_le_mul_of_nonneg_left hlow hr.le
  have hf : r*(k*v-(k+1)*u) ≤ 0 := by nlinarith
  by_contra hh
  have hp : 0 < r*(k*v-(k+1)*u) := mul_pos hr (by linarith)
  linarith

/-- A two-sided rough ratio bound controls its reciprocal to first order. -/
theorem reciprocal_ratio_error (r j z : ℝ) (hr : 0 < r) (hj : 0 ≤ j)
    (hjr : 2*j ≤ r) (hzl : r-j ≤ z) (hzu : z ≤ r+8*j) :
    |r*(j/z)-j| ≤ 16*j^2/r := by
  have hz : 0 < z := by linarith
  rw [show r*(j/z)-j = j*(r-z)/z by field_simp]
  rw [abs_div, abs_mul, abs_of_nonneg hj, abs_of_pos hz]
  have hab : |r-z| ≤ 8*j := by rw [abs_le]; constructor <;> linarith
  apply (div_le_iff₀ hz).2
  have h1 := mul_le_mul_of_nonneg_left hab hj
  have h2 := mul_le_mul_of_nonneg_left (show r/2 ≤ z by linarith)
    (show 0 ≤ 16*j^2/r by positivity)
  have he : (16*j^2/r)*(r/2) = 8*j^2 := by field_simp; ring
  rw [he] at h2
  nlinarith

/-- An isolated quadratic factor plus a cubic-order tail gives a first-order
approximation to the normalized coefficient ratio. -/
theorem normalized_ratio_error (r s j a b c d : ℝ)
    (hr : 0 < r) (hs : 0 ≤ s) (hsr : s ≤ r) (hj : 0 < j)
    (hjr : 2*j ≤ r) (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hl : r-j ≤ j*a/b) (hu : j*a/b ≤ r+8*j)
    (hba : r*b ≤ 2*j*a) (hcb : r*c ≤ 2*j*b)
    (he : |(j+1)*d-(r-j)*a-2*s*b| ≤ 16*r*c) :
    |r*((j+1)*d/a)-(r^2-r*j+2*s*j)| ≤ 1000*j^2 := by
  have herr := reciprocal_ratio_error r j (j*a/b) hr hj.le hjr hl hu
  have hid : j/(j*a/b) = b/a := by field_simp
  rw [hid] at herr
  have hca : r^2*c ≤ 4*j^2*a := by
    have h1 := mul_le_mul_of_nonneg_left hcb hr.le
    have h2 := mul_le_mul_of_nonneg_left hba (show 0 ≤ 2*j by positivity)
    nlinarith
  have hfirst : (r/a)*(16*r*c) ≤ 64*j^2 := by
    calc
      _ = 16*r^2*c/a := by ring
      _ ≤ 64*j^2 := (div_le_iff₀ ha).2 (by nlinarith [hca])
  have hsecond : (2*s)*(16*j^2/r) ≤ 32*j^2 := by
    have h := mul_le_mul_of_nonneg_right hsr (show 0 ≤ 32*j^2/r by positivity)
    have hid2 : r*(32*j^2/r) = 32*j^2 := by field_simp
    rw [hid2] at h
    calc
      _ = s*(32*j^2/r) := by ring
      _ ≤ 32*j^2 := h
  have hid3 : r*((j+1)*d/a)-(r^2-r*j+2*s*j) =
      (r/a)*((j+1)*d-(r-j)*a-2*s*b)+2*s*(r*(b/a)-j) := by field_simp; ring
  rw [hid3]
  calc
    _ ≤ |(r/a)*((j+1)*d-(r-j)*a-2*s*b)|+|2*s*(r*(b/a)-j)| := abs_add_le _ _
    _ = (r/a)*|(j+1)*d-(r-j)*a-2*s*b|+(2*s)*|r*(b/a)-j| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by positivity : 0 ≤ r/a),
        abs_of_nonneg (by positivity : 0 ≤ 2*s)]
    _ ≤ (r/a)*(16*r*c)+(2*s)*(16*j^2/r) :=
      add_le_add (mul_le_mul_of_nonneg_left he (by positivity))
        (mul_le_mul_of_nonneg_left herr (by positivity))
    _ ≤ 1000*j^2 := by nlinarith [sq_nonneg j]

#print axioms ratio_comparison
#print axioms reciprocal_ratio_error
#print axioms normalized_ratio_error
end BBFMRefined
