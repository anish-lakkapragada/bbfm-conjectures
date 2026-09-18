import BBFM.Binary.LogConcavity.PowerConcavity

/-! Local algebra for the shifted negative-binomial profile recurrence.
The recurrence and binomial-mask ratio must be supplied by a separate source
bridge; this module does not assume or assert the binary conjecture. -/
namespace BinaryPowerConcavity

/-- Exact defect identity for the inhomogeneous shifted-profile recurrence. -/
theorem shifted_profile_defect_identity (p k t a b c v w : ℝ)
    (hprev : t*b=(t+p)*a+v)
    (hnext : (t+1)*c=(t+p+1)*b+w)
    (hforce : (k+1)*w=(p-k)*v) :
    (t+1)*(k+1)*((p+1)*b^2-b*(a+c)-(p-1)*a*c) =
      v*((p+1)*k*b-(p-1)*(p-k)*a) := by
  linear_combination (k+1)*p*b*hprev -
    (k+1)*(b+(p-1)*a)*hnext - (b+(p-1)*a)*hforce

/-- The simple binomial-mask ratio is enough to make the profile defect
nonnegative throughout the finite forcing range. -/
theorem shifted_profile_boundary_pc (p k t a b c v w : ℝ)
    (hp : 1 ≤ p) (hk : 0 ≤ k) (hkp : k ≤ p)
    (ha : 0 ≤ a) (hv : 0 ≤ v) (ht : 0 < t+1)
    (hprev : t*b=(t+p)*a+v)
    (hnext : (t+1)*c=(t+p+1)*b+w)
    (hforce : (k+1)*w=(p-k)*v)
    (hmask : (p+2-k)*a ≤ k*b) : PC p a b c := by
  have hratio : (p+1)*((p+2-k)*a) ≤ (p+1)*(k*b) :=
    mul_le_mul_of_nonneg_left hmask (by linarith)
  have hrem : 0 ≤ (4*p+2-2*k)*a := mul_nonneg (by linarith) ha
  have hbracket : 0 ≤ (p+1)*k*b-(p-1)*(p-k)*a := by
    nlinarith only [hratio,hrem]
  have hid := shifted_profile_defect_identity p k t a b c v w hprev hnext hforce
  unfold PC
  exact nonneg_of_mul_nonneg_right (by rw [hid]; exact mul_nonneg hv hbracket)
    (mul_pos ht (by linarith))

/-- Past the forcing support, two consecutive homogeneous recurrences give
power-concavity with equality. -/
theorem shifted_profile_homogeneous (p t a b c : ℝ) (ht : t+1 ≠ 0)
    (hprev : t*b=(t+p)*a) (hnext : (t+1)*c=(t+p+1)*b) :
    (p+1)*b^2-b*(a+c)-(p-1)*a*c=0 := by
  have hid := shifted_profile_defect_identity p 0 t a b c 0 0
    (by simpa using hprev) (by simpa using hnext) (by ring)
  simpa [ht] using hid

#print axioms shifted_profile_defect_identity
#print axioms shifted_profile_boundary_pc
#print axioms shifted_profile_homogeneous
end BinaryPowerConcavity
