import BBFM.Denominator.Analytic.Differential

noncomputable section
namespace BBFMRefined
open Polynomial Finset DenominatorResearch

lemma square_factor_derivative_identity (s : ℕ) :
    (1+X^2)*(((1+(X : ℝ[X])^2)^s).derivative) =
      C (2*(s : ℝ))*X*(1+X^2)^s := by
  cases s with
  | zero => simp
  | succ s =>
    rw [derivative_pow_succ, derivative_add, derivative_one, zero_add,
      derivative_X_pow]
    push_cast
    simp only [map_add, map_mul, map_natCast]
    rw [pow_succ (1+(X : ℝ[X])^2) s]
    ring

lemma square_factor_derivative_lower (s : ℕ) :
    CoeffLE (C (2*(s : ℝ))*X*(1+X^2)^s)
      ((((1+(X : ℝ[X])^2)^s).derivative)+
        C (2*(s : ℝ))*X^3*(1+X^2)^s) := by
  have hu := factor_derivative_upper 1 s
  have hx := coeffLE_mul_left hu (nonneg_X_pow 2)
  have hi := square_factor_derivative_identity s
  intro k
  have hh := hx k
  norm_num only [Nat.cast_one, Nat.add_one, Nat.reduceAdd] at hh
  have he := congrArg (fun P : ℝ[X] => P.coeff k) hi
  rw [add_mul,one_mul,coeff_add] at he
  change _ ≤ _
  have hid : (X^2*((1+X^2)^s*(C ((s : ℝ)*2)*X^1)) : ℝ[X]) =
      C (2*(s : ℝ))*X^3*(1+X^2)^s := by rw [mul_comm (s : ℝ) 2]; ring
  rw [hid] at hh
  rw [coeff_add]
  linarith

/-- Keep the weight-two term in the differential lower bound. -/
lemma differential_lower_second (r s : ℕ) (Q : ℝ[X]) (hQ : Nonneg Q) :
    let P : ℝ[X] := (1+X)^r*(1+X^2)^s*Q
    CoeffLE ((C (r : ℝ)+C (2*(s : ℝ))*X)*P)
      ((1+X)*P.derivative+C (2*(s : ℝ))*X^3*P) := by
  dsimp only
  let A : ℝ[X] := (1+X)^r
  let B : ℝ[X] := (1+X^2)^s
  have hA : Nonneg A := by
    simpa [A] using (nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow 1)) r)
  have hB : Nonneg B := nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow 2)) s
  have hdA : (1+X)*A.derivative = C (r : ℝ)*A := unit_derivative_identity r
  have hl := coeffLE_mul_right (square_factor_derivative_lower s) (nonneg_mul hA hQ)
  have hpos1 := nonneg_mul (nonneg_mul (nonneg_X_pow 1) hA)
    (nonneg_mul (nonneg_derivative hB) hQ)
  have hpos2 := nonneg_mul
    (nonneg_mul (nonneg_mul (nonneg_add nonneg_one (nonneg_X_pow 1)) hA) hB)
    (nonneg_derivative hQ)
  have he : (1+X)*(A*B*Q).derivative+C (2*(s : ℝ))*X^3*(A*B*Q) =
      C (r : ℝ)*(A*B*Q)+
      (B.derivative+C (2*(s : ℝ))*X^3*B)*(A*Q)+
      X*A*(B.derivative*Q)+(1+X)*A*B*Q.derivative := by
    rw [derivative_mul,derivative_mul]
    calc
      _ = ((1+X)*A.derivative)*(B*Q)+
        (B.derivative+C (2*(s : ℝ))*X^3*B)*(A*Q)+
        X*A*(B.derivative*Q)+(1+X)*A*B*Q.derivative := by ring
      _ = _ := by rw [hdA]; ring
  intro k
  change (((C (r : ℝ)+C (2*(s : ℝ))*X)*(A*B*Q)).coeff k) ≤ _
  rw [he]
  have hh := hl k
  have h1 := hpos1 k
  have h2 := hpos2 k
  have hid : (C (r : ℝ)+C (2*(s : ℝ))*X)*(A*B*Q) =
      C (r : ℝ)*(A*B*Q)+(C (2*(s : ℝ))*X*B)*(A*Q) := by ring
  rw [hid]
  simp only [coeff_add, pow_one, B] at *
  linarith

/-- A matching upper bound; the tail polynomial contains only weights≥3. -/
lemma differential_upper_second (r s : ℕ) (Q H : ℝ[X])
    (hQ : Nonneg Q) (hH : CoeffLE Q.derivative (Q*H)) :
    let P : ℝ[X] := (1+X)^r*(1+X^2)^s*Q
    CoeffLE ((1+X)*P.derivative)
      ((C (r : ℝ)+C (2*(s : ℝ))*X)*P+
        P*(C (2*(s : ℝ))*X^2+(1+X)*H)) := by
  dsimp only
  let A : ℝ[X] := (1+X)^r
  let B : ℝ[X] := (1+X^2)^s
  have hA : Nonneg A := by
    simpa [A] using (nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow 1)) r)
  have hB : Nonneg B := nonneg_pow (nonneg_add nonneg_one (nonneg_X_pow 2)) s
  have hlin : Nonneg (1+(X : ℝ[X])) := by
    simpa using (nonneg_add nonneg_one (nonneg_X_pow 1))
  have hdA : (1+X)*A.derivative = C (r : ℝ)*A := unit_derivative_identity r
  have hb := coeffLE_mul_right (factor_derivative_upper 1 s)
    (nonneg_mul (nonneg_mul hlin hA) hQ)
  have hq := coeffLE_mul_left hH (nonneg_mul (nonneg_mul hlin hA) hB)
  have hh := coeffLE_add hb hq
  have hz := coeffLE_add (coeffLE_refl (C (r : ℝ)*A*B*Q)) hh
  convert hz using 1
  · rw [derivative_mul,derivative_mul]
    calc
      _ = ((1+X)*A.derivative)*(B*Q)+
        B.derivative*((1+X)*A*Q)+(1+X)*A*B*Q.derivative := by ring
      _ = _ := by rw [hdA]; ring
  · dsimp [A,B]
    ring

#print axioms differential_lower_second
#print axioms differential_upper_second
end BBFMRefined
