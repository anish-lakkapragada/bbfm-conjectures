import BBFM.Denominator.Analytic.Basic

namespace C4Search
open Polynomial

/-- Ascending coefficient list, interpreted over the reals. -/
noncomputable def poly : List ℕ → ℝ[X]
  | [] => 0
  | a :: p => C (a : ℝ) + X * poly p

def add : List ℕ → List ℕ → List ℕ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

def shift : ℕ → List ℕ → List ℕ
  | 0, p => p
  | s+1, p => 0 :: shift s p

def factor (p : List ℕ) (s : ℕ) : List ℕ := add p (shift s p)

def repeatFactor (p : List ℕ) (s : ℕ) : ℕ → List ℕ
  | 0 => p
  | r+1 => factor (repeatFactor p s r) s

def calculate (n : ℕ) : ℕ → List ℕ
  | 0 => [1]
  | i+1 => repeatFactor (calculate n i) (i+1) (Nat.log 2 (n/(i+1))+1)

def coefficients (n : ℕ) : List ℕ := calculate n n

lemma poly_add (p q : List ℕ) : poly (add p q) = poly p + poly q := by
  induction p generalizing q with
  | nil => simp [add, poly]
  | cons a p ih =>
    cases q with
    | nil => simp [add, poly]
    | cons b q => simp [add, poly, ih, Nat.cast_add]; ring

lemma poly_shift (s : ℕ) (p : List ℕ) : poly (shift s p) = X^s * poly p := by
  induction s with
  | zero => simp [shift]
  | succ s ih => simp [shift, poly, ih, pow_succ]; ring

lemma poly_factor (p : List ℕ) (s : ℕ) :
    poly (factor p s) = poly p * (1+X^s) := by
  rw [factor, poly_add, poly_shift]
  ring

lemma poly_repeatFactor (p : List ℕ) (s r : ℕ) :
    poly (repeatFactor p s r) = poly p * (1+X^s)^r := by
  induction r with
  | zero => simp [repeatFactor]
  | succ r ih => simp [repeatFactor, poly_factor, ih, pow_succ, mul_assoc]

lemma poly_calculate (n i : ℕ) :
    poly (calculate n i) = ∏ j ∈ Finset.range i,
      (1+(X : ℝ[X])^(j+1))^(Nat.log 2 (n/(j+1))+1) := by
  induction i with
  | zero => simp [calculate, poly]
  | succ i ih => rw [calculate, poly_repeatFactor, Finset.prod_range_succ, ih]

/-- The executable coefficient calculator represents exactly the prior formal denominator. -/
theorem poly_coefficients (n : ℕ) : poly (coefficients n) = DenominatorResearch.den n := by
  exact poly_calculate n n

lemma coeff_poly (p : List ℕ) (k : ℕ) : (poly p).coeff k = (p[k]?.getD 0 : ℝ) := by
  induction p generalizing k with
  | nil => simp [poly]
  | cons a p ih =>
    cases k with
    | zero => simp [poly]
    | succ k => simp [poly, coeff_X_mul, ih]

def checks (p : List ℕ) : Prop :=
  ∀ k ∈ List.range p.length, 1 ≤ k →
    (p[k-1]?.getD 0) * (p[k+1]?.getD 0) ≤ (p[k]?.getD 0)^2

instance (p : List ℕ) : Decidable (checks p) := by unfold checks; infer_instance

/-- A finite natural-number certificate yields every real coefficient inequality,
including all indices beyond the supplied list. -/
theorem logconcave_of_checks (p : List ℕ) (h : checks p) (k : ℕ) (hk : 1 ≤ k) :
    (poly p).coeff (k-1) * (poly p).coeff (k+1) ≤ ((poly p).coeff k)^2 := by
  simp only [coeff_poly]
  by_cases hp : k < p.length
  · have h' := h k (List.mem_range.mpr hp) hk
    exact_mod_cast h'
  · have hz : p[k+1]? = none := List.getElem?_eq_none (by omega)
    simp [hz]

theorem denominator_logconcave_of_checks (n : ℕ) (h : checks (coefficients n))
    (k : ℕ) (hk : 1 ≤ k) :
    (DenominatorResearch.den n).coeff (k-1) * (DenominatorResearch.den n).coeff (k+1) ≤
      ((DenominatorResearch.den n).coeff k)^2 := by
  rw [← poly_coefficients]
  exact logconcave_of_checks _ h k hk

#print axioms poly_coefficients
#print axioms denominator_logconcave_of_checks
end C4Search
