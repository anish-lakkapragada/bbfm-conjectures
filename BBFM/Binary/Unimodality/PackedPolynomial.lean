import BBFM.Binary.Unimodality.BinomialSmoothing
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.OfFn

open Polynomial
namespace BinaryCertificate

noncomputable def listPoly : List ℕ → ℤ[X]
  | [] => 0
  | a :: p => C (a : ℤ) + X * listPoly p

lemma listPoly_coeff (p : List ℕ) (k : ℕ) :
    (listPoly p).coeff k = (p[k]?.getD 0 : ℕ) := by
  induction p generalizing k with
  | nil => simp [listPoly]
  | cons a p ih =>
    cases k with
    | zero => simp [listPoly]
    | succ k => simp [listPoly, Polynomial.coeff_X_mul, ih]

lemma listPoly_eval (p : List ℕ) (b : ℕ) :
    (listPoly p).eval (b : ℤ) = (Nat.ofDigits b p : ℕ) := by
  induction p with
  | nil => simp [listPoly, Nat.ofDigits]
  | cons a p ih => simp [listPoly, Nat.ofDigits, ih]

noncomputable def coeffList (P : ℤ[X]) (d : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (d + 1) => (P.coeff i).toNat)

lemma listPoly_coeffList (P : ℤ[X]) (d : ℕ)
    (hsupport : ∀ k, d < k → P.coeff k = 0)
    (hnonneg : ∀ k, 0 ≤ P.coeff k) : listPoly (coeffList P d) = P := by
  ext k
  rw [listPoly_coeff]
  by_cases hk : k < d + 1
  · simp only [coeffList, List.getElem?_ofFn, dif_pos hk, Option.getD_some]
    exact Int.toNat_of_nonneg (hnonneg k)
  · simp only [coeffList, List.getElem?_ofFn, dif_neg hk, Option.getD_none, Nat.cast_zero]
    exact (hsupport k (by omega)).symm

lemma mem_le_ofDigits_one (p : List ℕ) {a : ℕ} (ha : a ∈ p) :
    a ≤ Nat.ofDigits 1 p := by
  induction p with
  | nil => simp at ha
  | cons c p ih =>
    simp only [List.mem_cons] at ha
    simp only [Nat.ofDigits, Nat.cast_id, one_mul]
    rcases ha with rfl | ha
    · omega
    · have h := ih ha; omega

lemma getD_eq_packed_digit (p : List ℕ) (b : ℕ) (hb : 0 < b)
    (hbound : ∀ a ∈ p, a < b) (k : ℕ) :
    p[k]?.getD 0 = Nat.ofDigits b p / b ^ k % b := by
  induction p generalizing k with
  | nil => simp [Nat.ofDigits]
  | cons a p ih =>
    have ha : a < b := hbound a (by simp)
    have hp : ∀ a ∈ p, a < b := fun x hx => hbound x (by simp [hx])
    have hdiv : Nat.ofDigits b (a :: p) / b = Nat.ofDigits b p := by
      simp only [Nat.ofDigits, Nat.cast_id]
      rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, zero_add]
    cases k with
    | zero => simp [Nat.ofDigits, Nat.add_mod, Nat.mod_eq_of_lt ha]
    | succ k =>
      rw [List.getElem?_cons_succ, ih hp, pow_succ', ← Nat.div_div_eq_div_mul, hdiv]

/-- A single carry-free integer evaluation determines the complete coefficient
list of a nonnegative polynomial. Every arithmetic premise can be kernel checked. -/
theorem polynomial_eq_of_packed (P : ℤ[X]) (d b : ℕ) (p : List ℕ)
    (hsupport : ∀ k, d < k → P.coeff k = 0)
    (hnonneg : ∀ k, 0 ≤ P.coeff k)
    (hbase : P.eval 1 < (b : ℤ)) (hp : ∀ a ∈ p, a < b)
    (hvalue : ((Nat.ofDigits b p : ℕ) : ℤ) = P.eval (b : ℤ)) : listPoly p = P := by
  let q := coeffList P d
  have heq : listPoly q = P := listPoly_coeffList P d hsupport hnonneg
  have hev (a : ℕ) : ((Nat.ofDigits a q : ℕ) : ℤ) = P.eval (a : ℤ) := by
    rw [← listPoly_eval, heq]
  have hq1 : Nat.ofDigits 1 q < b := by
    have ht := hev 1
    norm_num at ht
    omega
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le _) hq1
  have hq : ∀ a ∈ q, a < b := fun a ha => (mem_le_ofDigits_one q ha).trans_lt hq1
  have hv : Nat.ofDigits b p = Nat.ofDigits b q := by
    have ht := hev b
    omega
  rw [← heq]
  ext k
  rw [listPoly_coeff, listPoly_coeff, getD_eq_packed_digit p b hb hp k,
    getD_eq_packed_digit q b hb hq k, hv]

end BinaryCertificate

#print axioms BinaryCertificate.polynomial_eq_of_packed
