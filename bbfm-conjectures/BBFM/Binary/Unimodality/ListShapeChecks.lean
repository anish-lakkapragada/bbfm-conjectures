import BBFM.Binary.Unimodality.PackedBinary

open Polynomial BinaryShape BinaryResearch
namespace BinaryCertificate

def consecutiveBound : ℕ → ℕ → List ℕ → Bool
  | 0, _, _ => true
  | n + 1, K, a :: b :: p => decide (a + K ≤ b) && consecutiveBound n K (b :: p)
  | _ + 1, _, _ => false

lemma consecutiveBound_at (n K : ℕ) (p : List ℕ) (h : consecutiveBound n K p = true)
    (k : ℕ) (hk : k < n) : p[k]?.getD 0 + K ≤ p[k + 1]?.getD 0 := by
  induction n generalizing p k with
  | zero => omega
  | succ n ih =>
    cases p with
    | nil => simp [consecutiveBound] at h
    | cons a p =>
      cases p with
      | nil => simp [consecutiveBound] at h
      | cons b p =>
        simp only [consecutiveBound, Bool.and_eq_true, decide_eq_true_eq] at h
        cases k with
        | zero => simpa using h.1
        | succ k => simpa using ih (b :: p) h.2 k (by omega)

theorem listPoly_shape (p : List ℕ) (d : ℕ) (hlen : p.length = d + 1)
    (hsymm : p.reverse = p) (hmono : consecutiveBound (d / 2) 0 p = true) :
    HasShape (listPoly p) d := by
  constructor
  · intro k hk
    rw [listPoly_coeff]
    have hnil : p[k]? = none := List.getElem?_eq_none (by omega)
    simp [hnil]
  · intro k hk
    rw [listPoly_coeff, listPoly_coeff]
    congr 1
    have hh := congrArg (fun q : List ℕ => q[k]?.getD 0) hsymm
    rw [List.getElem?_reverse (by omega)] at hh
    simpa [hlen, show k < d + 1 by omega] using hh.symm
  · intro k
    rw [listPoly_coeff]
    positivity
  · intro k hk
    rw [listPoly_coeff, listPoly_coeff]
    by_cases hkhalf : k < d / 2
    · have hh := consecutiveBound_at (d / 2) 0 p hmono k hkhalf
      simp only [Nat.add_zero] at hh
      exact_mod_cast hh
    · have he : d - k = k + 1 := by omega
      have hh := congrArg (fun q : List ℕ => q[k]?.getD 0) hsymm
      rw [List.getElem?_reverse (by omega)] at hh
      have hh' : p[k + 1]?.getD 0 = p[k]?.getD 0 := by
        simpa [hlen, show k < d + 1 by omega, he] using hh
      rw [hh']

def slopeCheck (p : List ℕ) (lo hi K : ℕ) : Bool :=
  consecutiveBound (hi + 1 - lo) K (p.drop (lo - 1))

theorem listPoly_slope (p : List ℕ) (lo hi K : ℕ) (hlo : 1 ≤ lo)
    (h : slopeCheck p lo hi K = true) (k : ℕ) (hklo : lo ≤ k) (hkhi : k ≤ hi) :
    (K : ℤ) ≤ (listPoly p).coeff k - (listPoly p).coeff (k - 1) := by
  have hh := consecutiveBound_at (hi + 1 - lo) K (p.drop (lo - 1)) h
    (k - lo) (by omega)
  rw [List.getElem?_drop, List.getElem?_drop] at hh
  have h1 : lo - 1 + (k - lo) = k - 1 := by omega
  have h2 : lo - 1 + (k - lo + 1) = k := by omega
  rw [h1, h2] at hh
  rw [listPoly_coeff, listPoly_coeff]
  omega

def alternating : List ℕ → ℤ
  | [] => 0
  | a :: p => a - alternating p

lemma listPoly_eval_neg_one (p : List ℕ) : (listPoly p).eval (-1) = alternating p := by
  induction p with
  | nil => simp [listPoly, alternating]
  | cons a p ih => simp [listPoly, alternating, ih]; ring

lemma listPoly_head_tail (p : List ℕ) :
    listPoly p = C (p.headD 0 : ℤ) + X * listPoly p.tail := by
  cases p <;> simp [listPoly]

def residualCheck : List ℕ → List ℕ → ℕ → ℤ → ℕ → Bool
  | [], r, _, a, prev => decide (r = [] ∧ a = 0 ∧ prev = 0)
  | x :: p, r, c, a, prev =>
      decide ((x : ℤ) = (r.headD 0 : ℤ) + prev + if c = 0 then a else 0) &&
        residualCheck p r.tail (c - 1) (if c = 0 then 0 else a) (r.headD 0)

theorem residualCheck_identity (p r : List ℕ) (c : ℕ) (a : ℤ) (prev : ℕ)
    (h : residualCheck p r c a prev = true) :
    listPoly p = (1 + X) * listPoly r + C (prev : ℤ) + C a * X ^ c := by
  induction p generalizing r c a prev with
  | nil =>
    simp only [residualCheck, decide_eq_true_eq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    simp [listPoly]
  | cons x p ih =>
    simp only [residualCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    have hh := ih r.tail (c - 1) (if c = 0 then 0 else a) (r.headD 0) h.2
    rw [listPoly, hh, listPoly_head_tail r]
    by_cases hc : c = 0
    · subst c
      simp only [ite_true, pow_zero, mul_one, map_zero] at h ⊢
      rw [h.1]
      simp only [map_add]
      ring
    · simp only [if_neg hc, add_zero] at h
      simp only [if_neg hc]
      rw [h.1, map_add]
      have he : (X : ℤ[X]) ^ c = X * X ^ (c - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [he]
      ring

theorem residual_eq_of_check (n : ℕ) (p r : List ℕ) (hp : listPoly p = numB n)
    (h : residualCheck p r (center n) ((-1 : ℤ) ^ center n * alternating p) 0 = true) :
    listPoly r = residual n := by
  have ha : amplitude n = alternating p := by
    rw [amplitude, ← hp, listPoly_eval_neg_one]
  have hi := residualCheck_identity p r (center n) ((-1 : ℤ) ^ center n * alternating p) 0 h
  have hn := residual_identity n
  rw [ha, ← hp] at hn
  have hz : (1 + X : ℤ[X]) ≠ 0 := by
    intro he
    have h0 := congrArg (fun P : ℤ[X] => P.coeff 0) he
    norm_num at h0
  apply mul_left_cancel₀ hz
  rw [hn, hi]
  simp only [Nat.cast_zero, map_zero, add_zero]
  ring

end BinaryCertificate

#print axioms BinaryCertificate.listPoly_shape
#print axioms BinaryCertificate.listPoly_slope
#print axioms BinaryCertificate.residual_eq_of_check
