import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

open Polynomial

def powersOfTwoUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).image (fun k => 2 ^ k)

def IsBinaryPartition {n : ℕ} (p : Nat.Partition n) : Prop :=
  ∀ i ∈ p.parts, i ∈ powersOfTwoUpTo n

instance (n : ℕ) : DecidablePred (@IsBinaryPartition n) :=
  fun _ => Multiset.decidableDforallMultiset

def binaryPartitions (n : ℕ) : Finset (Nat.Partition n) :=
  (Finset.univ : Finset (Nat.Partition n)).filter IsBinaryPartition

noncomputable def denB (n : ℕ) : ℤ[X] :=
  ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k)) ^ (n / 2 ^ k)

noncomputable def hBPartition (n : ℕ) (p : Nat.Partition n) : ℤ[X] :=
  ∏ k ∈ Finset.range (n + 1), (1 + X ^ (2 ^ k)) ^ ((n / 2 ^ k) - p.parts.count (2 ^ k))

noncomputable def numB (n : ℕ) : ℤ[X] :=
  ∑ p ∈ binaryPartitions n, hBPartition n p


