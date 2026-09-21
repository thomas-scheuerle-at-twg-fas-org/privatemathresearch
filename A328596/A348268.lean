import Mathlib.Data.List.Find
import Mathlib.Data.Nat.Prime.Nth
import A328596.Sequence

/-!
# OEIS A348268 scaffold

This file starts the executable infrastructure for the Lyndon/prime
correspondence behind A348268.

The main ingredients are:

* `Nat.bits` as the reversed binary word of a natural number;
* the existing A328596 predicate for Lyndon reversed-binary words;
* `Nat.count` and `Nat.nth` for ranking and enumerating generators and primes.

The factorization theorem itself will be added incrementally on top of these
definitions.
-/

namespace A348268

open A328596

/-- Binary words are lists of bits. We reuse the `Bool` convention from A328596. -/
abbrev BitWord := List Bool

/-- Convert a reversed binary word back to a natural number. -/
def bitsToNat : BitWord → Nat
  | [] => 0
  | b :: w => Nat.bit b (bitsToNat w)

@[simp] theorem bitsToNat_nil : bitsToNat [] = 0 := rfl

@[simp] theorem bitsToNat_cons (b : Bool) (w : BitWord) :
    bitsToNat (b :: w) = Nat.bit b (bitsToNat w) := rfl

/-- `bitsToNat` is the inverse of `Nat.bits`. -/
theorem bitsToNat_bits (n : Nat) : bitsToNat n.bits = n := by
  induction n using Nat.binaryRec with
  | zero =>
      simp [bitsToNat]
  | bit b n ih =>
      cases b with
      | false =>
          by_cases hn : n = 0
          · subst hn
            simp [bitsToNat]
          · simpa [bitsToNat, ih] using congrArg bitsToNat (Nat.bit0_bits n hn)
      | true =>
          simpa [bitsToNat, ih] using congrArg bitsToNat (Nat.bit1_bits n)

@[simp] theorem bitsToNat_revBinary (n : Nat) : bitsToNat (revBinary n) = n := by
  simpa [revBinary] using bitsToNat_bits n

/-- The rank of `n` inside A328596, using `Nat.count`. -/
noncomputable def a328596Rank (n : Nat) : Nat := by
  classical
  exact Nat.count InA328596 n

/-- The prime attached to the `A328596`-rank of `n`. -/
noncomputable def primeOfA328596 (n : Nat) : Nat := by
  classical
  exact Nat.nth Nat.Prime (a328596Rank n)

/-- The prime attached to a binary word, after converting it to a natural number. -/
noncomputable def primeOfWord (w : BitWord) : Nat := by
  classical
  exact primeOfA328596 (bitsToNat w)

example : bitsToNat [false, true] = 2 := by
  simp [bitsToNat]

example : Nat.nth Nat.Prime 0 = 2 := by
  simp

example : Nat.nth Nat.Prime 1 = 3 := by
  simp

end A348268