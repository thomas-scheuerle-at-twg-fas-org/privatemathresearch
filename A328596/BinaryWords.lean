import Mathlib.Data.Nat.Bits
import Mathlib.Tactic

/-!
# Reversed Binary Words

This file defines the reversed binary expansion used in the OEIS A328596
formalization and proves a first structural lemma for powers of two.
-/

namespace A328596

/-- We represent binary words as lists of bits.
`false` means `0` and `true` means `1`. -/
abbrev Bit := Bool

/-- `revBinary n` is the ordinary binary expansion of `n`, written from
least significant bit to most significant bit.

For example, `26 = 11010₂`, so `revBinary 26 = [0, 1, 0, 1, 1]`. -/
def revBinary (n : Nat) : List Bit :=
  n.bits

@[simp] theorem revBinary_zero : revBinary 0 = [] := by
  rfl

@[simp] theorem revBinary_one : revBinary 1 = [true] := by
  simp [revBinary]

@[simp] theorem revBinary_two_mul {n : Nat} (hn : n ≠ 0) :
    revBinary (2 * n) = false :: revBinary n := by
  simp [revBinary, Nat.bit0_bits, hn]

@[simp] theorem revBinary_two_mul_add_one (n : Nat) :
    revBinary (2 * n + 1) = true :: revBinary n := by
  simp [revBinary]

/-- The reversed binary word of `2^k` is `0^k 1`. -/
theorem revBinary_pow_two (k : Nat) :
    revBinary (2 ^ k) = List.replicate k false ++ [true] := by
  induction k with
  | zero =>
      simp [revBinary_one]
  | succ k ih =>
      have hk : 2 ^ k ≠ 0 := by
        have hk' : 0 < 2 ^ k := by
          positivity
        exact Nat.ne_of_gt hk'
      calc
        revBinary (2 ^ (k + 1)) = revBinary (2 * (2 ^ k)) := by
          rw [Nat.pow_succ, Nat.mul_comm]
        _ = false :: revBinary (2 ^ k) := by
          simp [revBinary_two_mul hk]
        _ = false :: (List.replicate k false ++ [true]) := by
          rw [ih]
        _ = List.replicate (k + 1) false ++ [true] := by
          simp [List.replicate]

example : revBinary 26 = [false, true, false, true, true] := rfl

end A328596
