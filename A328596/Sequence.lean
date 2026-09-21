import Mathlib.Tactic
import A328596.BinaryWords
import A328596.Lyndon

/-!
# The Sequence A328596

This file packages the reversed-binary Lyndon condition into a predicate on
natural numbers and records a first OEIS sanity check.
-/

namespace A328596

/-- Membership in OEIS A328596:
`n` is positive and its reversed binary expansion is a Lyndon word. -/
def InA328596 (n : Nat) : Prop :=
  0 < n ∧ IsLyndon (revBinary n)

/-- A Boolean version of `InA328596`, used for computed examples. -/
def inA328596Bool (n : Nat) : Bool :=
  decide (0 < n) && isLyndonBool (revBinary n)

/-- A small computed prefix, used only as a sanity check against OEIS. -/
def firstTermsUpTo (n : Nat) : List Nat :=
  (List.range (n + 1)).filter inA328596Bool

example : firstTermsUpTo 32 = [1, 2, 4, 6, 8, 12, 14, 16, 20, 24, 26, 28, 30, 32] := by
  decide

theorem zeroes_then_one_isLyndon (k : Nat) :
    IsLyndon (List.replicate k false ++ [true]) := by
  exact (zeroes_then_one_isSuffixLyndon k).toIsLyndon

theorem two_pow_mem_a328596 (k : Nat) : InA328596 (2 ^ k) := by
  constructor
  · have hk : 0 < 2 ^ k := by
      positivity
    exact hk
  · rw [revBinary_pow_two]
    exact zeroes_then_one_isLyndon k

end A328596
