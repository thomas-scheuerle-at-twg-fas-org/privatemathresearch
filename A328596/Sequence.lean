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

theorem append_left_lt_of_lt {α : Type*} [LinearOrder α] {u v : List α} (p : List α)
    (h : u < v) : p ++ u < p ++ v := by
  exact (List.lt_iff_lex_lt _ _).2 <|
    List.Lex.append_left (R := (· < ·)) ((List.lt_iff_lex_lt _ _).1 h) p

theorem zeroes_then_one_isLyndon (k : Nat) :
    IsLyndon (List.replicate k false ++ [true]) := by
  constructor
  · simp
  · intro i hi0 hi
    cases i with
    | zero => cases Nat.lt_asymm hi0 hi0
    | succ j =>
        have hj : j < k := by
          simpa using hi
        have hle : j + 1 ≤ k := Nat.succ_le_of_lt hj
        have hdecomp : k = (k - (j + 1)) + (j + 1) := by
          exact (Nat.sub_add_cancel hle).symm
        have hsplit :
            List.replicate k false ++ [true] =
              List.replicate (k - (j + 1)) false ++
                (List.replicate (j + 1) false ++ [true]) := by
          rw [hdecomp, List.replicate_add, List.append_assoc]
          simp
        have hrotate :
            (List.replicate k false ++ [true]).rotate (j + 1) =
              List.replicate (k - (j + 1)) false ++
                (true :: List.replicate (j + 1) false) := by
          have hle' : j + 1 ≤ (List.replicate k false).length := by
            simpa using hle
          rw [List.rotate_eq_drop_append_take hi.le]
          rw [List.drop_append_of_le_length hle', List.take_append_of_le_length hle']
          simp [List.append_assoc, hj]
        rw [hrotate, hsplit]
        apply append_left_lt_of_lt
        exact (List.lt_iff_lex_lt _ _).2 <| by
          simpa [List.replicate] using (List.Lex.rel (show false < true by decide))

theorem two_pow_mem_a328596 (k : Nat) : InA328596 (2 ^ k) := by
  constructor
  · have hk : 0 < 2 ^ k := by
      positivity
    exact hk
  · rw [revBinary_pow_two]
    exact zeroes_then_one_isLyndon k

end A328596
