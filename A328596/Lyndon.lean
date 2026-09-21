import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Mathlib.Tactic

/-!
# Lyndon Words

This file contains the transparent list-based definition of a Lyndon word used
throughout the project.
-/

namespace A328596

/-- A word is Lyndon if it is nonempty and is lexicographically strictly smaller
than every nontrivial cyclic rotation.

This is the direct list-based version of the mathematical definition. -/
def IsLyndon {α : Type*} [LinearOrder α] (w : List α) : Prop :=
  w ≠ [] ∧
    ∀ i, 0 < i → i < w.length → w < w.rotate i

/-- A Boolean checker for the Lyndon condition, used for small computational
sanity checks.

It checks the nonempty condition and then tests all rotations with cut positions
`i < w.length`, treating `i = 0` as the trivial rotation that we ignore. -/
def isLyndonBool {α : Type*} [LinearOrder α] (w : List α) : Bool :=
  decide (w ≠ []) &&
    (List.range w.length).all fun i => decide (i = 0 ∨ w < w.rotate i)

theorem IsLyndon.ne_nil {α : Type*} [LinearOrder α] {w : List α} (h : IsLyndon w) :
    w ≠ [] :=
  h.1

theorem IsLyndon.lt_rotate {α : Type*} [LinearOrder α] {w : List α} (h : IsLyndon w)
    {i : Nat} (hi0 : 0 < i) (hi : i < w.length) :
    w < w.rotate i :=
  h.2 i hi0 hi

theorem isLyndon_singleton {α : Type*} [LinearOrder α] (a : α) :
    IsLyndon [a] := by
  constructor
  · simp
  · intro i hi0 hi
    have hlt : i < 1 := by simpa using hi
    omega

end A328596
