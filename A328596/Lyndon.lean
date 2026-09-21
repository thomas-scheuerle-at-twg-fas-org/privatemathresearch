import Mathlib.Data.List.Lex
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.TakeDrop
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

/-- An auxiliary formulation that compares a word directly with each proper
nonempty suffix. For the binary lemmas below, this is often easier to use than
the rotation-based definition. -/
def IsSuffixLyndon {α : Type*} [LinearOrder α] (w : List α) : Prop :=
  w ≠ [] ∧
    ∀ i, 0 < i → i < w.length → w < w.drop i

/-- A Boolean checker for the Lyndon condition, used for small computational
sanity checks.

It checks the nonempty condition and then tests all rotations with cut positions
`i < w.length`, treating `i = 0` as the trivial rotation that we ignore. -/
def isLyndonBool {α : Type*} [LinearOrder α] (w : List α) : Bool :=
  decide (w ≠ []) &&
    (List.range w.length).all fun i => decide (i = 0 ∨ w < w.rotate i)

theorem isLyndonBool_eq_true_iff {α : Type*} [LinearOrder α] (w : List α) :
    isLyndonBool w = true ↔ IsLyndon w := by
  constructor
  · intro h
    simp [isLyndonBool] at h
    rcases h with ⟨hne, hall⟩
    constructor
    · exact hne
    · intro i hi0 hi
      exact (hall i hi).resolve_left (by omega)
  · intro h
    rcases h with ⟨hne, hlt⟩
    simp [isLyndonBool, hne, List.all_eq_true]
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hxpos : 0 < x := Nat.pos_of_ne_zero hx0
      simp [hx0, hlt x hxpos hx]

theorem IsLyndon.ne_nil {α : Type*} [LinearOrder α] {w : List α} (h : IsLyndon w) :
    w ≠ [] :=
  h.1

theorem IsLyndon.lt_rotate {α : Type*} [LinearOrder α] {w : List α} (h : IsLyndon w)
    {i : Nat} (hi0 : 0 < i) (hi : i < w.length) :
    w < w.rotate i :=
  h.2 i hi0 hi

theorem IsSuffixLyndon.ne_nil {α : Type*} [LinearOrder α] {w : List α}
    (h : IsSuffixLyndon w) : w ≠ [] :=
  h.1

theorem IsSuffixLyndon.lt_drop {α : Type*} [LinearOrder α] {w : List α}
    (h : IsSuffixLyndon w) {i : Nat} (hi0 : 0 < i) (hi : i < w.length) :
    w < w.drop i :=
  h.2 i hi0 hi

theorem cons_lt_cons {α : Type*} [LinearOrder α] {a : α} {u v : List α}
    (h : u < v) : a :: u < a :: v := by
  exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.cons ((List.lt_iff_lex_lt _ _).1 h)

theorem append_right_lt_of_lt {α : Type*} [LinearOrder α] {u v : List α} (t : List α)
    (h : u < v) : u < v ++ t := by
  exact (List.lt_iff_lex_lt _ _).2 <|
    List.Lex.append_right (r := (· < ·)) t ((List.lt_iff_lex_lt _ _).1 h)

theorem append_left_lt_of_lt {α : Type*} [LinearOrder α] {u v : List α} (p : List α)
    (h : u < v) : p ++ u < p ++ v := by
  exact (List.lt_iff_lex_lt _ _).2 <|
    List.Lex.append_left (R := (· < ·)) ((List.lt_iff_lex_lt _ _).1 h) p

theorem append_left_cancel_lt {α : Type*} [LinearOrder α] {p u v : List α}
  (h : p ++ u < p ++ v) : u < v := by
  induction p with
  | nil => simpa using h
  | cons a p ih =>
    have h' : p ++ u < p ++ v := by
      exact (List.lex_cons_iff).1 h
    exact ih h'

theorem append_right_lt_of_lt_of_eq_length {α : Type*} [LinearOrder α]
  {u v : List α} (t : List α) (h : u < v) (hlen : u.length = v.length) :
  u ++ t < v ++ t := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => cases lt_irrefl [] h
    | cons b v => simp at hlen
  | cons a u ih =>
    cases v with
    | nil => simp at hlen
    | cons b v =>
      rcases lt_or_eq_of_le (List.head_le_of_lt h) with hab | rfl
      · exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel hab
      · have htail : u < v := by simpa [List.lex_cons_iff] using h
        have hlen' : u.length = v.length := by simpa using hlen
        exact cons_lt_cons (ih htail hlen')

theorem append_lt_of_lt_of_not_prefix {α : Type*} [LinearOrder α]
  {u v t : List α} (h : u < v) (hprefix : ¬ u <+: v) : u ++ t < v := by
  induction u generalizing v t with
  | nil =>
    simpa using hprefix
  | cons a u ih =>
    cases v with
    | nil => cases h
    | cons b v =>
      rcases lt_or_eq_of_le (List.head_le_of_lt h) with hab | rfl
      · exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel hab
      · have htail : u < v := by simpa [List.lex_cons_iff] using h
        have hprefix' : ¬ u <+: v := by
          intro hp
          exact hprefix (List.cons_prefix_cons.mpr ⟨rfl, hp⟩)
        exact cons_lt_cons (ih htail hprefix')

theorem IsSuffixLyndon.toIsLyndon {α : Type*} [LinearOrder α] {w : List α}
    (h : IsSuffixLyndon w) : IsLyndon w := by
  constructor
  · exact h.1
  · intro i hi0 hi
    rw [List.rotate_eq_drop_append_take hi.le]
    exact append_right_lt_of_lt (List.take i w) (h.lt_drop hi0 hi)

theorem IsLyndon.drop_not_prefix {α : Type*} [LinearOrder α] {w : List α}
    (h : IsLyndon w) {i : Nat} (hi0 : 0 < i) (hi : i < w.length) :
    ¬ w.drop i <+: w := by
  intro hprefix
  let v := w.drop i
  let u := w.take i
  let z := w.drop v.length
  have hsplit : w = u ++ v := by
    simpa [u, v] using (List.take_append_drop i w).symm
  have hrot_i : w < v ++ u := by
    have hrot := h.lt_rotate hi0 hi
    rw [List.rotate_eq_drop_append_take hi.le] at hrot
    simpa [u, v] using hrot
  have hprefix_split : w = v ++ w.drop v.length := by
    exact List.prefix_append_drop hprefix
  have hzltu : z < u := by
    rw [hprefix_split] at hrot_i
    simpa [z] using append_left_cancel_lt hrot_i
  have hvpos : 0 < v.length := by
    simp [v]
    omega
  have hvlt : v.length < w.length := by
    simp [v]
    omega
  have hzlen : z.length = u.length := by
    simp [u, v, z]
    omega
  have hrot_v : w < z ++ v := by
    have hrot : v ++ z < z ++ v := by
      have hrot' := h.lt_rotate hvpos hvlt
      rw [hprefix_split, List.rotate_append_length_eq] at hrot'
      simpa [z] using hrot'
    exact hprefix_split.symm ▸ hrot
  have hback : z ++ v < w := by
    have htmp : z ++ v < u ++ v :=
      append_right_lt_of_lt_of_eq_length v hzltu hzlen
    exact hsplit.symm ▸ htmp
  exact (lt_asymm hrot_v hback).elim

theorem IsLyndon.toIsSuffixLyndon {α : Type*} [LinearOrder α] {w : List α}
    (h : IsLyndon w) : IsSuffixLyndon w := by
  constructor
  · exact h.1
  · intro i hi0 hi
    let v := w.drop i
    let u := w.take i
    have hrot : w < v ++ u := by
      have hrot' := h.lt_rotate hi0 hi
      rw [List.rotate_eq_drop_append_take hi.le] at hrot'
      simpa [u, v] using hrot'
    by_contra hnv
    have hvne : v ≠ w := by
      intro hEq
      have : v.length < w.length := by
        simp [v]
        omega
      simpa [hEq] using this
    have hvw : v < w := lt_of_le_of_ne (le_of_not_gt hnv) hvne
    by_cases hprefix : v <+: w
    · exact (h.drop_not_prefix hi0 hi) hprefix
    · have hcontra : v ++ u < w := append_lt_of_lt_of_not_prefix hvw hprefix
      exact (lt_asymm hrot hcontra).elim

theorem isLyndon_singleton {α : Type*} [LinearOrder α] (a : α) :
    IsLyndon [a] := by
  constructor
  · simp
  · intro i hi0 hi
    have hlt : i < 1 := by simpa using hi
    omega

theorem isSuffixLyndon_singleton {α : Type*} [LinearOrder α] (a : α) :
    IsSuffixLyndon [a] := by
  constructor
  · simp
  · intro i hi0 hi
    have hlt : i < 1 := by simpa using hi
    omega

/-- If a binary suffix-Lyndon word ends in `1`, then prefixing one more `0`
produces another suffix-Lyndon word.

This is one of the structural closure properties behind the least-significant-
bit decomposition. -/
theorem prepend_false_preserves_isSuffixLyndon (u : List Bool)
    (h : IsSuffixLyndon (u ++ [true])) :
    IsSuffixLyndon (false :: (u ++ [true])) := by
  constructor
  · simp
  · intro i hi0 hi
    cases i with
    | zero => cases Nat.lt_asymm hi0 hi0
    | succ j =>
        have hj : j < (u ++ [true]).length := by
          simpa using hi
        have hjle : j ≤ u.length := by
          simpa using hj
        have hdrop : (u ++ [true]).drop j = u.drop j ++ [true] := by
          simpa using List.drop_append_of_le_length (l₁ := u) (l₂ := [true]) hjle
        cases huj : u.drop j with
        | nil =>
            rw [show (false :: (u ++ [true])).drop (j + 1) = [true] by simp [hdrop, huj]]
            exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel (show false < true by decide)
        | cons b t =>
            cases b with
            | false =>
                have hju : j < u.length := by
                  have hlen' : 0 < (u.drop j).length := by
                    simp [huj]
                  rw [List.length_drop] at hlen'
                  omega
                have htail : (u ++ [true]).drop (j + 1) = t ++ [true] := by
                  rw [← List.drop_drop, hdrop, huj]
                  simp
                have huw : u ++ [true] < t ++ [true] := by
                  have huw' : u ++ [true] < (u ++ [true]).drop (j + 1) :=
                    h.lt_drop (Nat.succ_pos _) (by simpa using Nat.succ_lt_succ hju)
                  rw [htail] at huw'
                  exact huw'
                rw [show (false :: (u ++ [true])).drop (j + 1) = false :: (t ++ [true]) by
                  simp [hdrop, huj]]
                exact cons_lt_cons huw
            | true =>
                rw [show (false :: (u ++ [true])).drop (j + 1) = true :: (t ++ [true]) by
                  simp [hdrop, huj]]
                exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel (show false < true by decide)

theorem prepend_false_preserves_isLyndon (u : List Bool)
    (h : IsSuffixLyndon (u ++ [true])) :
    IsLyndon (false :: (u ++ [true])) :=
  (prepend_false_preserves_isSuffixLyndon u h).toIsLyndon

theorem append_true_lt_true_cons (u : List Bool) :
  u ++ [true] < true :: (u ++ [true]) := by
  induction u with
  | nil =>
    exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.cons List.Lex.nil
  | cons b u ih =>
    cases b with
    | false =>
      exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel (show false < true by decide)
    | true =>
      simpa using cons_lt_cons (a := true) ih

theorem prepend_false_lt_self_append_true (u : List Bool) :
  false :: (u ++ [true]) < u ++ [true] := by
  induction u with
  | nil =>
    exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel (show false < true by decide)
  | cons b u ih =>
    cases b with
    | false =>
      simpa using cons_lt_cons (a := false) ih
    | true =>
      exact (List.lt_iff_lex_lt _ _).2 <| List.Lex.rel (show false < true by decide)

theorem replicate_falses_lt_self_append_true (k : Nat) (u : List Bool) :
  List.replicate (k + 1) false ++ (u ++ [true]) < u ++ [true] := by
  induction k with
  | zero =>
      simpa using prepend_false_lt_self_append_true u
  | succ k ih =>
      have h₁ : false :: (List.replicate (k + 1) false ++ (u ++ [true])) < false :: (u ++ [true]) :=
        cons_lt_cons (a := false) ih
      have h₂ : List.replicate (k + 2) false ++ (u ++ [true]) < false :: (u ++ [true]) := by
        simpa [List.replicate, List.append_assoc] using h₁
      exact lt_trans h₂ (prepend_false_lt_self_append_true u)

theorem replicate_falses_lt_self_append_true_of_pos {i : Nat} (hi : 0 < i) (u : List Bool) :
    List.replicate i false ++ (u ++ [true]) < u ++ [true] := by
  cases i with
  | zero => cases Nat.lt_asymm hi hi
  | succ j =>
      simpa using replicate_falses_lt_self_append_true j u

theorem remove_first_true_preserves_isSuffixLyndon (k : Nat) (u : List Bool)
    (h : IsSuffixLyndon (List.replicate k false ++ (true :: (u ++ [true])))) :
    IsSuffixLyndon (List.replicate k false ++ (u ++ [true])) := by
  let t := u ++ [true]
  have hyx : List.replicate k false ++ t < List.replicate k false ++ (true :: t) := by
    simpa [t] using append_left_lt_of_lt (List.replicate k false) (append_true_lt_true_cons u)
  constructor
  · simp [t]
  · intro i hi0 hi
    by_cases hik : i ≤ k
    · have hdecomp : k = (k - i) + i := by omega
      have hy : List.replicate k false ++ t =
          List.replicate (k - i) false ++ (List.replicate i false ++ t) := by
        rw [hdecomp, List.replicate_add, List.append_assoc]
        simp
      have hdropy : (List.replicate k false ++ t).drop i = List.replicate (k - i) false ++ t := by
        rw [List.drop_append_of_le_length]
        · simp [hik, t]
        · simpa using hik
      calc
        List.replicate k false ++ t
            = List.replicate (k - i) false ++ (List.replicate i false ++ t) := hy
        _ < List.replicate (k - i) false ++ t :=
          append_left_lt_of_lt (List.replicate (k - i) false)
            (replicate_falses_lt_self_append_true_of_pos hi0 u)
        _ = (List.replicate k false ++ t).drop i := hdropy.symm
    · have hklt : k < i := lt_of_not_ge hik
      let j := i - k
      have hjpos : 0 < j := by
        dsimp [j]
        omega
      have hjlen : j < t.length := by
        dsimp [j] at *
        simp [t] at hi ⊢
        omega
      have hdropy : (List.replicate k false ++ t).drop i = t.drop j := by
        calc
          (List.replicate k false ++ t).drop i
              = ((List.replicate k false ++ t).drop k).drop j := by
                  rw [show i = k + j by
                    dsimp [j]
                    omega, List.drop_drop]
          _ = t.drop j := by
            rw [List.drop_append_of_le_length]
            · simp [t]
            · simp
      have hdropx : (List.replicate k false ++ (true :: t)).drop (i + 1) = t.drop j := by
        calc
          (List.replicate k false ++ (true :: t)).drop (i + 1)
              = ((List.replicate k false ++ (true :: t)).drop (k + 1)).drop j := by
                  rw [show i + 1 = (k + 1) + j by
                    dsimp [j]
                    omega, List.drop_drop]
          _ = t.drop j := by
            have hxk1 : (List.replicate k false ++ (true :: t)).drop (k + 1) = t := by
              calc
                (List.replicate k false ++ (true :: t)).drop (k + 1)
                    = ((List.replicate k false ++ (true :: t)).drop k).drop 1 := by
                        rw [show k + 1 = k + 1 by omega, List.drop_drop]
                _ = (true :: t).drop 1 := by
                  rw [List.drop_append_of_le_length]
                  · simp
                  · simp
                _ = t := by simp
            rw [hxk1]
      have hxlt : List.replicate k false ++ (true :: t) < t.drop j := by
        have hxlen : i + 1 < (List.replicate k false ++ (true :: t)).length := by
          simp [t] at hi ⊢
          omega
        have htmp := h.lt_drop (Nat.succ_pos _) hxlen
        rw [hdropx] at htmp
        exact htmp
      rw [hdropy]
      exact lt_trans hyx hxlt

/-- Suffix-form version of the main combinatorial transformation:
from `0^k 1 u 1`, delete the first `1` after the initial zero block, then
prepend one more `0`. -/
theorem zero_block_step_isSuffixLyndon (k : Nat) (u : List Bool)
    (h : IsSuffixLyndon (List.replicate k false ++ (true :: (u ++ [true])))) :
    IsSuffixLyndon (List.replicate (k + 1) false ++ (u ++ [true])) := by
  have h' : IsSuffixLyndon ((List.replicate k false ++ u) ++ [true]) := by
    simpa [List.append_assoc] using remove_first_true_preserves_isSuffixLyndon k u h
  simpa [List.replicate, List.replicate_add, List.append_assoc] using
    prepend_false_preserves_isSuffixLyndon (List.replicate k false ++ u) h'

/-- Rotation-form corollary of `zero_block_step_isSuffixLyndon`. -/
theorem zero_block_step_isLyndon (k : Nat) (u : List Bool)
    (h : IsSuffixLyndon (List.replicate k false ++ (true :: (u ++ [true])))) :
    IsLyndon (List.replicate (k + 1) false ++ (u ++ [true])) :=
  (zero_block_step_isSuffixLyndon k u h).toIsLyndon

theorem zeroes_then_one_isSuffixLyndon (k : Nat) :
    IsSuffixLyndon (List.replicate k false ++ [true]) := by
  induction k with
  | zero =>
      simpa using isSuffixLyndon_singleton true
  | succ k ih =>
      simpa [List.replicate, List.replicate_add] using
        prepend_false_preserves_isSuffixLyndon (List.replicate k false) ih

end A328596
