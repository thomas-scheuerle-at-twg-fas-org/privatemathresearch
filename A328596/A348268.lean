import Mathlib.Data.Nat.Find
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Prime.Infinite
import A328596.Sequence

/-!
# OEIS A348268 scaffold

This file starts the executable infrastructure for the Lyndon/prime
correspondence behind A348268.

The main ingredients are:

* `Nat.bits` as the reversed binary word of a natural number;
* the existing A328596 predicate for Lyndon reversed-binary words;
* a computable prefix rank for A328596 and a computable prime enumerator.

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

/-- Appending a trailing `true` makes the bit-encoding positive. -/
theorem bitsToNat_pos_append_true (u : BitWord) : 0 < bitsToNat (u ++ [true]) := by
  induction u with
  | nil =>
      simp [bitsToNat]
  | cons b u ih =>
      cases b <;> simp [bitsToNat, ih]

/-- A binary word ending in `true` is the reversed binary expansion of the
natural number obtained from its bits. -/
theorem revBinary_bitsToNat_append_true (u : BitWord) :
    revBinary (bitsToNat (u ++ [true])) = u ++ [true] := by
  induction u with
  | nil =>
      simp [bitsToNat, revBinary_one]
  | cons b u ih =>
      have hpos : 0 < bitsToNat (u ++ [true]) := bitsToNat_pos_append_true u
      cases b with
      | false =>
          calc
            revBinary (bitsToNat (false :: (u ++ [true])))
                = revBinary (2 * bitsToNat (u ++ [true])) := by simp [bitsToNat]
            _ = false :: revBinary (bitsToNat (u ++ [true])) := by
              simpa using (revBinary_two_mul (n := bitsToNat (u ++ [true]))
                (Nat.ne_of_gt hpos))
            _ = false :: (u ++ [true]) := by rw [ih]
            _ = (false :: u) ++ [true] := by rfl
      | true =>
          calc
            revBinary (bitsToNat (true :: (u ++ [true])))
                = revBinary (2 * bitsToNat (u ++ [true]) + 1) := by simp [bitsToNat]
            _ = true :: revBinary (bitsToNat (u ++ [true])) := by
              simpa using (revBinary_two_mul_add_one (n := bitsToNat (u ++ [true])))
            _ = true :: (u ++ [true]) := by rw [ih]
            _ = (true :: u) ++ [true] := by rfl

/-- A Lyndon binary word ending in `true` corresponds to an actual
`A328596` number. -/
theorem inA328596_of_isLyndon_append_true {w : BitWord} (h : IsLyndon w)
    (hw : ∃ u, w = u ++ [true]) : InA328596 (bitsToNat w) := by
  rcases hw with ⟨u, rfl⟩
  constructor
  · exact bitsToNat_pos_append_true u
  · simpa [revBinary_bitsToNat_append_true] using h

/-- The rank of `n` inside A328596.

This is computed by filtering the finite prefix `0, 1, ..., n - 1`.
-/
def a328596Rank (n : Nat) : Nat :=
  ((List.range n).filter inA328596Bool).length

/-- The prime attached to the `A328596`-rank of `n`. -/
def nextPrimeAfter (n : Nat) : Nat :=
  Nat.find (show ∃ m : Nat, n < m ∧ Nat.Prime m from by
    obtain ⟨p, hle, hp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨p, by omega, hp⟩)

/-- The `k`-th prime, defined by iterating `nextPrimeAfter`. -/
def primeAt : Nat → Nat
  | 0 => 2
  | n + 1 => nextPrimeAfter (primeAt n)

/-- The prime attached to the `A328596`-rank of `n`. -/
def primeOfA328596 (n : Nat) : Nat := primeAt (a328596Rank n)

/-- The prime attached to a binary word, after converting it to a natural number. -/
def primeOfWord (w : BitWord) : Nat := primeOfA328596 (bitsToNat w)

/-- The longest Lyndon prefix length of a binary word. -/
def longestLyndonPrefixLen (w : BitWord) : Nat :=
  Nat.findGreatest (fun k => 0 < k ∧ isLyndonBool (w.take k)) w.length

/-- The longest Lyndon prefix length is bounded by the word length. -/
theorem longestLyndonPrefixLen_le (w : BitWord) : longestLyndonPrefixLen w ≤ w.length := by
  exact Nat.findGreatest_le _

/-- If the greedy prefix length is positive, that prefix is genuinely Lyndon. -/
theorem longestLyndonPrefix_isLyndon {w : BitWord}
    (h : 0 < longestLyndonPrefixLen w) : IsLyndon (w.take (longestLyndonPrefixLen w)) := by
  have hspec := (Nat.findGreatest_eq_iff (P := fun k => 0 < k ∧ isLyndonBool (w.take k))
      (k := w.length) (m := longestLyndonPrefixLen w)).1 rfl
  have hbool : isLyndonBool (w.take (longestLyndonPrefixLen w)) = true := by
    exact (hspec.2.1 (Nat.ne_of_gt h)).2
  exact (isLyndonBool_eq_true_iff (w := w.take (longestLyndonPrefixLen w))).1 hbool

/-- Any nonempty binary word has a positive Lyndon prefix length. -/
theorem longestLyndonPrefixLen_pos {w : BitWord} (hw : w ≠ []) :
    0 < longestLyndonPrefixLen w := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons b w =>
    refine (Nat.findGreatest_pos
      (P := fun k => 0 < k ∧ isLyndonBool ((b :: w).take k))
      (k := (b :: w).length)).2 ?_
    refine ⟨1, by decide, by simp, ?_⟩
    simpa using (isLyndonBool_eq_true_iff (w := [b])).2 (isLyndon_singleton b)

/-- The greedy Lyndon prefix of a binary word ending in `true` also ends in `true`. -/
theorem longestLyndonPrefixLen_ends_true {w : BitWord} (hw : ∃ u, w = u ++ [true]) :
    ∃ u, w.take (longestLyndonPrefixLen w) = u ++ [true] := by
  rcases w with _ | b t
  · rcases hw with ⟨u, hu⟩
    simp at hu
  · cases b with
    | true =>
        by_cases h1 : longestLyndonPrefixLen (true :: t) = 1
        · refine ⟨[], ?_⟩
          simpa [h1] using rfl
        · have hpos : 0 < longestLyndonPrefixLen (true :: t) :=
            longestLyndonPrefixLen_pos (by simp)
          have hlt : 1 < longestLyndonPrefixLen (true :: t) := by omega
          have hly : IsLyndon ((true :: t).take (longestLyndonPrefixLen (true :: t))) :=
            longestLyndonPrefix_isLyndon (w := true :: t) hpos
          rcases hly.last_eq_true_of_lt_length hlt with ⟨u, hu⟩
          exact ⟨u, hu⟩
    | false =>
        let p : Bool → Bool := fun x => decide (x = false)
        have htake_ne_nil : (false :: t).takeWhile p ≠ [] := by
          intro hnil
          rw [List.takeWhile_eq_nil_iff] at hnil
          have hlen : 0 < (false :: t).length := by simp
          have hcontra := hnil hlen
          simp [p] at hcontra
        have htake_all_false : ∀ x ∈ (false :: t).takeWhile p, x = false := by
          intro x hx
          have hpx := List.mem_takeWhile_imp (p := p) hx
          simp [p] at hpx
        have hrep : (false :: t).takeWhile p = List.replicate ((false :: t).takeWhile p).length false := by
          exact (List.eq_replicate_length).2 htake_all_false
        have hdrop_ne_nil : (false :: t).dropWhile p ≠ [] := by
          intro hnil
          rw [List.dropWhile_eq_nil_iff] at hnil
          rcases hw with ⟨u, hu⟩
          have hmem : true ∈ (false :: t) := by
            rw [hu]
            simp
          have hfalse : p true := hnil true hmem
          simp [p] at hfalse
        have hdrop_pos : 0 < ((false :: t).dropWhile p).length := by
          exact Nat.pos_of_ne_zero hdrop_ne_nil
        have hhead_not_false : ¬ p (((false :: t).dropWhile p).get ⟨0, hdrop_pos⟩) :=
          List.dropWhile_get_zero_not (p := p) (l := false :: t) hdrop_pos
        rcases List.exists_cons_of_ne_nil hdrop_ne_nil with ⟨c, s, hcons⟩
        have hc : c = true := by
          rw [hcons] at hhead_not_false
          cases c <;> simp [p] at hhead_not_false
        have hcons' : (false :: t).dropWhile p = true :: s := by
          rw [hcons, hc]
        have hsplit : false :: t = (false :: t).takeWhile p ++ (true :: s) := by
          rw [← List.takeWhile_append_dropWhile (p := p), hcons']
        have hprefix : (false :: t).take (((false :: t).takeWhile p).length + 1)
            = (false :: t).takeWhile p ++ [true] := by
          rw [hsplit]
          simp
        have hly : IsLyndon ((false :: t).takeWhile p ++ [true]) := by
          simpa [hrep] using zeroes_then_one_isLyndon ((false :: t).takeWhile p).length
        have hlen_le : ((false :: t).takeWhile p).length + 1 ≤ longestLyndonPrefixLen (false :: t) := by
          refine Nat.le_findGreatest ?_ ?_
          · rw [hsplit]
            omega
          · constructor
            · omega
            · simpa [hprefix] using
                (isLyndonBool_eq_true_iff
                  (w := (false :: t).take (((false :: t).takeWhile p).length + 1))).2 hly
        have hgt : 1 < longestLyndonPrefixLen (false :: t) := by
          have h2 : 1 < ((false :: t).takeWhile p).length + 1 := by omega
          exact lt_of_lt_of_le h2 hlen_le
        have hlyprefix : IsLyndon ((false :: t).take (longestLyndonPrefixLen (false :: t))) :=
          longestLyndonPrefix_isLyndon (w := false :: t) (Nat.pos_of_lt hgt)
        rcases hlyprefix.last_eq_true_of_lt_length hgt with ⟨u, hu⟩
        exact ⟨u, hu⟩

/-- A greedy Lyndon factorization of a binary word.

This is an executable scaffold for the Chen-Fox-Lyndon factorization.
The correctness proof will come later.
-/
def lyndonFactors : BitWord → List BitWord
  | [] => []
  | w =>
      let k := longestLyndonPrefixLen w
      if hk : k = 0 then [w] else w.take k :: lyndonFactors (w.drop k)
termination_by w => w.length
decreasing_by
  simp_wf
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have hkle : k ≤ w.length := longestLyndonPrefixLen_le w
  omega

/-- The greedy factorization recombines to the original word. -/
theorem lyndonFactors_flatten (w : BitWord) : (lyndonFactors w).flatten = w := by
  let P : Nat → Prop := fun n => ∀ w : BitWord, w.length = n → (lyndonFactors w).flatten = w
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih w hw
    cases w with
    | nil =>
        subst hw
        simp [P, lyndonFactors]
    | cons b w' =>
        subst hw
        dsimp [P] at *
        simp [lyndonFactors]
        let k := longestLyndonPrefixLen (b :: w')
        by_cases hk : k = 0
        · simp [k, hk]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
          have hkle : k ≤ (b :: w').length := longestLyndonPrefixLen_le _
          have hlt : ((b :: w').drop k).length < (b :: w').length := by
            rw [List.length_drop]
            omega
          have hrec : (lyndonFactors ((b :: w').drop k)).flatten = (b :: w').drop k :=
            ih ((b :: w').drop k).length hlt ((b :: w').drop k) rfl
          simp [k, hk, hrec, List.take_append_drop, hkle]
  have hmain : P w.length := Nat.strong_induction_on w.length hP
  exact hmain w rfl

/-- Every factor produced by the greedy decomposition is Lyndon. -/
theorem lyndonFactors_mem_isLyndon (w : BitWord) :
    ∀ x ∈ lyndonFactors w, IsLyndon x := by
  let P : Nat → Prop := fun n => ∀ w : BitWord, w.length = n → ∀ x ∈ lyndonFactors w, IsLyndon x
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih w hw x hx
    cases w with
    | nil =>
        simp [lyndonFactors] at hw hx
    | cons b w' =>
        subst hw
        let k := longestLyndonPrefixLen (b :: w')
        by_cases hk : k = 0
        · have hkpos : 0 < k := longestLyndonPrefixLen_pos (by simp)
          exact (Nat.ne_of_gt hkpos hk).elim
        · simp [lyndonFactors, k, hk] at hx ⊢
          rcases hx with rfl | hx
          · exact longestLyndonPrefix_isLyndon (w := b :: w') (Nat.pos_of_ne_zero hk)
          · have hlt : ((b :: w').drop k).length < (b :: w').length := by
              have hkle : k ≤ (b :: w').length := longestLyndonPrefixLen_le _
              rw [List.length_drop]
              omega
            have hrec : ∀ y ∈ lyndonFactors ((b :: w').drop k), IsLyndon y :=
              ih ((b :: w').drop k).length hlt ((b :: w').drop k) rfl
            exact hrec x hx
  have hmain : P w.length := Nat.strong_induction_on w.length hP
  exact hmain w rfl

/-- The A348268 value attached to `n`.

For `n > 0`, we factor the reversed binary word of `n` into Lyndon pieces,
convert each Lyndon piece to its associated prime, and multiply the primes.
-/
def a348268 (n : Nat) : Nat :=
  if _h : n = 0 then 1 else
    ((lyndonFactors (revBinary n)).map primeOfWord).prod

example : bitsToNat [false, true] = 2 := by
  simp [bitsToNat]

example : primeAt 0 = 2 := rfl

theorem nextPrimeAfter_two : nextPrimeAfter 2 = 3 := by
  rw [nextPrimeAfter]
  have h : ∃ m : Nat, 2 < m ∧ Nat.Prime m := by
    refine ⟨3, ?_, ?_⟩
    · omega
    · decide
  apply (Nat.find_eq_iff h).2
  constructor
  · constructor
    · omega
    · decide
  · intro n hn hpn
    omega

theorem primeAt_one : primeAt 1 = 3 := by
  simpa [primeAt] using nextPrimeAfter_two

example : longestLyndonPrefixLen [false, true, false, true] = 2 := by
  decide

example : a348268 0 = 1 := by
  simp [a348268]

end A348268