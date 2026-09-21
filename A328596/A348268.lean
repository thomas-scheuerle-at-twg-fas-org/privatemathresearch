import Mathlib.Data.Nat.Find
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