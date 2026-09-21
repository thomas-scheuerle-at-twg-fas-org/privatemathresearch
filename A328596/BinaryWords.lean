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

/-- Multiplying a positive number by `2^k` prefixes `k` zero bits in the
reversed binary expansion. -/
theorem revBinary_mul_pow_two (k n : Nat) (hn : n ≠ 0) :
    revBinary (2 ^ k * n) = List.replicate k false ++ revBinary n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hk : 2 ^ k * n ≠ 0 := by
        exact Nat.mul_ne_zero (pow_ne_zero k (by decide)) hn
      have hmul : 2 ^ (k + 1) * n = 2 * (2 ^ k * n) := by
        rw [Nat.pow_succ]
        ac_rfl
      calc
        revBinary (2 ^ (k + 1) * n) = revBinary (2 * (2 ^ k * n)) := by rw [hmul]
        _ = false :: revBinary (2 ^ k * n) := by
          simp [revBinary_two_mul hk]
        _ = false :: (List.replicate k false ++ revBinary n) := by
          rw [ih]
        _ = List.replicate (k + 1) false ++ revBinary n := by
          simp [List.replicate]

/-- Splitting off the least-significant `1` from an odd factor exposes the
shape used in the additive decomposition argument. -/
theorem revBinary_pow_two_mul_odd (k r : Nat) :
    revBinary (2 ^ k * (2 * r + 1)) = List.replicate k false ++ (true :: revBinary r) := by
  calc
    revBinary (2 ^ k * (2 * r + 1)) = List.replicate k false ++ revBinary (2 * r + 1) := by
      exact revBinary_mul_pow_two k (2 * r + 1) (by omega)
    _ = List.replicate k false ++ (true :: revBinary r) := by
      simp [revBinary_two_mul_add_one]

/-- Clearing the least-significant set bit of `2^k * (2r + 1)` for `r > 0`
adds one more leading `0` in reversed binary. -/
theorem revBinary_clear_lsb (k r : Nat) (hr : r ≠ 0) :
    revBinary (2 ^ k * (2 * r + 1) - 2 ^ k) =
      List.replicate (k + 1) false ++ revBinary r := by
  have hsub : 2 ^ k * (2 * r + 1) - 2 ^ k = 2 ^ k * (2 * r) := by
    calc
      2 ^ k * (2 * r + 1) - 2 ^ k = 2 ^ k * (2 * r + 1) - 2 ^ k * 1 := by simp
      _ = 2 ^ k * ((2 * r + 1) - 1) := by rw [Nat.mul_sub_left_distrib]
      _ = 2 ^ k * (2 * r) := by simp
  have hmul : 2 ^ k * (2 * r) = 2 ^ (k + 1) * r := by
    rw [Nat.pow_succ]
    ac_rfl
  calc
    revBinary (2 ^ k * (2 * r + 1) - 2 ^ k)
        = revBinary (2 ^ k * (2 * r)) := by rw [hsub]
    _ = revBinary (2 ^ (k + 1) * r) := by rw [hmul]
    _ = List.replicate (k + 1) false ++ revBinary r := by
          exact revBinary_mul_pow_two (k + 1) r hr

/-- Every positive reversed binary expansion ends with a `1`. -/
theorem revBinary_pos_ends_with_true {n : Nat} (hn : 0 < n) :
    ∃ u, revBinary n = u ++ [true] := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      by_cases hodd : n.bodd = true
      · cases hdiv : n.div2 with
        | zero =>
            use []
            have hn1 : n = 1 := by
              have hbit : Nat.bit true 0 = n := by
                simpa [hodd, hdiv] using Nat.bit_bodd_div2 n
              simpa [Nat.bit] using hbit.symm
            simp [hn1, revBinary_one]
        | succ m =>
            have hsmall : Nat.succ m < n := by
              simpa [hdiv] using Nat.binaryRec_decreasing hn0
            rcases ih (Nat.succ m) hsmall (Nat.succ_pos _) with ⟨u, hu⟩
            use true :: u
            have hbit : Nat.bit true (Nat.succ m) = n := by
              simpa [hodd, hdiv] using Nat.bit_bodd_div2 n
            have hnexpr : n = 2 * Nat.succ m + 1 := by
              simpa [Nat.bit] using hbit.symm
            rw [hnexpr, revBinary_two_mul_add_one, hu]
            simp
      · have hodd0 : n.bodd = false := by
          cases hbod : n.bodd <;> simp_all
        cases hdiv : n.div2 with
        | zero =>
            have : False := by
              have hbit : Nat.bit false 0 = n := by
                simpa [hodd0, hdiv] using Nat.bit_bodd_div2 n
              have hnzero : n = 0 := by
                simpa [Nat.bit] using hbit.symm
              exact hn0 hnzero
            exact this.elim
        | succ m =>
            have hsmall : Nat.succ m < n := by
              simpa [hdiv] using Nat.binaryRec_decreasing hn0
            rcases ih (Nat.succ m) hsmall (Nat.succ_pos _) with ⟨u, hu⟩
            use false :: u
            have hbit : Nat.bit false (Nat.succ m) = n := by
              simpa [hodd0, hdiv] using Nat.bit_bodd_div2 n
            have hnexpr : n = 2 * Nat.succ m := by
              simpa [Nat.bit] using hbit.symm
            rw [hnexpr, revBinary_two_mul (by simp [hdiv]), hu]
            simp

/-- Any binary word ending in `true` is the reversed binary expansion of the
natural number obtained from its bits. -/

example : revBinary 26 = [false, true, false, true, true] := rfl

end A328596
