import Mathlib.Data.Nat.PadicValNat
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

theorem clear_lsb_shape_mem_a328596 (k r : Nat) (hr : r ≠ 0)
    (hA : InA328596 (2 ^ k * (2 * r + 1))) :
    InA328596 (2 ^ (k + 1) * r) := by
  constructor
  · exact Nat.mul_pos (by positivity) (Nat.pos_of_ne_zero hr)
  · rcases revBinary_pos_ends_with_true (Nat.pos_of_ne_zero hr) with ⟨u, hu⟩
    have hword : IsSuffixLyndon (List.replicate k false ++ (true :: (u ++ [true]))) := by
      have hly : IsLyndon (List.replicate k false ++ (true :: (u ++ [true]))) := by
        simpa [revBinary_pow_two_mul_odd, hu] using hA.2
      exact hly.toIsSuffixLyndon
    have hsmall : IsLyndon (List.replicate (k + 1) false ++ (u ++ [true])) :=
      zero_block_step_isLyndon k u hword
    simpa [revBinary_mul_pow_two (k + 1) r hr, hu, List.append_assoc] using hsmall

theorem a328596_additive {n : Nat} (hn : 1 < n) (hA : InA328596 n) :
    ∃ a b, InA328596 a ∧ InA328596 b ∧ n = a + b := by
  let k := padicValNat 2 n
  let q := n.divMaxPow 2
  have hfact : 2 ^ k * q = n := by
    simpa [k, q] using (pow_padicValNat_mul_divMaxPow 2 n)
  by_cases hq1 : q = 1
  · have hkshape : n = 2 ^ k := by
      simpa [hq1] using hfact.symm
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · have hnone : n = 1 := by simpa [hk0] using hkshape
      omega
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
      refine ⟨2 ^ j, 2 ^ j, two_pow_mem_a328596 j, two_pow_mem_a328596 j, ?_⟩
      calc
        n = 2 ^ (j + 1) := by simpa [hj] using hkshape
        _ = 2 ^ j + 2 ^ j := by
          rw [Nat.pow_succ]
          nth_rw 2 [show 2 = 1 + 1 by rfl]
          rw [Nat.mul_add]
          simp
  · have hqpos : 0 < q := by
      apply Nat.pos_of_ne_zero
      intro hq0
      rw [hq0, mul_zero] at hfact
      exact (Nat.ne_of_gt hA.1) hfact.symm
    have hqodd : ¬ 2 ∣ q := by
      simpa [q] using (Nat.not_dvd_divMaxPow (by decide : 1 < 2) (Nat.ne_of_gt hA.1))
    have hbodd : q.bodd = true := by
      cases hqbod : q.bodd <;> simp [Nat.mod_two_of_bodd, hqbod, Nat.dvd_iff_mod_eq_zero] at hqodd ⊢
    let r := q.div2
    have hqshape : q = 2 * r + 1 := by
      have hbit : Nat.bit true r = q := by
        simpa [r, hbodd] using (Nat.bit_bodd_div2 q)
      simpa [Nat.bit, r] using hbit.symm
    have hr : r ≠ 0 := by
      intro hr0
      have : q = 1 := by simpa [hqshape, r, hr0]
      exact hq1 this
    have hshape : n = 2 ^ k * (2 * r + 1) := by
      rw [← hfact, hqshape]
    have hsmall : InA328596 (2 ^ (k + 1) * r) := by
      have hAshape : InA328596 (2 ^ k * (2 * r + 1)) := by
        simpa [hshape] using hA
      exact clear_lsb_shape_mem_a328596 k r hr hAshape
    refine ⟨2 ^ k, 2 ^ (k + 1) * r, two_pow_mem_a328596 k, hsmall, ?_⟩
    calc
      n = 2 ^ k * (2 * r + 1) := hshape
      _ = 2 ^ k + 2 ^ (k + 1) * r := by
        rw [Nat.mul_add, Nat.mul_one, Nat.pow_succ]
        ac_rfl

end A328596
