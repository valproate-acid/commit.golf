import Mathlib

/-! Research primitive only. This is not an image certificate or a submission.
An occupied binary cap of height eight has at most 128 frontier hashes. -/
namespace CommitGolfCandidate
inductive MarkTree : Nat → Type
  | leaf (marked : Bool) : MarkTree 0
  | node {height : Nat} (left right : MarkTree height) : MarkTree (height + 1)

def occupied : {height : Nat} → MarkTree height → Bool
  | _, .leaf marked => marked
  | _, .node left right => occupied left || occupied right

def frontier : {height : Nat} → MarkTree height → Nat
  | _, .leaf _ => 0
  | _, .node left right =>
    if occupied left then
      if occupied right then frontier left + frontier right else frontier left + 1
    else if occupied right then frontier right + 1 else 0

/-- Structural boundary bound, independent of the number or shape of marked leaves. -/
theorem frontier_bound (height : Nat) (tree : MarkTree height) :
    frontier tree ≤ if height = 0 then 0 else 2 ^ (height - 1) := by
  induction height with
  | zero => cases tree; simp [frontier]
  | succ height ih =>
    cases tree with
    | node left right =>
      cases height with
      | zero =>
        cases left with
        | leaf a =>
          cases right with
          | leaf b => cases a <;> cases b <;> decide
      | succ depth =>
        have leftBound : frontier left ≤ 2 ^ depth := by simpa using ih left
        have rightBound : frontier right ≤ 2 ^ depth := by simpa using ih right
        have positive : 1 ≤ 2 ^ depth := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
        simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
        unfold frontier
        split <;> split <;> rw [Nat.pow_succ] <;> omega

theorem height_eight_frontier (tree : MarkTree 8) : frontier tree ≤ 128 := by
  simpa using frontier_bound 8 tree

end CommitGolfCandidate


