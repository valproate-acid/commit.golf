import CommitGolfCandidate.TwoPermutationTranscript

namespace TwoPermutationPrototype.QOpening
open TwoPermutationPrototype.Sampling

/-- The pending right subtrees encoded by the current heap node. Traversing upward
over an odd node closes both children. An even node has one pending sibling. -/
def pendingRight (node height : Nat) : List (Nat × Nat) :=
  if node ≤ 1 then []
  else
    let rest := pendingRight (node / 2) (height + 1)
    if node % 2 = 0 then (node + 1, height) :: rest else rest
termination_by node
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem pending_left_child (node height : Nat) (positive : 0 < node) :
    pendingRight (2 * node) height =
      (2 * node + 1, height) :: pendingRight node (height + 1) := by
  conv_lhs => rw [pendingRight]
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (2 * node) / 2 = node by omega]

theorem pending_right_child (node height : Nat) (positive : 0 < node) :
    pendingRight (2 * node + 1) height = pendingRight node (height + 1) := by
  conv_lhs => rw [pendingRight]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), show (2 * node + 1) / 2 = node by omega]

theorem pending_visit_sibling (node height : Nat) (nonRoot : 1 < node)
    (even : node % 2 = 0) :
    pendingRight node height = (node + 1, height) :: pendingRight (node + 1) height := by
  have sameParent : (node + 1) / 2 = node / 2 := by omega
  conv_lhs => rw [pendingRight]
  conv_rhs => arg 2; rw [pendingRight]
  simp [Nat.not_le_of_gt nonRoot, show ¬ node + 1 ≤ 1 by omega,
    even, show ¬ (node + 1) % 2 = 0 by omega, sameParent]

theorem pending_ascend (node height : Nat) (nonRoot : 1 < node) (odd : node % 2 = 1) :
    pendingRight node height = pendingRight (node / 2) (height + 1) := by
  conv_lhs => rw [pendingRight]
  simp [Nat.not_le_of_gt nonRoot, odd]

def remainingFrontier (groups : List Nat) (node height : Nat) : List Nat :=
  capFrontierNodes groups node height ++
    (pendingRight node height).flatMap (fun (subtree, height) => capFrontierNodes groups subtree height)

theorem frontier_descend (groups : List Nat) (node height : Nat) (positive : 0 < node)
    (marked : capIsMarked groups node (height + 1) = true) :
    remainingFrontier groups node (height + 1) =
      remainingFrontier groups (2 * node) height := by
  simp [remainingFrontier, capFrontierNodes, marked, pending_left_child _ _ positive, List.append_assoc]

theorem frontier_emit (groups : List Nat) (node height : Nat)
    (unmarked : capIsMarked groups node height = false) :
    remainingFrontier groups node height =
      node :: (pendingRight node height).flatMap
        (fun (subtree, height) => capFrontierNodes groups subtree height) := by
  cases height <;> simp [remainingFrontier, capFrontierNodes, unmarked]

theorem frontier_skip_leaf (groups : List Nat) (node : Nat)
    (marked : capIsMarked groups node 0 = true) :
    remainingFrontier groups node 0 =
      (pendingRight node 0).flatMap (fun (subtree, height) => capFrontierNodes groups subtree height) := by
  simp [remainingFrontier, capFrontierNodes, marked]

theorem frontier_root (groups : List Nat) (height : Nat) :
    remainingFrontier groups 1 height = capFrontierNodes groups 1 height := by
  simp [remainingFrontier, pendingRight]

end TwoPermutationPrototype.QOpening
