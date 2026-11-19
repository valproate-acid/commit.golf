import CommitGolfCandidate.QOpeningFrontier
import CommitGolfCandidate.QOpeningGeometry

namespace TwoPermutationPrototype.QOpening
open CommitGolf TwoPermutationPrototype.Sampling RiscvZkvm.Rv64

set_option maxRecDepth 4096

def capHeight (node : Nat) : Nat := 8 - node.log2

theorem cap_leaf_height (node : Fin 512) (leaf : 256 ≤ node.val) :
    capHeight node.val = 0 := by
  revert node
  decide

theorem cap_child_heights (node : Fin 256) (positive : 0 < node.val) :
    capHeight node.val = capHeight (2 * node.val) + 1 ∧
      capHeight (2 * node.val + 1) = capHeight (2 * node.val) := by
  revert node
  decide

def markWord (groups : List Nat) (node : Nat) : Word :=
  BitVec.ofNat 64 (capIsMarked groups node (capHeight node)).toNat

theorem mark_word_parent (groups : List Nat) (node : Fin 256) (positive : 0 < node.val) :
    markWord groups node.val =
      markWord groups (2 * node.val) ||| markWord groups (2 * node.val + 1) := by
  have ⟨parentHeight, rightHeight⟩ := cap_child_heights node positive
  simp only [markWord, parentHeight, rightHeight, cap_marked_children]
  cases capIsMarked groups (2 * node.val) (capHeight (2 * node.val)) <;>
    cases capIsMarked groups (2 * node.val + 1) (capHeight (2 * node.val)) <;> rfl

theorem mark_word_leaf (groups : List Nat) (node : Fin 512) (leaf : 256 ≤ node.val) :
    markWord groups node.val = if node.val ∈ groups then 1 else 0 := by
  rw [markWord, cap_leaf_height node leaf]
  have member : capIsMarked groups node.val 0 = true ↔ node.val ∈ groups := by
    simp only [capIsMarked, List.any_eq_true, Nat.pow_zero, Nat.div_one, beq_iff_eq]
    constructor
    · rintro ⟨group, belongs, equal⟩
      exact equal ▸ belongs
    · intro belongs
      exact ⟨node.val, belongs, rfl⟩
  by_cases belongs : node.val ∈ groups
  · simp [member.mpr belongs, belongs]
  · have absent : capIsMarked groups node.val 0 = false := Bool.eq_false_iff.mpr
      (fun marked => belongs (member.mp marked))
    simp [absent, belongs]

/-- The mark associated with a lower record is exactly its transcript cap group. -/
theorem lower_node_cap_group (index : Index) : lowerNode index 16 = capGroup index := rfl

def markParent (marks : Nat → Word) (node : Nat) : Nat → Word :=
  fun other => if other = node then marks (2 * node) ||| marks (2 * node + 1) else marks other

/-- Sweep the internal cap nodes from the last parent down to the root. -/
def markSweep (marks : Nat → Word) : Nat → Nat → Word
  | 0 => marks
  | next + 1 => markSweep (markParent marks (next + 1)) next

theorem mark_sweep_correct (marks : Nat → Word) (groups : List Nat) (remaining : Nat)
    (internal : remaining < 256)
    (finished : ∀ node, remaining < node → node < 512 → marks node = markWord groups node) :
    ∀ node, 0 < node → node < 512 → markSweep marks remaining node = markWord groups node := by
  induction remaining generalizing marks with
  | zero => exact finished
  | succ remaining ih =>
    apply ih _ (by omega)
    intro node above below
    by_cases next : node = remaining + 1
    · subst node
      have child := mark_word_parent groups ⟨remaining + 1, internal⟩
        (show 0 < remaining + 1 by omega)
      change markWord groups (remaining + 1) = markWord groups (2 * (remaining + 1)) |||
        markWord groups (2 * (remaining + 1) + 1) at child
      rw [markParent, ite_eq_left rfl, finished _ (by omega) (by omega),
        finished _ (by omega) (by omega), child]
    · rw [markParent, ite_eq_right next, finished _ (by omega) below]

theorem mark_sweep_from_leaves (marks : Nat → Word) (groups : List Nat)
    (leafMarks : ∀ node, 256 ≤ node → node < 512 →
      marks node = if node ∈ groups then 1 else 0) :
    ∀ node, 0 < node → node < 512 → markSweep marks 255 node = markWord groups node := by
  apply mark_sweep_correct marks groups 255 (by decide)
  intro node greater bounded
  rw [leafMarks node (by omega) bounded]
  exact (mark_word_leaf groups ⟨node, bounded⟩ (show 256 ≤ node by omega)).symm

end TwoPermutationPrototype.QOpening
