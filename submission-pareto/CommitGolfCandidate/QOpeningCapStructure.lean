import CommitGolfCandidate.QOpeningMarks

namespace TwoPermutationPrototype.QOpening
open TwoPermutationPrototype.Sampling

/-- Coordinates for an aligned subtree of the height-eight cap. The scaled interval
is its exact span of cap-leaf slots. -/
structure CapSpan (node height : Nat) : Prop where
  heightBound : height ≤ 8
  start : 256 ≤ node * 2 ^ height
  finish : (node + 1) * 2 ^ height ≤ 512

theorem cap_span_root : CapSpan 1 8 := ⟨by decide, by decide, by decide⟩

theorem cap_span_children (node height : Nat) (span : CapSpan node (height + 1)) :
    CapSpan (2 * node) height ∧ CapSpan (2 * node + 1) height := by
  have bound := span.heightBound
  have start := span.start
  have finish := span.finish
  have leftStart : (2 * node) * 2 ^ height = node * 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    ring
  have rightEnd : (2 * node + 1 + 1) * 2 ^ height = (node + 1) * 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    ring
  refine ⟨⟨by omega, by omega, ?_⟩, ⟨by omega, ?_, by omega⟩⟩
  · exact (Nat.mul_le_mul_right _ (by omega : 2 * node + 1 ≤ 2 * node + 1 + 1)).trans
      (rightEnd.trans_le finish)
  · exact start.trans (leftStart.symm.le.trans (Nat.mul_le_mul_right _ (by omega)))

theorem cap_span_node (node height : Nat) (span : CapSpan node height) :
    0 < node ∧ node < 512 := by
  have low := span.start
  have high := span.finish
  have finish : node + 1 ≤ (node + 1) * 2 ^ height := by
    exact Nat.le_mul_of_pos_right _ (by positivity)
  constructor
  · by_contra zero
    have eq : node = 0 := by omega
    simp [eq] at low
  · omega

theorem cap_span_is_leaf (node : Nat) (span : CapSpan node 0) : 256 ≤ node := by
  simpa using span.start

theorem cap_span_is_internal (node height : Nat) (span : CapSpan node (height + 1)) :
    node < 256 := by
  have pow : 2 ≤ 2 ^ (height + 1) := by
    rw [Nat.pow_succ]
    have positive : 0 < 2 ^ height := by positivity
    omega
  have growth := (Nat.mul_le_mul_left (node + 1) pow).trans span.finish
  omega

theorem cap_span_height (node height : Nat) (span : CapSpan node height) :
    capHeight node = height := by
  have positive := (cap_span_node node height span).1
  have exponent := span.heightBound
  have leftScale : 2 ^ (8 - height) * 2 ^ height = 256 := by
    rw [← Nat.pow_add, show 8 - height + height = 8 by omega]
  have rightScale : 2 ^ ((8 - height) + 1) * 2 ^ height = 512 := by
    rw [← Nat.pow_add, show (8 - height) + 1 + height = 9 by omega]
  have powerPos : 0 < 2 ^ height := by positivity
  have exactLog : node.log2 = 8 - height := by
    apply (Nat.log2_eq_iff (by omega)).mpr
    constructor
    · exact Nat.le_of_mul_le_mul_right (leftScale.trans_le span.start) powerPos
    · have upper : (node + 1) * 2 ^ height ≤ 2 ^ ((8 - height) + 1) * 2 ^ height :=
        span.finish.trans rightScale.symm.le
      have := Nat.le_of_mul_le_mul_right upper powerPos
      omega
  unfold capHeight
  omega

/-- The cycles from visiting a node to starting its own advance block. The two
internal-child advances each cost six cycles and are included in the parent. -/
def capSubtreeCycles (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => if capIsMarked groups node 0 then 5 else 15
  | height + 1 =>
    if capIsMarked groups node (height + 1) then
      19 + capSubtreeCycles groups (2 * node) height + capSubtreeCycles groups (2 * node + 1) height
    else 15

theorem cap_subtree_cycle_bound (groups : List Nat) (node height : Nat) :
    capSubtreeCycles groups node height ≤ 19 * (2 ^ (height + 1) - 1) := by
  induction height generalizing node with
  | zero => simp [capSubtreeCycles]; split <;> decide
  | succ height ih =>
    have left := ih (2 * node)
    have right := ih (2 * node + 1)
    rw [capSubtreeCycles, Nat.pow_succ 2 (height + 1)]
    have positive : 0 < 2 ^ (height + 1) := by positivity
    split <;> omega

end TwoPermutationPrototype.QOpening
