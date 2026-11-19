import CommitGolfCandidate.TwoPermutationPackedOpeningCapMoves
import CommitGolfCandidate.TwoPermutationPackedOpeningCapWrites
import CommitGolfCandidate.TwoPermutationPackedOpeningSchedule

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64

open Opening (CapSpan proofBase cap_span_node cap_span_children cap_frontier_nodes_small)

def EmitCap : Prop :=
  ∀ (groups : List Nat) (state : MachineState) (node dest : Nat),
    node < 512 → CapPosition groups state node dest →
    state.pc = 0x19b8 → proofBase ≤ dest → dest % 2 = 0 → dest+30 ≤ MEMORY_BYTES →
    ∃ after, RunsOpeningBlock state after 33 ∧ after.pc = 0x1a3c ∧
      CapPosition groups after node (dest+30) ∧ CapWrites state after dest [node]

private theorem lookup_block (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x199c) :
    let after := cursorVisitPrefix state 4
    RunsOpeningBlock state after 4 ∧
    after.pc = (if capIsMarked groups node height then 0x19ac else 0x19b8) ∧
    CapPosition groups after node dest ∧ after.mem = state.mem := by
  obtain ⟨_, target, nextNode, nextDest, memory, context⟩ :=
    cap_lookup state groups node height 0 false span position.context pc position.nodeWord
  exact ⟨fun fuel coins => (cap_lookup state groups node height fuel coins span position.context pc
    position.nodeWord).1, target, ⟨context, nextNode.trans position.nodeWord, nextDest.trans position.destWord⟩, memory⟩

private theorem walk_unmarked (emitCap : EmitCap) (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x199c) (mark : capIsMarked groups node height = false)
    (separate : proofBase ≤ dest) (aligned : dest % 2 = 0) (fits : dest+30 ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after 37 ∧ after.pc = 0x1a3c ∧
      CapPosition groups after node (dest+30) ∧ CapWrites state after dest [node] := by
  obtain ⟨lookup, branch, looked, stable⟩ := lookup_block groups state node height dest span position pc
  have target : (cursorVisitPrefix state 4).pc = 0x19b8 := by simpa [mark] using branch
  obtain ⟨after, emit, next, final, writes⟩ := emitCap groups _ node dest (cap_span_node node height span).2
    looked target separate aligned fits
  exact ⟨_, lookup.next emit, next, final, writes.move stable.symm rfl⟩

/-- The actual stackless cap cursor emits the recursively specified frontier in
left-to-right order. A subtree returns at its own advance label, before any
sibling traversal, and preserves memory outside the appended proof bytes. -/
theorem execute_cap_subtree (emitCap : EmitCap) (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x199c) (separate : proofBase ≤ dest) (aligned : dest % 2 = 0)
    (fits : dest + 30 * (capFrontierNodes groups node height).length ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (capSubtreeCycles groups node height) ∧
      after.pc = 0x1a3c ∧
      CapPosition groups after node (dest + 30 * (capFrontierNodes groups node height).length) ∧
      CapWrites state after dest (capFrontierNodes groups node height) := by
  induction height generalizing state node dest with
  | zero =>
    cases mark : capIsMarked groups node 0
    · have small : dest+30 ≤ MEMORY_BYTES := by simpa [capFrontierNodes, mark] using fits
      simpa [capSubtreeCycles, capFrontierNodes, mark] using
        walk_unmarked emitCap groups state node 0 dest span position pc mark separate aligned small
    · obtain ⟨lookup, branch, looked, mem⟩ := lookup_block groups state node 0 dest span position pc
      have target : (cursorVisitPrefix state 4).pc = 0x19ac := by simpa [mark] using branch
      obtain ⟨prune, next, final, memAfter⟩ := cap_prune_step groups _ node dest looked span target
      have bytes := cap_writes_empty state (cursorKnownPrefix (cursorVisitPrefix state 4) 1) dest (memAfter.trans mem)
      simpa [capFrontierNodes, capSubtreeCycles, mark] using
        (show ∃ after, RunsOpeningBlock state after 5 ∧ after.pc = 0x1a3c ∧
          CapPosition groups after node dest ∧ CapWrites state after dest [] from
            ⟨_, lookup.next prune, next, final, bytes⟩)
  | succ height ih =>
    cases mark : capIsMarked groups node (height+1)
    · have small : dest+30 ≤ MEMORY_BYTES := by simpa [capFrontierNodes, mark] using fits
      simpa [capSubtreeCycles, capFrontierNodes, mark] using
        walk_unmarked emitCap groups state node (height+1) dest span position pc mark separate aligned small
    · let left := capFrontierNodes groups (2*node) height
      let right := capFrontierNodes groups (2*node+1) height
      let midway := dest + 30*left.length
      have allFits : dest + 30 * (left ++ right).length ≤ MEMORY_BYTES := by
        simpa [capFrontierNodes, mark, left, right] using fits
      have leftFits : dest + 30 * left.length ≤ MEMORY_BYTES := by
        simp only [List.length_append, Nat.mul_add] at allFits
        omega
      have rightFits : midway + 30 * right.length ≤ MEMORY_BYTES := by
        simp only [midway, List.length_append, Nat.mul_add] at *
        omega
      obtain ⟨lookup, branch, looked, mem⟩ := lookup_block groups state node (height+1) dest span position pc
      have target : (cursorVisitPrefix state 4).pc = 0x19ac := by simpa [mark] using branch
      obtain ⟨descend, leftPC, leftPos, memLeft⟩ := cap_descend_step groups _ node height dest looked span target
      obtain ⟨leftSpan, rightSpan⟩ := cap_span_children node height span
      obtain ⟨leftEnd, ranLeft, leftDone, fromLeft, leftBytes⟩ :=
        ih _ (2*node) dest leftSpan leftPos leftPC separate aligned leftFits
      have positive := (cap_span_node node (height+1) span).1
      obtain ⟨across, rightPC, rightPos, memRight⟩ := advance_left_to_right groups leftEnd node midway
        positive (cap_span_node _ _ leftSpan).2 fromLeft leftDone
      obtain ⟨rightEnd, ranRight, rightDone, fromRight, rightBytes⟩ :=
        ih _ (2*node+1) midway rightSpan rightPos rightPC (by unfold midway; omega)
          (by unfold midway; omega) rightFits
      obtain ⟨up, finalPC, finalPos, memUp⟩ := advance_right_to_parent groups rightEnd node
        (midway + 30*right.length) positive (cap_span_node _ _ rightSpan).2 fromRight rightDone
      have leftWrites : CapWrites state (advanceRight leftEnd) dest left :=
        leftBytes.move ((memLeft.trans mem).symm) memRight
      have rightWrites : CapWrites (advanceRight leftEnd) (advanceUp rightEnd) midway right :=
        rightBytes.move rfl memUp
      have bytes := leftWrites.join rightWrites separate
        (cap_frontier_nodes_small groups _ _ rightSpan) allFits
      have trace := ((((lookup.next descend).next ranLeft).next across).next ranRight).next up
      refine ⟨advanceUp rightEnd, ?_, finalPC, ?_, ?_⟩
      · simp only [capSubtreeCycles, mark, ite_true]
        convert trace using 1
        omega
      · simpa only [capFrontierNodes, mark, ite_true, List.length_append, Nat.mul_add,
          ← Nat.add_assoc, left, right, midway] using finalPos
      · simpa only [capFrontierNodes, mark, ite_true, left, right] using bytes

end TwoPermutationPrototype.PackedOpening
