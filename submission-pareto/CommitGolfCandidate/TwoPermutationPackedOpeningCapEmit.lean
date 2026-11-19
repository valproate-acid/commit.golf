import CommitGolfCandidate.TwoPermutationPackedOpeningCopy
import CommitGolfCandidate.TwoPermutationPackedOpeningCapSubtree

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (capDigestAddress cap_digest_bounds proofBase markBase trapdoorBase)

theorem ByteCopy.move {before after before' after' : MachineState} {source dest count : Nat}
    (copy : ByteCopy before after source dest count) (start : before'.mem = before.mem)
    (finish : after'.mem = after.mem) :
    ByteCopy before' after' source dest count := by
  constructor
  · intro i inside
    simpa only [MachineState.getByte, MachineState.getMem, start, finish] using copy.copied i inside
  · intro address outside
    simpa only [MachineState.getByte, MachineState.getMem, start, finish] using copy.frame address outside

theorem emit_cap : EmitCap := by
  intro groups state node dest bounded position pc separate aligned fits
  let src := capDigestAddress node
  let setup := capSource state
  let copied := copyState .cap setup
  let after := capAdvance copied
  have initial := cap_source_post state
  have final := cap_advance_post copied
  have source : setup.getReg .x7 = BitVec.ofNat 64 src := by
    rw [initial.2.2.1, position.context.heap, position.nodeWord, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 trapdoorBase + BitVec.ofNat 64 node * BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm node, ← BitVec.ofNat_add]
    rfl
  have destination := (initial.2.2.2 .x21 (by decide)).trans position.destWord
  have place : FieldInputs .cap setup src dest := by
    have ⟨sourceAlign, beforeProof⟩ := cap_digest_bounds _ bounded
    refine ⟨by rw [initial.1, pc]; rfl, source, destination, ?_, fits, ?_, aligned⟩
    · have bound := beforeProof.trans separate
      change src+30 ≤ dest
      change src+32 ≤ dest at bound
      omega
    · change src%2=0
      change src%8=0 at sourceAlign
      omega
  have finishPC : copied.pc = 0x1a38 := place.final_pc
  have setupRun : RunsOpeningBlock state setup 2 := fun fuel coins => execute_cap_source state pc fuel coins
  have advanceRun : RunsOpeningBlock copied after 1 := fun fuel coins => execute_cap_advance copied finishPC fuel coins
  have sameRegister (reg : Reg) (temp : reg ≠ .x7) (destReg : reg ≠ .x21) (scratch : reg ≠ .x31) :
      after.getReg reg = state.getReg reg :=
    (final.2.2.2 reg destReg).trans
      ((copy_register .cap setup reg scratch).trans (initial.2.2.2 reg temp))
  have proofCopy : ByteCopy state after src dest 30 := place.bytes.move initial.2.1.symm final.2.1
  refine ⟨after, (setupRun.next place.run).next advanceRun, ?_, ?_,
    proofCopy.cap_writes (fits.trans (by decide))⟩
  · rw [final.1, finishPC]
    rfl
  · refine ⟨?_, (sameRegister .x6 (by decide) (by decide) (by decide)).trans position.nodeWord, ?_⟩
    · apply position.context.of_preserved
      · intro reg member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> exact sameRegister _ (by decide) (by decide) (by decide)
      · intro n _ inside
        have before : markBase+8*n < proofBase := by
          have small := Opening.marks_before_trapdoor
          have heap : trapdoorBase ≤ proofBase := by decide
          omega
        have stable := place.words_before proofBase (markBase+8*n) before separate (by decide)
        have saved : after.mem = copied.mem := final.2.1
        have reads : setup.mem = state.mem := initial.2.1
        simpa only [Opening.machineMarks, MachineState.getMem, saved, reads] using stable
    · rw [final.2.2.1, copy_register .cap setup .x21 (by decide), destination]
      exact (BitVec.ofNat_add (n := 64) dest 30).symm

theorem cap_subtree (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (span : Opening.CapSpan node height) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x199c) (separate : proofBase ≤ dest) (aligned : dest % 2 = 0)
    (fits : dest+30*(Sampling.capFrontierNodes groups node height).length ≤ MEMORY_BYTES) :
    ∃ after, RunsOpeningBlock state after (capSubtreeCycles groups node height) ∧
      after.pc = 0x1a3c ∧
      CapPosition groups after node (dest+30*(Sampling.capFrontierNodes groups node height).length) ∧
      CapWrites state after dest (Sampling.capFrontierNodes groups node height) :=
  execute_cap_subtree emit_cap groups state node height dest span position pc separate aligned fits

end TwoPermutationPrototype.PackedOpening
