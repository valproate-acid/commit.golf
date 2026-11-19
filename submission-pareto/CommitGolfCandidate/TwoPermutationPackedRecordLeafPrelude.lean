import CommitGolfCandidate.TwoPermutationPackedDecode
import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.TwoPermutationPackedRecordGeometry
import CommitGolfCandidate.TwoPermutationCheckerRecordSetup
import CommitGolfCandidate.TwoPermutationPackedCheckerSteps

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (beginRecordCode beginRecord beginLowerCode beginLower
  record_setup_post record_setup_register record_setup_mem lower_setup_post lower_setup_register lower_setup_mem
  checkIndexWord checkSourceWord checker_positions_bound RecordInputFrame honestIndex record_input_index)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem setup_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

theorem execute_record_setup (state : MachineState) (pc : state.pc = 0x1058) (fuel : Nat)
    (index : accessValid (state.getReg .x8) 8 = true) :
    execute packedImage (6+fuel) state false =
      (do let result ← execute packedImage fuel (beginRecord state 6) false
          return result.charge 6 0) := by
  apply execute_unit_steps (states := beginRecord state)
  intro i bounded
  refine ⟨.base (beginRecordCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (22+i) _ (by omega)
    · interval_cases i <;> simp [beginRecord, beginRecordCode, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> simp [ordinaryStep, memoryArgumentsValid, memAccess, beginRecord,
      beginRecordCode, signExtend12, index] <;> assumption
  · interval_cases i <;> rfl


theorem execute_lower_setup (state : MachineState) (pc : state.pc = 0x10e8) (fuel : Nat) :
    execute packedImage (5+fuel) state false =
      (do let result ← execute packedImage fuel (beginLower state 5) false
          return result.charge 5 0) := by
  apply execute_unit_steps (states := beginLower state)
  intro i bounded
  refine ⟨.base (beginLowerCode[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetch_at _ (58+i) _ (by omega)
    · interval_cases i <;> simp [beginLower, beginLowerCode, execInstrBr, MachineState.setPC, pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl


def staged (state : MachineState) : MachineState := copyField (fieldCode .nonce) (beginRecord state 6)

theorem stage_ready (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (state : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal state) :
    CopyReady (fieldCode .nonce) (beginRecord state 6) (checkProofByte ordinal) 12272 0 := by
  obtain ⟨aligned,_,_,room,_⟩ := packed_record_geometry input ordinal h fits
  have pc : state.pc=0x1058 := cursor.pc.trans (ite_eq_right (by omega))
  have regs := record_setup_post state
  have keep (r : Reg) (a : r≠.x6) (b : r≠.x28) (c : r≠.x10) (d : r≠.x11) (e : r≠.x13) :=
    record_setup_register state r a b c d e
  refine ⟨?_,(keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans cursor.proof,
    ?_,?_,by decide,aligned,by decide⟩
  · change (beginRecord state 6).pc = 0x1070
    rw [regs.2.2.2.2.2,pc];rfl
  · change (beginRecord state 6).getReg .x4+0=_
    rw [keep .x4 (by decide) (by decide) (by decide) (by decide) (by decide),cursor.nonceScratch];rfl
  · change checkProofByte ordinal+16≤MEMORY_BYTES;omega

theorem staged_nonce_read (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (state : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal state) :
    readBuffer (staged state) 12272 16=readBuffer state (checkProofByte ordinal) 16 := by
  have room := (packed_record_geometry input ordinal h fits).2.2.1
  exact (field_read .nonce (beginRecord state 6) _ _ (stage_ready _ _ h _ fits cursor) (by omega)).trans
    (read_buffer_memory_congr _ _ (record_setup_mem state) _ _)

theorem staged_word_frame (input : CheckInput) (ordinal : Nat) (h : ordinal < input.positions.card)
    (state : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal state)
    (word : Nat) (bound : word < 2^33) (outside : word<1534 ∨ 1536≤word) :
    memoryView (staged state) word=memoryView state word := by
  have room := (packed_record_geometry input ordinal h fits).2.2.1
  have frame := (field_bytes .nonce (beginRecord state 6) _ _ (stage_ready _ _ h _ fits cursor) (by omega)).2
  apply Eq.trans (word_eq_of_byte_frame (beginRecord state 6) (staged state) word ?_)
  · exact congrFun (record_setup_mem state) _
  · intro i hi
    apply frame
    intro j hj eq
    have same := congrArg BitVec.toNat eq
    have one : 8*word+i<2^64 := by omega
    change j<16 at hj
    have two : 12272+j<2^64 := by omega
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt one,BitVec.toNat_ofNat,Nat.mod_eq_of_lt two] at same
    omega

end TwoPermutationPrototype.Packed.RecordLeaf
