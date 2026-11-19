import CommitGolfCandidate.TwoPermutationOpeningRecordStart
import CommitGolfCandidate.TwoPermutationOpeningRecordTail
import CommitGolfCandidate.TwoPermutationOpeningMarkContents

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096

attribute [local irreducible] siblingPrefix noncePrefix

private theorem lower_path_register (state : MachineState) (remaining : Nat) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x29) (e : reg ≠ .x31) :
    (lowerPathMachine state remaining).getReg reg = state.getReg reg := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    change (lowerPathMachine (siblingPrefix state 15) remaining).getReg reg = state.getReg reg
    exact (ih _).trans (sibling_register state reg a b c d e)

theorem record_data_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x29) (e : reg ≠ .x31) :
    (recordDataMachine state).getReg reg = state.getReg reg :=
  (lower_path_register (noncePrefix state 10) 16 reg a b c d e).trans (nonce_register state reg a b c d e)

def recordMachine (state : MachineState) : MachineState :=
  recordTailPrefix (recordDataMachine state) 6

private theorem record_group_address (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal)
    (marks : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    recordMarkAddress (recordDataMachine state) =
      BitVec.ofNat 64 (markBase + 8 * lowerNode (sortedIndex positions ordinal present) 16) := by
  have base := (record_data_register state .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans marks
  have control := record_data_control s layout trapdoor positions state ordinal present ready
  exact record_mark_address _ _ base control.node

attribute [local irreducible] execute recordDataMachine

/-- One full physical lower record consists of the nonce, 16 siblings, and the
cap-group mark. The mark is outside the returned proof. -/
theorem execute_record (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal fuel : Nat) (allowCoins : Bool)
    (present : ordinal < positions.card) (ready : RecordStart s trapdoor positions state ordinal)
    (marks : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    execute openingImage (256 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (recordMachine state) allowCoins
          return result.charge 256 0) := by
  have dataStep := execute_record_data s layout trapdoor positions state ordinal (6 + fuel)
    allowCoins present ready
  have control := record_data_control s layout trapdoor positions state ordinal present ready
  have capBound := lower_cap_range (sortedIndex positions ordinal present)
  have guard : accessValid (recordMarkAddress (recordDataMachine state)) 8 = true := by
    rw [record_group_address s layout trapdoor positions state ordinal present ready marks]
    apply aligned_access
    · unfold markBase
      omega
    · unfold markBase MEMORY_BYTES
      omega
  have tail := execute_record_tail (recordDataMachine state) (by simpa using control.pc)
    fuel allowCoins guard
  rw [show 256 + fuel = 250 + (6 + fuel) by omega, dataStep, tail]
  simp [recordMachine, Execution.charge, ← Nat.add_assoc]

theorem record_mark_memory (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal)
    (marks : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (one : state.getReg .x23 = 1#64) :
    (recordMachine state).mem =
      ((recordDataMachine state).setMem
        (BitVec.ofNat 64 (markBase + 8 * lowerNode (sortedIndex positions ordinal present) 16)) 1#64).mem := by
  have control := record_data_control s layout trapdoor positions state ordinal present ready
  have effect := (record_tail_post (recordDataMachine state) (by simpa using control.pc)).1
  have bit := (record_data_register state .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans one
  rw [record_group_address s layout trapdoor positions state ordinal present ready marks, bit] at effect
  exact effect

private theorem observed_mark_outside (before after : MachineState) (mark address : Word)
    (memory : after.mem = (before.setMem mark 1#64).mem)
    (different : address ≠ mark) : after.getMem address = before.getMem address := by
  have observed : after.getMem address = (before.setMem mark 1#64).getMem address :=
    congrFun memory address
  exact observed.trans (MachineState.getMem_setMem_ne different)

theorem record_mark_outside (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal address : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal)
    (marks : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (one : state.getReg .x23 = 1#64) (outside : trapdoorBase ≤ address)
    (bounded : address < 2 ^ 64) :
    (recordMachine state).getMem (BitVec.ofNat 64 address) =
      (recordDataMachine state).getMem (BitVec.ofNat 64 address) := by
  have slot := lower_cap_range (sortedIndex positions ordinal present)
  have first := marks_before_trapdoor
  have different : BitVec.ofNat 64 address ≠
      BitVec.ofNat 64 (markBase + 8 * lowerNode (sortedIndex positions ordinal present) 16) := by
    intro same
    unfold markBase at first same
    have equal := nat_address_injective bounded (by omega) same
    omega
  exact observed_mark_outside _ _ _ _ (record_mark_memory s layout trapdoor positions state ordinal
    present ready marks one) different

private theorem record_slot_above_trapdoor (ordinal offset : Nat) :
    trapdoorBase ≤ recordBase ordinal + offset := by
  have proofAbove : trapdoorBase ≤ proofBase := by decide
  unfold recordBase
  omega

attribute [local irreducible] readBuffer recordMachine

/-- The mark store preserves the exact nonce, sibling bytes and original input. -/
theorem record_final_contents (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal)
    (marks : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (one : state.getReg .x23 = 1#64) :
    LowerContents s trapdoor positions (recordMachine state)
      (sortedIndex positions ordinal present) ordinal 16 := by
  let index := sortedIndex positions ordinal present
  have length : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have dataBytes := record_data_contents s layout trapdoor positions state ordinal present ready
  have stable (address : Nat) (low : trapdoorBase ≤ address) (high : address < 2 ^ 64) :=
    record_mark_outside s layout trapdoor positions state ordinal address present ready marks one low high
  refine ⟨?_, ?_, ?_⟩
  · intro address low high
    have fit := proof_fits_memory
    unfold MEMORY_BYTES at fit
    exact (stable address low (by omega)).trans (dataBytes.input address low high)
  · have ⟨_, aligned, _, finish⟩ := ordinal_nonce_geometry index ordinal (by omega)
    have eq : readBuffer (recordMachine state) (recordBase ordinal) 16 =
        readBuffer (recordDataMachine state) (recordBase ordinal) 16 := by
      apply copied_buffer _ _ _ _ 2 aligned aligned (by decide)
      intro j jBound
      unfold MEMORY_BYTES at finish
      exact stable _ (record_slot_above_trapdoor ordinal (8*j)) (by omega)
    exact eq.trans dataBytes.nonce
  · intro level inside
    have ⟨_, aligned, _, fits⟩ := ordinal_sibling_geometry index ordinal level (by omega) inside
    have eq : readBuffer (recordMachine state) (siblingDest ordinal level) 32 =
        readBuffer (recordDataMachine state) (siblingDest ordinal level) 32 := by
      apply copied_buffer _ _ _ _ 4 aligned aligned (by decide)
      intro j jBound
      have low : trapdoorBase ≤ recordBase ordinal + 0 := record_slot_above_trapdoor ordinal 0
      unfold MEMORY_BYTES at fits
      exact stable _ (by unfold siblingDest; omega) (by omega)
    exact eq.trans (dataBytes.sibling level inside)

end TwoPermutationPrototype.Opening
