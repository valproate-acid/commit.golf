import CommitGolfCandidate.TwoPermutationPackedOpeningSiblingRun
import CommitGolfCandidate.TwoPermutationOpeningRecordStart

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (OpeningLayout SameOpeningInput sortedIndex trapdoorBase indicesBase nonceBase proofBase lowerNode)

structure RecordStart (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = 0x1034
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state

def nonceBlock (state : MachineState) : MachineState :=
  nonceAdvance (copyState .nonce (nonceSetup state))

structure NonceTrace (state : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state (nonceBlock state) 21
  next : LowerCursor (nonceBlock state) index ordinal 0
  bytes : ByteCopy state (nonceBlock state) (nonceAddress index) (recordBase ordinal) 16
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 →
    (nonceBlock state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (nonceBlock state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

theorem execute_ordinal_nonce (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    NonceTrace state (sortedIndex positions ordinal present) ordinal := by
  let index := sortedIndex positions ordinal present
  let prepared := nonceSetup state
  let copied := copyState .nonce prepared
  let done := nonceBlock state
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have below : indicesBase+8*ordinal < proofBase := by
    have geometry := Opening.indices_before_records
    omega
  have above : trapdoorBase ≤ indicesBase+8*ordinal := by unfold indicesBase; omega
  have readIndex : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val := by
    rw [ready.index, ready.input _ above below]
    exact Opening.input_index s layout trapdoor positions ordinal present
  have inputSafe : accessValid (state.getReg .x8) 8 = true := by
    rw [ready.index]
    apply Opening.aligned_access
    · have aligned : indicesBase % 8 = 0 := by decide
      omega
    · have ram := packed_proof_memory
      have slots := Opening.indices_before_records
      omega
  have setup := nonce_setup_post state
  have advance := nonce_advance_post copied
  have landscape := all_nonce_copies_fit index ordinal (by omega)
  have field : FieldInputs .nonce prepared (nonceAddress index) (recordBase ordinal) :=
    ⟨by rw [setup.1, ready.pc]; rfl, physical_nonce_source state index ready.nonce readIndex,
      (setup.2.2.2.2 .x21 (by decide) (by decide)).trans ready.dest,
      landscape.2.2.1, landscape.2.2.2, landscape.1, landscape.2.1⟩
  have advancePC : copied.pc = 0x1080 := field.final_pc
  have kept (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x31) :
      done.getReg reg = state.getReg reg :=
    (advance.2.2.2.2 reg c a).trans
      ((copy_register .nonce prepared reg d).trans (setup.2.2.2.2 reg a b))
  have startRun : RunsOpeningBlock state prepared 3 :=
    fun fuel coins => execute_nonce_setup state ready.pc inputSafe fuel coins
  have endRun : RunsOpeningBlock copied done 2 :=
    fun fuel coins => execute_nonce_advance copied advancePC fuel coins
  refine ⟨(startRun.next field.run).next endRun,
    ⟨?_, (kept .x9 (by decide) (by decide) (by decide) (by decide)).trans ready.heap, ?_, ?_⟩,
    field.bytes.move setup.2.1.symm advance.2.1, kept, ?_⟩
  · change (nonceAdvance copied).pc = lowerPC 0
    rw [advance.1, advancePC]
    rfl
  · change (nonceAdvance copied).getReg .x6 = BitVec.ofNat 64 (lowerNode index 0)
    rw [advance.2.2.2.1, copy_register .nonce prepared .x6 (by decide),
      setup.2.2.2.1, readIndex, copy_register .nonce prepared .x19 (by decide),
      setup.2.2.2.2 .x19 (by decide) (by decide), ready.leaves, ← BitVec.ofNat_add]
    simp [lowerNode, Nat.add_comm]
  · change (nonceAdvance copied).getReg .x21 = _
    rw [advance.2.2.1, copy_register .nonce prepared .x21 (by decide),
      setup.2.2.2.2 .x21 (by decide) (by decide), ready.dest]
    exact (BitVec.ofNat_add (n := 64) (recordBase ordinal) 16).symm
  · intro address below
    have separate : proofBase ≤ recordBase ordinal := by unfold recordBase; omega
    have stable := field.words_before proofBase address below separate (by decide)
    have saved : done.mem = copied.mem := advance.2.1
    have reads : prepared.mem = state.mem := setup.2.1
    change done.getMem _ = _
    simpa only [MachineState.getMem, saved, reads] using stable

end TwoPermutationPrototype.PackedOpening
