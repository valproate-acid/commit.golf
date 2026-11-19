import CommitGolfCandidate.TwoPermutationPackedOpeningRecordData
import CommitGolfCandidate.TwoPermutationPackedOpeningRecordTail
import CommitGolfCandidate.TwoPermutationPackedOpeningSetup
import CommitGolfCandidate.TwoPermutationOpeningRecordGroups

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (OpeningLayout sortedIndex SameOpeningInput trapdoorBase indicesBase nonceBase proofBase markBase
  RecordMarks groupsBefore machineMarks nat_address_injective)

structure RecordBoundary (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = if ordinal = positions.card then 0x196c else 0x1034
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  left : state.getReg .x18 = BitVec.ofNat 64 (positions.card-ordinal)
  marks : state.getReg .x26 = BitVec.ofNat 64 markBase
  one : state.getReg .x23 = 1#64
  capHeap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27 = 256#64
  proofBegin : state.getReg .x20 = BitVec.ofNat 64 proofBase

theorem RecordBoundary.start {s : Submission} {trapdoor : BitVec (8*s.sizes.trapdoor)}
    {positions : Positions} {state : MachineState} {ordinal : Nat}
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (present : ordinal < positions.card) : RecordStart s trapdoor positions state ordinal :=
  ⟨by simpa only [ite_eq_right (show ordinal ≠ positions.card by omega)] using boundary.pc,
    boundary.heap, boundary.index, boundary.nonce, boundary.dest, boundary.leaves, boundary.input⟩

def recordCost (final : Bool) : Nat := if final then 589 else 590

def afterLatch (marked : MachineState) (final : Bool) : MachineState :=
  if final then marked else marked.setPC 0x1034

def runRecord (state : MachineState) (final : Bool) : MachineState :=
  afterLatch (recordTailPrefix (recordData state) 6) final

structure OneRecord (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before after : MachineState) (ordinal : Nat)
    (present : ordinal < positions.card) : Prop where
  run : RunsOpeningBlock before after (recordCost (decide (ordinal+1=positions.card)))
  next : RecordBoundary s trapdoor positions after (ordinal+1)
  marks : ∀ node < 512, machineMarks after node =
    if node = Sampling.capGroup (sortedIndex positions ordinal present) then 1 else machineMarks before node
  frame : ∀ address < MEMORY_BYTES, trapdoorBase ≤ address →
    address < recordBase ordinal ∨ recordBase (ordinal+1) ≤ address →
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address)
  nonce : ∀ byte < 16, after.getByte (BitVec.ofNat 64 (recordBase ordinal+byte)) =
    before.getByte (BitVec.ofNat 64 (nonceAddress (sortedIndex positions ordinal present)+byte))
  sibling : ∀ level < 16, ∀ byte < siblingWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      before.getByte (BitVec.ofNat 64 (siblingAddress (sortedIndex positions ordinal present) level+byte))

def recordsCost (size ordinal count : Nat) : Nat :=
  if 0<count ∧ ordinal+count=size then 590*count-1 else 590*count

def runRecords (size ordinal : Nat) : Nat → MachineState → MachineState
  | 0, state => state
  | remaining+1, state =>
    runRecords size (ordinal+1) remaining (runRecord state (decide (ordinal+1=size)))

def CompletedRecords (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) : Prop :=
  ∀ prior (present : prior < positions.card), prior < ordinal →
    let index := sortedIndex positions prior present
    let loaded := s.initialState .opening (trapdoor, positions)
    (∀ byte < 16, state.getByte (BitVec.ofNat 64 (recordBase prior+byte)) =
      loaded.getByte (BitVec.ofNat 64 (nonceAddress index+byte))) ∧
    ∀ level < 16, ∀ byte < siblingWidth level,
      state.getByte (BitVec.ofNat 64 (siblingDestination prior level+byte)) =
        loaded.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))

structure RecordsFinished (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (before after : MachineState) (ordinal count : Nat) : Prop where
  run : RunsOpeningBlock before after (recordsCost positions.card ordinal count)
  boundary : RecordBoundary s trapdoor positions after (ordinal+count)
  marks : RecordMarks positions after (ordinal+count)
  bytes : CompletedRecords s trapdoor positions after (ordinal+count)

def RecordExecute : Prop :=
  ∀ (s : Submission) (_layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card),
    RecordBoundary s trapdoor positions state ordinal →
    OneRecord s trapdoor positions state (runRecord state (decide (ordinal+1=positions.card))) ordinal present

def RecordsExecute : Prop :=
  ∀ (s : Submission) (_layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal count : Nat), ordinal+count ≤ positions.card →
    RecordBoundary s trapdoor positions state ordinal →
    RecordMarks positions state ordinal →
    CompletedRecords s trapdoor positions state ordinal →
    RecordsFinished s trapdoor positions state (runRecords positions.card ordinal count state) ordinal count

end TwoPermutationPrototype.PackedOpening
