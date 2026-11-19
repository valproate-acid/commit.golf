import CommitGolfCandidate.TwoPermutationOpeningRecordMark
import CommitGolfCandidate.TwoPermutationOpeningSetup

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem record_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem record_tail_register (state : MachineState) (reg : Reg)
    (temporary : reg ≠ .x7) (ordinal : reg ≠ .x8) (remaining : reg ≠ .x18) :
    (recordTailPrefix state 6).getReg reg = state.getReg reg := by
  by_cases finished : state.getReg .x18 + 18446744073709551615#64 = 0#64 <;>
    simp [recordTailPrefix, recordTailInstructions, execInstrBr, signExtend12, finished,
      Ne.symm temporary, Ne.symm ordinal, Ne.symm remaining]

attribute [local irreducible] execute recordDataMachine recordTailPrefix

/-- Register and input ABI state at an ordinal boundary. The final boundary enters
the cap phase, all other boundaries enter the next nonce record. -/
structure RecordBoundary (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = if ordinal = positions.card then 0x10b0 else 0x1034
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase + 8 * ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  left : state.getReg .x18 = BitVec.ofNat 64 (positions.card - ordinal)
  marks : state.getReg .x26 = BitVec.ofNat 64 markBase
  one : state.getReg .x23 = 1#64
  capHeap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase
  capLeaves : state.getReg .x27 = 256#64
  proofBegin : state.getReg .x20 = BitVec.ofNat 64 proofBase

theorem RecordBoundary.start {s : Submission} {trapdoor : BitVec (8 * s.sizes.trapdoor)}
    {positions : Positions} {state : MachineState} {ordinal : Nat}
    (boundary : RecordBoundary s trapdoor positions state ordinal)
    (present : ordinal < positions.card) : RecordStart s trapdoor positions state ordinal :=
  ⟨by simpa only [ite_eq_right (show ordinal ≠ positions.card by omega)] using boundary.pc,
    boundary.heap, boundary.index, boundary.nonce, boundary.dest, boundary.leaves, boundary.input⟩

theorem record_boundary_next (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal) :
    RecordBoundary s trapdoor positions (recordMachine state) (ordinal + 1) := by
  let ready := boundary.start present
  have data := record_data_control s layout trapdoor positions state ordinal present ready
  have contents := record_final_contents s layout trapdoor positions state ordinal present ready
    boundary.marks boundary.one
  have tail := record_tail_post (recordDataMachine state) (by simpa using data.pc)
  have left := (record_data_register state .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    boundary.left
  have nextLeft : (recordDataMachine state).getReg .x18 - 1 =
      BitVec.ofNat 64 (positions.card - (ordinal + 1)) := by
    rw [left]
    change BitVec.ofNat 64 (positions.card - ordinal) - BitVec.ofNat 64 1 = _
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by decide) (by omega)]
    congr 1
  have empty : BitVec.ofNat 64 (positions.card - (ordinal + 1)) = 0#64 ↔ ordinal + 1 = positions.card := by
    have limit : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
    constructor
    · intro zero
      have eq := nat_address_injective (left := positions.card - (ordinal + 1)) (right := 0)
        (by norm_num [LENGTH, LOG_LENGTH] at limit; omega) (by decide) zero
      omega
    · intro finished
      rw [finished, Nat.sub_self]
  have stay (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x29)
      (e : reg ≠ .x31) (f : reg ≠ .x8) (g : reg ≠ .x18) :
      (recordMachine state).getReg reg = state.getReg reg :=
    (record_tail_register (recordDataMachine state) reg b f g).trans (record_data_register state reg a b c d e)
  refine ⟨?_, (stay .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    boundary.heap, ?_,
    (stay .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      boundary.nonce, ?_,
    (stay .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      boundary.leaves, contents.input, tail.2.2.1.trans nextLeft, ?_, ?_, ?_, ?_, ?_⟩
  · change (recordTailPrefix (recordDataMachine state) 6).pc = _
    rw [tail.2.2.2, nextLeft]
    simp only [empty]
  · change (recordTailPrefix (recordDataMachine state) 6).getReg .x8 = _
    rw [tail.2.1, record_data_register state .x8 (by decide) (by decide) (by decide) (by decide) (by decide),
      boundary.index]
    rw [← BitVec.ofNat_add]
    congr 1
  · change (recordTailPrefix (recordDataMachine state) 6).getReg .x21 = _
    rw [record_tail_register _ .x21 (by decide) (by decide) (by decide), data.destination,
      ordinal_sibling_end]
  · exact (stay .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans boundary.marks
  · exact (stay .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans boundary.one
  · exact (stay .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans boundary.capHeap
  · exact (stay .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans boundary.capLeaves
  · exact (stay .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans boundary.proofBegin

def recordsMachine (state : MachineState) : Nat → MachineState
  | 0 => state
  | remaining + 1 => recordsMachine (recordMachine state) remaining

/-- Execute every opening record up to the desired ordinal. This induction
covers every cardinality, with the record-tail branch sending the final one to the cap. -/
theorem execute_records (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal remaining fuel : Nat) (allowCoins : Bool)
    (limit : ordinal + remaining ≤ positions.card)
    (boundary : RecordBoundary s trapdoor positions state ordinal) :
    execute openingImage (256 * remaining + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (recordsMachine state remaining) allowCoins
          return result.charge (256 * remaining) 0) ∧
      RecordBoundary s trapdoor positions (recordsMachine state remaining) (ordinal + remaining) := by
  induction remaining generalizing state ordinal with
  | zero => simpa [recordsMachine, Execution.charge] using boundary
  | succ remaining ih =>
    have present : ordinal < positions.card := by omega
    have one := execute_record s layout trapdoor positions state ordinal (256 * remaining + fuel)
      allowCoins present (boundary.start present) boundary.marks
    have next := record_boundary_next s layout trapdoor positions state ordinal present boundary
    have ⟨tail, finish⟩ := ih (recordMachine state) (ordinal + 1) (by omega) next
    constructor
    · rw [show 256 * (remaining + 1) + fuel = 256 + (256 * remaining + fuel) by omega, one, tail]
      simp [recordsMachine, Execution.charge, Nat.add_assoc, Nat.mul_succ, Nat.add_comm 256]
    · simpa only [recordsMachine, show ordinal + (remaining + 1) = ordinal + 1 + remaining by omega] using finish

private theorem nonempty_count (positions : Positions) (nonempty : 0 < positions.card) :
    BitVec.ofNat 64 positions.card ≠ 0#64 := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  intro empty
  have zero := nat_address_injective (left := positions.card) (right := 0)
    (by norm_num [LENGTH, LOG_LENGTH] at cardinal; omega) (by decide) empty
  omega

theorem opening_first_boundary (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (nonempty : 0 < positions.card) :
    let initial := s.initialState .opening (trapdoor, positions)
    RecordBoundary s trapdoor positions (setupPrefix initial 13) 0 := by
  let initial := s.initialState .opening (trapdoor, positions)
  have start : initial.pc = 0x1000 := rfl
  have trapPointer : initial.getReg .x12 = BitVec.ofNat 64 trapdoorBase :=
    congrArg (BitVec.ofNat 64) layout.trapdoor
  have indexPointer : initial.getReg .x13 = BitVec.ofNat 64 indicesBase :=
    congrArg (BitVec.ofNat 64) layout.indices
  have proofPointer : initial.getReg .x15 = BitVec.ofNat 64 proofBase :=
    congrArg (BitVec.ofNat 64) layout.proof
  have countValue : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have ⟨proofStart, dest, ordinal, heap, count, size, nonce, one, capHeap, marks, capLeaves, memory⟩ :=
    setup_registers initial
  refine ⟨?_, heap.trans trapPointer, ?_, ?_, ?_, size, ?_, ?_, marks, one,
    capHeap.trans trapPointer, capLeaves, proofStart.trans proofPointer⟩
  · rw [ite_eq_right (show (0 : Nat) ≠ positions.card by omega)]
    exact setup_pc initial start (countValue ▸ nonempty_count positions nonempty)
  · simpa using ordinal.trans indexPointer
  · rw [nonce, trapPointer, ← BitVec.ofNat_add]
    rfl
  · simpa [recordBase] using dest.trans proofPointer
  · intro address _ _
    exact congrFun memory (BitVec.ofNat 64 address)
  · simpa using count.trans countValue

/-- The entire nonempty opening prefix reaches the cap with a known pointer and
without randomness or oracle calls, independently of the private-state bytes. -/
theorem execute_opening_records (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (nonempty : 0 < positions.card) (fuel : Nat) (allowCoins : Bool) :
    let initial := s.initialState .opening (trapdoor, positions)
    let final := recordsMachine (setupPrefix initial 13) positions.card
    execute openingImage (13 + 256 * positions.card + fuel) initial allowCoins =
      (do let result ← execute openingImage fuel final allowCoins
          return result.charge (13 + 256 * positions.card) 0) ∧
      RecordBoundary s trapdoor positions final positions.card := by
  let initial := s.initialState .opening (trapdoor, positions)
  have count : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have active : initial.getReg .x16 ≠ 0#64 := by
    rw [count]
    exact nonempty_count positions nonempty
  have setup := execute_setup initial rfl (256 * positions.card + fuel) allowCoins active
  have ⟨run, boundary⟩ := execute_records s layout trapdoor positions (setupPrefix initial 13) 0
    positions.card fuel allowCoins (by omega) (opening_first_boundary s layout trapdoor positions nonempty)
  dsimp only
  constructor
  · rw [show 13 + 256 * positions.card + fuel = 13 + (256 * positions.card + fuel) by omega,
      setup, run]
    simp [Execution.charge, ← Nat.add_assoc, initial]
  · simpa only [Nat.zero_add] using boundary

end TwoPermutationPrototype.Opening
