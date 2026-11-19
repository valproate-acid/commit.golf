import CommitGolfCandidate.TwoPermutationPackedOpeningLowerRun

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (OpeningLayout proofBase sortedIndex SameOpeningInput trapdoorBase)

def recordData (state : MachineState) := lowerRun 0 16 (nonceBlock state)

structure RecordData (state after : MachineState) (index : Index) (ordinal : Nat) : Prop where
  run : RunsOpeningBlock state after 583
  cursor : LowerCursor after index ordinal 16
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 →
    after.getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    after.getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)
  frame : ∀ address < 2^64, address < recordBase ordinal ∨ recordBase (ordinal+1) ≤ address →
    after.getByte (BitVec.ofNat 64 address) = state.getByte (BitVec.ofNat 64 address)
  nonce : ∀ byte < 16, after.getByte (BitVec.ofNat 64 (recordBase ordinal+byte)) =
    state.getByte (BitVec.ofNat 64 (nonceAddress index+byte))
  sibling : ∀ level < 16, ∀ byte < siblingWidth level,
    after.getByte (BitVec.ofNat 64 (siblingDestination ordinal level+byte)) =
      state.getByte (BitVec.ofNat 64 (siblingAddress index level+byte))

theorem execute_record_data (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    RecordData state (recordData state) (sortedIndex positions ordinal present) ordinal := by
  let index := sortedIndex positions ordinal present
  let middle := nonceBlock state
  let final := recordData state
  have card : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have n := execute_ordinal_nonce s layout trapdoor positions state ordinal present ready
  have low := execute_lower middle index ordinal 0 16 (by omega) (by decide) n.next
  have ⟨_, _, _, nonceFit⟩ := all_nonce_copies_fit index ordinal (by omega)
  have ram : MEMORY_BYTES < 2^64 := by decide
  have start : siblingDestination ordinal 0 = recordBase ordinal+16 := rfl
  refine ⟨n.run.next low.run, low.next,
    fun r a b c d => (low.register r a b c d).trans (n.register r a b c d),
    fun address valid => (low.input address valid).trans (n.input address valid), ?_, ?_, ?_⟩
  · intro address fit outside
    have tail := low.frame address fit
    rw [start, show (0:Nat)+16=16 by decide, record_end] at tail
    have later : recordBase ordinal+16 ≤ recordBase (ordinal+1) := by
      unfold recordBase recordBytes
      omega
    exact (tail (outside.imp (by omega) id)).trans
      (field_outside n.bytes address fit (by omega) (outside.imp id (by omega)))
  · intro byte inside
    have stable := low.frame (recordBase ordinal+byte) (by omega) (Or.inl (by rw [start]; omega))
    exact stable.trans (n.bytes.copied byte inside)
  · intro level levelBound byte inside
    have sibling := low.fields level (Nat.zero_le _) levelBound byte inside
    have before : siblingAddress index level+byte < recordBase ordinal := by
      have nodeBound := Opening.lower_swap_bound index level
      have heapEnd := Opening.heap_before_nonces
      have nonceEnd := Opening.nonces_end_at_indices
      have indicesEnd := Opening.indices_before_records
      have roomy : siblingWidth level ≤ 32 := by unfold siblingWidth; split <;> decide
      unfold siblingAddress recordBase
      omega
    exact sibling.trans (field_outside n.bytes _ (by omega) (by omega) (Or.inl before))

end TwoPermutationPrototype.PackedOpening
