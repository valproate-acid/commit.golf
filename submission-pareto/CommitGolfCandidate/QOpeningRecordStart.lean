import CommitGolfCandidate.QOpeningLowerBytes

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

theorem nonce_register (state : MachineState) (reg : Reg)
    (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21)
    (d : reg ≠ .x29) (e : reg ≠ .x31) :
    (noncePrefix state 10).getReg reg = state.getReg reg := by
  simp [noncePrefix, nonceInstructions, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c,
    Ne.symm d, Ne.symm e]

/-- The stable per-record pointers and immutable input view at the first LD. -/
structure RecordStart (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (ordinal : Nat) : Prop where
  pc : state.pc = 0x1034
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase + 8 * ordinal)
  nonce : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (recordBase ordinal)
  leaves : state.getReg .x19 = BitVec.ofNat 64 LENGTH
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state

def sortedIndex (positions : Positions) (ordinal : Nat) (present : ordinal < positions.card) : Index :=
  (positions.sort (· ≤ ·))[ordinal]'(by simpa using present)

private theorem ordinal_count (positions : Positions) : positions.card ≤ LENGTH := by
  simpa [Index] using Finset.card_le_univ positions

private theorem record_index (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    state.getMem (state.getReg .x8) = BitVec.ofNat 64 (sortedIndex positions ordinal present).val := by
  have length := ordinal_count positions
  have lower : trapdoorBase ≤ indicesBase + 8 * ordinal := by unfold indicesBase; omega
  have upper : indicesBase + 8 * ordinal < proofBase := by unfold proofBase; omega
  rw [ready.index, ready.input _ lower upper]
  exact input_index s layout trapdoor positions ordinal present

private theorem record_nonce_disjoint (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    nonceSource state + 8 ≠ state.getReg .x21 := by
  let index := sortedIndex positions ordinal present
  have length := ordinal_count positions
  have ⟨_, _, separate, inside⟩ := ordinal_nonce_geometry index ordinal (by omega)
  rw [nonce_address state _ ready.nonce (record_index s layout trapdoor positions state ordinal present ready),
    ready.dest]
  simpa using separated_words _ _ 2 separate inside 1 0

attribute [local irreducible] noncePrefix

theorem record_start_control (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    LowerControl (noncePrefix state 10) (sortedIndex positions ordinal present) ordinal 0 := by
  have post := nonce_post state (record_nonce_disjoint s layout trapdoor positions state ordinal present ready)
  refine ⟨?_, (nonce_register state .x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
    ready.heap, ?_, ?_, post.2.2.2.1⟩
  · rw [post.2.2.2.2, ready.pc]
    rfl
  · rw [post.2.1, ready.dest, siblingDest]
    change BitVec.ofNat 64 (recordBase ordinal) + BitVec.ofNat 64 16 = _
    rw [← BitVec.ofNat_add]
  · rw [post.2.2.1, record_index s layout trapdoor positions state ordinal present ready, ready.leaves,
      ← BitVec.ofNat_add]
    simp [lowerNode, Nat.add_comm]

theorem record_start_contents (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    LowerContents s trapdoor positions (noncePrefix state 10) (sortedIndex positions ordinal present) ordinal 0 := by
  have length := ordinal_count positions
  have ⟨_, _, _, fits⟩ := ordinal_nonce_geometry (sortedIndex positions ordinal present) ordinal (by omega)
  unfold MEMORY_BYTES at fits
  have different (address : Nat) (upper : address < proofBase) (offset : Nat) (small : offset ≤ 8) :
      BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (recordBase ordinal + offset) := by
    intro overlap
    have low : proofBase ≤ recordBase ordinal := by unfold recordBase; omega
    have equality := nat_address_injective (by omega) (by omega) overlap
    omega
  refine ⟨?_, ordinal_nonce_bytes s layout trapdoor positions ordinal present state ready.index ready.nonce
    ready.dest ready.input, fun prior h => by omega⟩
  intro address low high
  have first : BitVec.ofNat 64 address ≠ state.getReg .x21 := by
    rw [ready.dest]
    simpa using different address high 0 (by decide)
  have second : BitVec.ofNat 64 address ≠ state.getReg .x21 + 8 := by
    rw [ready.dest]
    exact (fun overlap => different address high 8 (by decide) (overlap.trans (word_at _ 1)))
  exact (nonce_frame state _ (record_nonce_disjoint s layout trapdoor positions state ordinal present ready)
    first second).trans (ready.input address low high)

private theorem execute_record_nonce (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal fuel : Nat) (allowCoins : Bool)
    (present : ordinal < positions.card) (ready : RecordStart s trapdoor positions state ordinal) :
    execute openingImage (10 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (noncePrefix state 10) allowCoins
          return result.charge 10 0) := by
  let index := sortedIndex positions ordinal present
  have length := ordinal_count positions
  have ⟨srcAlign, dstAlign, ordered, finish⟩ := ordinal_nonce_geometry index ordinal (by omega)
  have indexFits : accessValid (state.getReg .x8) 8 = true := by
    rw [ready.index]
    apply aligned_access
    · norm_num [indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH]
    · have before := indices_before_records
      have fits := proof_fits_memory
      omega
  have src := nonce_address state index.val ready.nonce
    (record_index s layout trapdoor positions state ordinal present ready)
  apply execute_nonce state ready.pc fuel allowCoins indexFits
  · rw [src]
    exact aligned_access _ srcAlign (by omega)
  · rw [src]
    change accessValid (BitVec.ofNat 64 (nonceBase + 16 * index.val) + BitVec.ofNat 64 (8 * 1)) 8 = true
    rw [word_at]
    exact aligned_access _ (by omega) (by omega)
  · rw [ready.dest]
    exact aligned_access _ dstAlign (by omega)
  · rw [ready.dest]
    change accessValid (BitVec.ofNat 64 (recordBase ordinal) + BitVec.ofNat 64 (8 * 1)) 8 = true
    rw [word_at]
    exact aligned_access _ (by omega) (by omega)

def recordDataMachine (state : MachineState) : MachineState :=
  lowerPathMachine (noncePrefix state 10) 16

attribute [local irreducible] execute

/-- All bytes of one lower record are written after 250 instructions. This
includes the exact ordinal nonce load and all 16 sibling copies. -/
theorem execute_record_data (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal fuel : Nat) (allowCoins : Bool)
    (present : ordinal < positions.card) (ready : RecordStart s trapdoor positions state ordinal) :
    execute openingImage (250 + fuel) state allowCoins =
      (do let result ← execute openingImage fuel (recordDataMachine state) allowCoins
          return result.charge 250 0) := by
  have length := ordinal_count positions
  have nonce := execute_record_nonce s layout trapdoor positions state ordinal (240 + fuel) allowCoins
    present ready
  have lower := execute_lower_path (noncePrefix state 10) (sortedIndex positions ordinal present)
      ordinal 0 16 fuel allowCoins (by omega) (by decide)
      (record_start_control s layout trapdoor positions state ordinal present ready)
  rw [show 250 + fuel = 10 + (240 + fuel) by omega, nonce, lower]
  simp [recordDataMachine, Execution.charge, ← Nat.add_assoc]

theorem record_data_contents (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    LowerContents s trapdoor positions (recordDataMachine state)
      (sortedIndex positions ordinal present) ordinal 16 := by
  have length := ordinal_count positions
  exact lower_path_contents s layout trapdoor positions (noncePrefix state 10)
    (sortedIndex positions ordinal present) ordinal 0 16 (by omega) (by decide)
    (record_start_control s layout trapdoor positions state ordinal present ready)
    (record_start_contents s layout trapdoor positions state ordinal present ready)

theorem record_data_control (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal) :
    LowerControl (recordDataMachine state) (sortedIndex positions ordinal present) ordinal 16 :=
  lower_path_control _ _ _ 0 16 (by decide)
    (record_start_control s layout trapdoor positions state ordinal present ready)

attribute [local irreducible] siblingPrefix

private theorem lower_words_before (state : MachineState) (index : Index)
    (ordinal level remaining address : Nat) (ordinalBound : ordinal < LENGTH)
    (ends : level + remaining = 16) (control : LowerControl state index ordinal level)
    (before : address < recordBase ordinal) (fit : address < 2 ^ 64) :
    (lowerPathMachine state remaining).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction remaining generalizing state level with
  | zero => rfl
  | succ remaining ih =>
    change (lowerPathMachine (siblingPrefix state 15) remaining).getMem (BitVec.ofNat 64 address) = _
    have inside : level < 16 := by omega
    have next := lower_control_next state index ordinal level inside control
    have below : address < siblingDest ordinal level := by unfold siblingDest; omega
    exact (ih _ (level + 1) (by omega) next).trans (lower_level_untouched state index ordinal
      level address ordinalBound inside control fit (Or.inl below))

/-- The 250-cycle record-data phase preserves every word before its output slot. -/
theorem record_data_before (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (ordinal address : Nat) (present : ordinal < positions.card)
    (ready : RecordStart s trapdoor positions state ordinal)
    (before : address < recordBase ordinal) (fit : address < 2 ^ 64) :
    (recordDataMachine state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have length := ordinal_count positions
  let index := sortedIndex positions ordinal present
  have ⟨_, _, _, endWrite⟩ := ordinal_nonce_geometry index ordinal (by omega)
  unfold MEMORY_BYTES at endWrite
  have different (offset : Nat) (within : offset ≤ 8) :
      BitVec.ofNat 64 address ≠ BitVec.ofNat 64 (recordBase ordinal + offset) := by
    intro equal
    have same := nat_address_injective fit (by omega) equal
    omega
  have first : BitVec.ofNat 64 address ≠ state.getReg .x21 := by
    rw [ready.dest]
    simpa using different 0 (by decide)
  have second : BitVec.ofNat 64 address ≠ state.getReg .x21 + 8 := by
    rw [ready.dest]
    exact fun equal => different 8 (by decide) (equal.trans (word_at _ 1))
  have tail := lower_words_before (noncePrefix state 10) index ordinal 0 16 address
    (by omega) (by decide) (record_start_control s layout trapdoor positions state ordinal present ready) before fit
  exact tail.trans (nonce_frame state _
    (record_nonce_disjoint s layout trapdoor positions state ordinal present ready) first second)

end TwoPermutationPrototype.QOpening
