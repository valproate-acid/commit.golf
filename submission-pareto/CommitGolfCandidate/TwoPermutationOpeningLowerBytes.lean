import CommitGolfCandidate.TwoPermutationOpeningLowerControl
import CommitGolfCandidate.TwoPermutationOpeningCopyBytes
import CommitGolfCandidate.TwoPermutationOpeningSibling

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

attribute [local irreducible] siblingPrefix

private theorem buffer_from_mem (before after : MachineState) (address bytes : Nat)
    (memory : before.mem = after.mem) :
    readBuffer before address bytes = readBuffer after address bytes := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, memory]

private theorem lower_step_memory (state : MachineState) (index : Index) (ordinal level : Nat)
    (ordinalBound : ordinal < LENGTH) (levelBound : level < 16)
    (control : LowerControl state index ordinal level) :
    let source := trapdoorBase + 32 * (lowerNode index level ^^^ 1)
    let dest := siblingDest ordinal level
    (siblingPrefix state 15).mem =
      (fourWordStore state (BitVec.ofNat 64 source) (BitVec.ofNat 64 dest)).mem := by
  dsimp only
  have source := sibling_address state (lowerNode index level) control.heap control.node
  have ⟨_, _, separate, fits⟩ := ordinal_sibling_geometry index ordinal level ordinalBound levelBound
  have disjoint (i j : Fin 4) :
      siblingSource state + BitVec.ofNat 64 (8 * i.val) ≠ state.getReg .x21 + BitVec.ofNat 64 (8 * j.val) := by
    rw [source, control.destination]
    exact separated_words _ _ 4 separate fits i j
  have output := sibling_memory state disjoint
  rw [source, control.destination] at output
  exact output

theorem lower_level_slot (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (index : Index) (ordinal level : Nat)
    (ordinalBound : ordinal < LENGTH) (levelBound : level < 16)
    (control : LowerControl state index ordinal level)
    (unchanged : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state) :
    readBuffer (siblingPrefix state 15) (siblingDest ordinal level) 32 =
      trapdoor.extractLsb' (256 * (lowerNode index level ^^^ 1)) 256 := by
  let source := trapdoorBase + 32 * (lowerNode index level ^^^ 1)
  let dest := siblingDest ordinal level
  have ⟨alignedSrc, alignedDst, _, fits⟩ :=
    ordinal_sibling_geometry index ordinal level ordinalBound levelBound
  change readBuffer (siblingPrefix state 15) dest 32 = _
  have stored := lower_step_memory state index ordinal level ordinalBound levelBound control
  rw [buffer_from_mem _ _ _ _ stored, four_word_store_bytes state source dest alignedSrc alignedDst fits]
  have heapStable : readBuffer state source 32 =
      readBuffer (s.initialState .opening (trapdoor, positions)) source 32 := by
    apply copied_buffer _ _ source source 4 alignedSrc alignedSrc (by decide)
    intro j inside
    apply unchanged
    · unfold source
      omega
    · unfold source
      have words := lower_swap_bound index level
      have first := heap_before_nonces
      have second := nonces_end_at_indices
      have third := indices_before_records
      omega
  rw [heapStable]
  exact input_digest s layout trapdoor positions _ (lower_swap_bound index level)

private theorem observed_copy_outside (before after : MachineState) (source dest address : Word)
    (memory : after.mem = (fourWordStore before source dest).mem)
    (outside : ∀ i : Fin 4, address ≠ dest + BitVec.ofNat 64 (8 * i.val)) :
    after.getMem address = before.getMem address := by
  have copied : after.getMem address = (fourWordStore before source dest).getMem address :=
    congrFun memory address
  exact copied.trans (four_word_store_outside before source dest address outside)

theorem lower_level_untouched (state : MachineState) (index : Index) (ordinal level address : Nat)
    (ordinalBound : ordinal < LENGTH) (levelBound : level < 16)
    (control : LowerControl state index ordinal level)
    (addressBound : address < 2 ^ 64)
    (outside : address < siblingDest ordinal level ∨ siblingDest ordinal level + 32 ≤ address) :
    (siblingPrefix state 15).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have store := lower_step_memory state index ordinal level ordinalBound levelBound control
  have untouched (i : Fin 4) : BitVec.ofNat 64 address ≠
      BitVec.ofNat 64 (siblingDest ordinal level) + BitVec.ofNat 64 (8 * i.val) := by
    rw [word_at]
    intro eq
    have inside := i.isLt
    have ⟨_, _, _, fits⟩ := ordinal_sibling_geometry index ordinal level ordinalBound levelBound
    unfold MEMORY_BYTES at fits
    have exactAddr := nat_address_injective addressBound (by omega) eq
    rcases outside with earlier | later <;> omega
  exact observed_copy_outside state (siblingPrefix state 15)
    (BitVec.ofNat 64 (trapdoorBase + 32 * (lowerNode index level ^^^ 1)))
    (BitVec.ofNat 64 (siblingDest ordinal level)) (BitVec.ofNat 64 address) store untouched

private theorem prior_slice_preserved (state : MachineState) (index : Index)
    (ordinal level address words : Nat) (ordinalBound : ordinal < LENGTH) (levelBound : level < 16)
    (control : LowerControl state index ordinal level)
    (aligned : address % 8 = 0) (short : words ≤ 8)
    (before : address + 8 * words ≤ siblingDest ordinal level) :
    readBuffer (siblingPrefix state 15) address (8 * words) =
      readBuffer state address (8 * words) := by
  apply copied_buffer _ _ address address words aligned aligned short
  intro j inside
  have ⟨_, _, _, fits⟩ := ordinal_sibling_geometry index ordinal level ordinalBound levelBound
  unfold MEMORY_BYTES at fits
  exact lower_level_untouched state index ordinal level (address + 8 * j)
    ordinalBound levelBound control (by omega) (Or.inl (by omega))

/-- The lower record's exact contents up through the siblings already visited. -/
structure LowerContents (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (index : Index) (ordinal level : Nat) : Prop where
  input : SameOpeningInput (s.initialState .opening (trapdoor, positions)) state
  nonce : readBuffer state (recordBase ordinal) 16 =
    trapdoor.extractLsb' (8 * (80 * LENGTH + 16 * index.val)) 128
  sibling : ∀ prior < level, readBuffer state (siblingDest ordinal prior) 32 =
    trapdoor.extractLsb' (256 * (lowerNode index prior ^^^ 1)) 256

theorem lower_contents_next (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (index : Index) (ordinal level : Nat)
    (ordinalBound : ordinal < LENGTH) (levelBound : level < 16)
    (control : LowerControl state index ordinal level)
    (contents : LowerContents s trapdoor positions state index ordinal level) :
    LowerContents s trapdoor positions (siblingPrefix state 15) index ordinal (level + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro address lo hi
    have low : address < siblingDest ordinal level := by
      unfold siblingDest recordBase
      omega
    have fits : address < 2 ^ 64 := by
      have := proof_fits_memory
      unfold MEMORY_BYTES at this
      omega
    exact (lower_level_untouched state index ordinal level address ordinalBound levelBound
      control fits (Or.inl low)).trans (contents.input address lo hi)
  · have ⟨_, aligned, _, _⟩ := ordinal_nonce_geometry index ordinal ordinalBound
    exact (prior_slice_preserved state index ordinal level (recordBase ordinal) 2 ordinalBound
      levelBound control aligned (by decide) (by unfold siblingDest; omega)).trans contents.nonce
  · intro prior recent
    by_cases last : prior = level
    · subst prior
      exact lower_level_slot s layout trapdoor positions state index ordinal level
        ordinalBound levelBound control contents.input
    · have earlier : prior < level := by omega
      have ⟨_, aligned, _, _⟩ := ordinal_sibling_geometry index ordinal prior ordinalBound (by omega)
      exact (prior_slice_preserved state index ordinal level (siblingDest ordinal prior) 4 ordinalBound
        levelBound control aligned (by decide) (by unfold siblingDest; omega)).trans
          (contents.sibling prior earlier)

/-- All 16 digest reads come from the original heap and leave the exact nonce and
earlier digest bytes untouched at the end of the actual lower loop. -/
theorem lower_path_contents (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (state : MachineState) (index : Index) (ordinal level remaining : Nat)
    (ordinalBound : ordinal < LENGTH) (final : level + remaining = 16)
    (control : LowerControl state index ordinal level)
    (contents : LowerContents s trapdoor positions state index ordinal level) :
    LowerContents s trapdoor positions (lowerPathMachine state remaining) index ordinal 16 := by
  induction remaining generalizing state level with
  | zero =>
    have done : level = 16 := by omega
    subst level
    exact contents
  | succ remaining ih =>
    apply ih _ (level + 1) (by omega)
    · exact lower_control_next state index ordinal level (by omega) control
    · exact lower_contents_next s layout trapdoor positions state index ordinal level ordinalBound
        (by omega) control contents

end TwoPermutationPrototype.Opening
