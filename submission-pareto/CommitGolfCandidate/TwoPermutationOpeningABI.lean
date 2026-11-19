import CommitGolfCandidate.TwoPermutationOpeningCapSubtree
import CommitGolfCandidate.TwoPermutationOpeningRecordPrefix

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : proofCapacity ≤ s.sizes.proof
  fuel : 512 * LENGTH + 65536 ≤ s.steps .opening

def openingNodes (positions : Positions) : List Nat :=
  if positions.card = 0 then [] else capFrontierNodes (groupsBefore positions positions.card) 1 8

def openingLength (positions : Positions) : Nat :=
  528 * positions.card + 32 * (openingNodes positions).length

def openingMachineCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7
  else 13 + 256 * positions.card + 2552 +
    capSubtreeCycles (groupsBefore positions positions.card) 1 8 + 6

theorem opening_nodes_bound (positions : Positions) : (openingNodes positions).length ≤ 128 := by
  unfold openingNodes
  split
  · simp
  · rw [cap_frontier_length]
    exact production_boundary_bound _

theorem opening_length_bound (positions : Positions) : openingLength positions ≤ proofCapacity := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have small := opening_nodes_bound positions
  unfold openingLength proofCapacity
  omega

private theorem observed_store_outside (before after : MachineState) (dest value address : Word)
    (memory : after.mem = (before.setMem dest value).mem) (outside : address ≠ dest) :
    after.getMem address = before.getMem address := by
  have observed : after.getMem address = (before.setMem dest value).getMem address :=
    congrFun memory address
  exact observed.trans (MachineState.getMem_setMem_ne outside)

attribute [local irreducible] markParentPrefix execute

private theorem sweep_frame (state : MachineState) (remaining address : Nat) (bounded : remaining < 256)
    (above : trapdoorBase ≤ address) (fit : address < 2^64)
    (pc : state.pc = if remaining = 0 then 0x10dc else 0x10b4)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have parentPC : state.pc = 0x10b4 := by simpa using pc
    have ⟨_, _, parent⟩ := mark_addresses state (remaining+1) base count
    have mark := mark_parent_post state parentPC
    have different : BitVec.ofNat 64 address ≠ parentAddress state := by
      rw [parent]
      intro same
      have below := marks_before_trapdoor
      have cellFit : markBase + 8*(remaining+1) < 2^64 := by unfold markBase; omega
      have eq := nat_address_injective fit cellFit same
      omega
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) parentPC count
    have nextBase := mark.2.1.trans base
    have earlier := observed_store_outside _ _ _ _ _ mark.1 different
    change (markMachine (markParentPrefix state 10) remaining).getMem (BitVec.ofNat 64 address) = _
    exact (ih _ (by omega) nextPC nextBase nextCount).trans earlier

theorem cap_preparation_frame (state : MachineState) (address : Nat) (above : trapdoorBase ≤ address)
    (fit : address < 2^64) (base : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    (capPreparation state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  change (markMachine (markSweepEntry state) 255).getMem (BitVec.ofNat 64 address) =
    (markSweepEntry state).getMem (BitVec.ofNat 64 address)
  exact sweep_frame _ 255 address (by decide) above fit rfl base rfl

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem abi_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem root_exit (state : MachineState) (pc : state.pc = 0x1128)
    (root : state.getReg .x6 = 1#64) (fuel : Nat) (allowCoins : Bool) :
    let result := exitPrefix (advancePrefix state 19 2) 3
    execute openingImage (6 + fuel) state allowCoins = pure ⟨.success, result, 6, 0⟩ ∧
    result.mem = state.mem ∧ result.getReg .x11 = state.getReg .x21 - state.getReg .x20 := by
  let checked := advancePrefix state 19 2
  have ready : checked.pc = 0x1148 := by rw [advance_root_target state pc, root]; simp
  have memory : checked.mem = state.mem := by
    simp [checked, advancePrefix, capWalkInstructions, execInstrBr, signExtend12, root]
    rfl
  have dest : checked.getReg .x21 = state.getReg .x21 := by
    simp [checked, advancePrefix, capWalkInstructions, execInstrBr, signExtend12, root]
  have start : checked.getReg .x20 = state.getReg .x20 := by
    simp [checked, advancePrefix, capWalkInstructions, execInstrBr, signExtend12, root]
  refine ⟨?_, (exit_memory checked).trans memory, ?_⟩
  · rw [show 6 + fuel = 2 + (4 + fuel) by omega, execute_advance_root_test _ pc,
      execute_exit _ ready]
    simp [Execution.charge, checked]
  · rw [exit_register, dest, start]

private theorem terminal_length (state : MachineState) (outputLen : Nat)
    (final : state.getReg .x21 = BitVec.ofNat 64 (proofBase+outputLen))
    (start : state.getReg .x20 = BitVec.ofNat 64 proofBase)
    (fits : proofBase + outputLen ≤ MEMORY_BYTES) :
    (state.getReg .x21 - state.getReg .x20).toNat = outputLen := by
  rw [final, start, BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by
    have : proofBase < 2^64 := by decide
    omega) (by omega), Nat.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold MEMORY_BYTES at fits
  omega

private theorem proof_buffer_fits (positions : Positions) :
    proofBase + openingLength positions ≤ MEMORY_BYTES :=
  (Nat.add_le_add_left (opening_length_bound positions) _).trans proof_fits_memory

private theorem extra_opening_fuel (s : Submission) (abi : OpeningABI s) (positions : Positions)
    (need : Nat) (bounded : need ≤ 13 + 256*positions.card + 2552 + 19*511 + 6) :
    need + (s.steps .opening - need) = s.steps .opening := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have fuel := abi.fuel
  omega

/-- The byte-level result of the honest opener. Heap words and nonces are read
from the actual serialized trapdoor at the same addresses used by commit. -/
structure OpenPhysical (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = openingLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = openingMachineCycles positions
  lower : CompletedRecords s trapdoor positions result.state positions.card
  footer : ∀ i (inside : i < (openingNodes positions).length),
    readBuffer result.state (recordBase positions.card + 32*i) 32 =
      trapdoor.extractLsb' (256 * (openingNodes positions)[i]) 256

private theorem memory_buffer_eq (one two : MachineState) (address count : Nat)
    (memory : one.mem = two.mem) :
    readBuffer one address count = readBuffer two address count := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, memory]

/-- Exact sound, query-free opening execution on every ABI input and cardinality. -/
theorem opening_physical (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    ∃ result, s.run .opening (trapdoor, positions) = pure result ∧ OpenPhysical s trapdoor positions result := by
  let initial := s.initialState .opening (trapdoor, positions)
  have initialCount : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  by_cases empty : positions.card = 0
  · let answer : Execution := ⟨.success, exitPrefix (setupPrefix initial 3) 3, 7, 0⟩
    have ran := execute_empty initial rfl (s.steps .opening - 7) true (by rw [initialCount, empty])
    refine ⟨answer, ?_, ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩⟩
    · change execute (s.image .opening) (s.steps .opening) initial true = pure answer
      rw [abi.image, ← extra_opening_fuel s abi positions 7 (by omega)]
      exact ran
    · change ((exitPrefix (setupPrefix initial 3) 3).getReg .x11).toNat = _
      rw [empty_proof_length]
      simp [openingLength, openingNodes, empty]
    · simp [answer, openingMachineCycles, empty]
    · intro ordinal present _
      omega
    · intro i inside
      simp [openingNodes, empty] at inside
  · let lower := recordsMachine (setupPrefix initial 13) positions.card
    let groups := groupsBefore positions positions.card
    let nodes := capFrontierNodes groups 1 8
    let dest := recordBase positions.card
    let phase := capPreparation lower
    have nodesEqual : openingNodes positions = nodes := by simp [openingNodes, empty, nodes, groups]
    have lengthPos : 0 < positions.card := by omega
    have boundary : RecordBoundary s trapdoor positions lower positions.card :=
      (execute_opening_records s abi.toOpeningLayout trapdoor positions lengthPos 0 true).2
    have ranLower : RunsOpeningBlock initial lower (13+256*positions.card) :=
      fun fuel coins => (execute_opening_records s abi.toOpeningLayout trapdoor positions lengthPos fuel coins).1
    have control := opening_first_boundary s abi.toOpeningLayout trapdoor positions lengthPos
    have lowerBytes : CompletedRecords s trapdoor positions lower positions.card := by
      have all := records_contents s abi.toOpeningLayout trapdoor positions (setupPrefix initial 13) 0
        positions.card (by omega) control (fun ordinal _ h => by omega)
      simpa only [Nat.zero_add] using all
    have marks : RecordMarks positions lower positions.card := by
      have all := records_marks s abi.toOpeningLayout trapdoor positions (setupPrefix initial 13) 0
        positions.card (by omega) control (initial_record_marks s abi.toOpeningLayout abi.image trapdoor positions)
      simpa only [Nat.zero_add] using all
    have initCap : lower.pc = 0x10b0 := by simpa using boundary.pc
    have ranPrep : RunsOpeningBlock lower phase 2552 := execute_cap_preparation lower initCap boundary.marks
    have ⟨startPC, atRoot, startPtr, context⟩ := cap_preparation_context s trapdoor positions lower boundary marks
    have fits : dest + 32*nodes.length ≤ MEMORY_BYTES := by
      simpa [openingLength, nodesEqual, dest, recordBase, Nat.add_assoc] using proof_buffer_fits positions
    have startAligned : dest % 8 = 0 := by
      norm_num [dest, recordBase, proofBase, indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH]
      omega
    have begin : proofBase ≤ dest := by unfold dest recordBase; omega
    obtain ⟨capEnd, ranCap, endPC, endPtr, footer⟩ := execute_cap_subtree groups phase 1 8 dest
      cap_span_root ⟨context, atRoot, startPtr⟩ startPC begin startAligned fits
    let cycles := (13 + 256*positions.card + 2552 + capSubtreeCycles groups 1 8) + 6
    let after := exitPrefix (advancePrefix capEnd 19 2) 3
    let answer : Execution := ⟨.success, after, cycles, 0⟩
    have capBound := cap_subtree_cycle_bound groups 1 8
    norm_num at capBound
    have steps := extra_opening_fuel s abi positions cycles (by unfold cycles; omega)
    have ⟨ranExit, exitMem, lenReg⟩ := root_exit capEnd endPC endPtr.nodeWord (s.steps .opening - cycles) true
    have ran := ((ranLower.next ranPrep).next ranCap) (6 + (s.steps .opening - cycles)) true
    refine ⟨answer, ?_, ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩⟩
    · change execute (s.image .opening) (s.steps .opening) initial true = pure answer
      rw [abi.image, ← steps]
      rw [show cycles + (s.steps .opening - cycles) =
        (13 + 256*positions.card + 2552 + capSubtreeCycles groups 1 8) +
          (6+(s.steps .opening-cycles)) by unfold cycles; omega, ran, ranExit]
      simp [answer, Execution.charge, cycles, after]
    · change (after.getReg .x11).toNat = openingLength positions
      rw [lenReg]
      have finalAddress : capEnd.getReg .x21 = BitVec.ofNat 64 (proofBase + openingLength positions) := by
        simpa [dest, recordBase, openingLength, nodesEqual, Nat.add_assoc] using endPtr.destWord
      exact terminal_length capEnd _ finalAddress endPtr.context.proofStart (proof_buffer_fits positions)
    · simp [answer, cycles, openingMachineCycles, empty, groups]
    · have capFit : dest < 2^64 := by unfold MEMORY_BYTES at fits; omega
      have stable (address : Nat) (above : trapdoorBase ≤ address) (before : address < dest) :
          after.getMem (BitVec.ofNat 64 address) = lower.getMem (BitVec.ofNat 64 address) := by
        have fit := before.trans capFit
        have restored : after.getMem (BitVec.ofNat 64 address) = capEnd.getMem (BitVec.ofNat 64 address) :=
          congrFun exitMem (BitVec.ofNat 64 address)
        exact restored.trans ((footer.frame _ fit (Or.inl before)).trans
          (cap_preparation_frame lower _ above fit boundary.marks))
      intro ordinal present _
      let index := sortedIndex positions ordinal present
      have actual := lowerBytes ordinal present present
      have aboveProof : trapdoorBase ≤ proofBase := by decide
      refine ⟨?_, ?_, ?_⟩
      · intro address lo hi
        have early : address < dest := by unfold dest recordBase; omega
        exact (stable address lo early).trans (actual.input address lo hi)
      · have ⟨_, aligned, _, _⟩ := ordinal_nonce_geometry index ordinal (by omega)
        have same : readBuffer after (recordBase ordinal) 16 = readBuffer lower (recordBase ordinal) 16 := by
          apply copied_buffer _ _ _ _ 2 aligned aligned (by decide)
          intro j hj
          exact stable _ (by unfold recordBase; omega) (by unfold dest recordBase; omega)
        exact same.trans actual.nonce
      · intro level inside
        have ⟨_, aligned, _, _⟩ := ordinal_sibling_geometry index ordinal level (by omega) inside
        have same : readBuffer after (siblingDest ordinal level) 32 =
          readBuffer lower (siblingDest ordinal level) 32 := by
          apply copied_buffer _ _ _ _ 4 aligned aligned (by decide)
          intro j hj
          exact stable _ (by unfold siblingDest recordBase; omega) (by unfold dest siblingDest recordBase; omega)
        exact same.trans (actual.sibling level inside)
    · intro i inside
      have within : i < nodes.length := by simpa [nodesEqual] using inside
      have nodeEq : (openingNodes positions)[i] = nodes[i] := by
        simp only [nodesEqual]
      rw [nodeEq]
      change readBuffer after (dest+32*i) 32 = _
      rw [memory_buffer_eq after capEnd _ _ exitMem, footer.digest i within]
      let node := nodes[i]
      have bounded : node < 512 := cap_frontier_nodes_small groups 1 8 cap_span_root _ (List.getElem_mem _)
      have ⟨aligned, before⟩ := cap_digest_bounds node bounded
      have earlier : readBuffer phase (capDigestAddress node) 32 =
          readBuffer initial (capDigestAddress node) 32 := by
        apply copied_buffer _ _ _ _ 4 aligned aligned (by decide)
        intro j hj
        have low : trapdoorBase ≤ capDigestAddress node + 8*j := by unfold capDigestAddress; omega
        have high : capDigestAddress node + 8*j < proofBase := by omega
        have addressFits : capDigestAddress node + 8*j < 2^64 := high.trans (by decide)
        exact (cap_preparation_frame lower _ low addressFits boundary.marks).trans (boundary.input _ low high)
      rw [earlier]
      exact input_digest s abi.toOpeningLayout trapdoor positions node (by
        have capSmall : 512 < 2*LENGTH := by decide
        omega)

end TwoPermutationPrototype.Opening
