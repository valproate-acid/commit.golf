import CommitGolfCandidate.TwoPermutationPackedOpeningInitial
import CommitGolfCandidate.TwoPermutationPackedOpeningFinish

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp Sampling
open Opening (OpeningLayout trapdoorBase proofBase groupsBefore openingNodes capDigestAddress)

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : PackedOpening.capacity ≤ s.sizes.proof
  fuel : 17179934720 ≤ s.steps .opening

structure OpenPhysical (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) : Prop where
  success : result.exit = .success
  length : (result.state.getReg .x11).toNat = proofLength positions
  noCalls : result.oracleCalls = 0
  cycles : result.cycles = scheduledCycles positions
  lower : CompletedRecords s trapdoor positions result.state positions.card
  footer : ∀ i (inside : i < (openingNodes positions).length),
    readBuffer result.state (recordBase positions.card+30*i) 30 =
      (trapdoor.extractLsb' (256*(openingNodes positions)[i]) 256).extractLsb' 0 240

private theorem byte_memory (before after : MachineState) (address : Nat) (fit : address < MEMORY_BYTES)
    (frame : ∀ query : Nat, trapdoorBase ≤ query → query < 2^64 →
      after.getMem (BitVec.ofNat 64 query) = before.getMem (BitVec.ofNat 64 query))
    (above : trapdoorBase ≤ address) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  let aligned := alignToDword (BitVec.ofNat 64 address)
  have safe : MEMORY_BYTES+8 ≤ 2^64 := by decide
  have lower := aligned_dword_above trapdoorBase address (by decide) above (by omega)
  have stable := frame aligned.toNat lower aligned.isLt
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at stable
  change extractByte (after.getMem aligned) _ = _
  rw [stable]
  rfl

attribute [local irreducible] execute capPreparation setupPrefix readBuffer

theorem opening_physical_with (recordsExecute : RecordsExecute) (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    ∃ result : Execution, s.run .opening (trapdoor, positions) = pure result ∧ OpenPhysical s trapdoor positions result := by
  let initial := s.initialState .opening (trapdoor, positions)
  have countReg : initial.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have budget : scheduledCycles positions ≤ s.steps .opening := (scheduled_fuel_fits positions).trans abi.fuel
  have allFit := (Nat.add_le_add_left (proof_fits_every_cardinality positions) _).trans packed_proof_memory
  by_cases empty : positions.card = 0
  · let result : Execution := ⟨.success, exitPrefix (setupPrefix initial 3) 3, 7, 0⟩
    have charge : scheduledCycles positions = 7 := by simp [scheduledCycles, empty]
    have steps : 7+(s.steps .opening-7) = s.steps .opening := by rw [charge] at budget; omega
    refine ⟨result, ?_, ⟨rfl, ?_, rfl, charge.symm, ?_, ?_⟩⟩
    · change execute (s.image .opening) (s.steps .opening) initial true = pure result
      rw [abi.image, ← steps]
      exact execute_empty initial rfl _ true (by rw [countReg, empty])
    · change ((exitPrefix (setupPrefix initial 3) 3).getReg .x11).toNat = _
      rw [empty_proof_length]
      simp [proofLength, openingNodes, empty]
    · intro ordinal present _
      omega
    · intro i inside
      simp [openingNodes, empty] at inside
  · let grouped := groupsBefore positions positions.card
    let nodes := capFrontierNodes grouped 1 8
    let dest := recordBase positions.card
    let begin := setupPrefix initial 13
    let lower := runRecords positions.card 0 positions.card begin
    let prepared := capPreparation lower
    have positive : 0 < positions.card := by omega
    have ready := opening_first_boundary s abi.toOpeningLayout trapdoor positions positive
    have marks := initial_record_marks s abi.toOpeningLayout abi.image trapdoor positions
    have assembled := recordsExecute s abi.toOpeningLayout trapdoor positions begin 0 positions.card
      (by omega) ready marks (fun j _ first => (by omega : False).elim)
    have atCap : RecordBoundary s trapdoor positions lower positions.card := by
      simpa only [Nat.zero_add] using assembled.boundary
    have written : CompletedRecords s trapdoor positions lower positions.card := by
      simpa only [Nat.zero_add] using assembled.bytes
    have groups : Opening.RecordMarks positions lower positions.card := by
      simpa only [Nat.zero_add] using assembled.marks
    have leafMarks (node : Nat) (leaf : 255 < node) (inside : node < 512) :
        Opening.machineMarks lower node = Opening.markWord grouped node := by
      rw [groups node inside, Opening.mark_word_leaf grouped ⟨node,inside⟩ (show 256 ≤ node by omega)]
    have ⟨rootPC, root⟩ := cap_preparation_context lower grouped dest
      atCap.marks atCap.capHeap atCap.capLeaves atCap.proofBegin atCap.dest leafMarks
    have frontier : openingNodes positions = nodes := by simp [openingNodes, empty, nodes, grouped]
    have room : dest+30*nodes.length ≤ MEMORY_BYTES := by
      simpa only [proofLength, frontier, dest, recordBase, Nat.add_assoc] using allFit
    have aligned : dest % 2 = 0 := by
      have base : proofBase % 2 = 0 := by decide
      unfold dest recordBase recordBytes
      omega
    have above : proofBase ≤ dest := by unfold dest recordBase; omega
    obtain ⟨after, ranCap, afterPC, endPosition, footerBytes⟩ :=
      cap_subtree grouped prepared 1 8 dest Opening.cap_span_root root rootPC above aligned room
    let final := exitPrefix (advancePrefix after 41 2) 3
    have charge : scheduledCycles positions = 13+(590*positions.card-1)+2552+capSubtreeCycles grouped 1 8+6 := by
      rw [scheduledCycles, if_neg empty]
      dsimp only [grouped]
      omega
    have enough : scheduledCycles positions+(s.steps .opening-scheduledCycles positions) = s.steps .opening := by omega
    let surplus := s.steps .opening-scheduledCycles positions
    have ranSetup : RunsOpeningBlock initial begin 13 :=
      fun fuel coins => execute_setup initial rfl fuel coins (countReg ▸ nonempty_count positions positive)
    have ranRecords : RunsOpeningBlock begin lower (590*positions.card-1) := by
      have charged : recordsCost positions.card 0 positions.card = 590*positions.card-1 := by
        simp [recordsCost, positive]
      exact charged ▸ assembled.run
    have ranPrep : RunsOpeningBlock lower prepared 2552 :=
      execute_cap_preparation lower (by simpa using atCap.pc) atCap.marks
    have ⟨ranExit, finalMem, retLen⟩ := root_exit after afterPC endPosition.nodeWord surplus true
    have lowerFrame (address : Nat) (fromProof : proofBase ≤ address) (beforeCap : address < dest) :
        final.getByte (BitVec.ofNat 64 address) = lower.getByte (BitVec.ofNat 64 address) := by
      have byteFit : address < MEMORY_BYTES := by omega
      have safe : MEMORY_BYTES < 2^64 := by decide
      have heapBefore : trapdoorBase ≤ proofBase := by decide
      have prepStable := byte_memory lower prepared address byteFit
        (fun query low fit => cap_preparation_frame lower query low fit atCap.marks)
        (heapBefore.trans fromProof)
      have unchanged := (footerBytes.frame address (by omega) (Or.inl beforeCap)).trans prepStable
      have eq : final.mem = after.mem := finalMem
      simpa only [MachineState.getByte, MachineState.getMem, eq] using unchanged
    let result : Execution := ⟨.success, final, scheduledCycles positions, 0⟩
    refine ⟨result, ?_, ⟨rfl, ?_, rfl, rfl, ?_, ?_⟩⟩
    · change execute (s.image .opening) (s.steps .opening) initial true = pure result
      rw [abi.image, ← enough]
      change execute openingImage (scheduledCycles positions+surplus) initial true = pure result
      have amount : scheduledCycles positions+surplus =
          13+(590*positions.card-1)+2552+capSubtreeCycles grouped 1 8+(6+surplus) := by
        exact congrArg (fun amount => amount+surplus) charge |>.trans (Nat.add_assoc _ 6 surplus)
      have prefixTrace := (((ranSetup.next ranRecords).next ranPrep).next ranCap) (6+surplus) true
      rw [amount, prefixTrace, ranExit]
      simp [Execution.charge, result, final, charge, Nat.add_comm]
    · change (final.getReg .x11).toNat = _
      have ret : final.getReg .x11 = after.getReg .x21-after.getReg .x20 := retLen
      rw [ret]
      apply terminal_length after _ _ endPosition.context.proofStart allFit
      simpa only [proofLength, frontier, dest, recordBase, Nat.add_assoc] using endPosition.destWord
    · intro ordinal present _
      obtain ⟨nonce, siblings⟩ := written ordinal present present
      constructor
      · intro byte inside
        have prefixTrace : recordBase ordinal+byte < dest := by unfold dest recordBase recordBytes; omega
        exact (lowerFrame _ (by unfold recordBase; omega) prefixTrace).trans (nonce byte inside)
      · intro level levelBound byte inside
        have prefixTrace : siblingDestination ordinal level+byte < dest := by
          have reached := destination_mono ordinal (show level+1 ≤ 16 by omega)
          rw [record_end] at reached
          have step : siblingDestination ordinal (level+1) =
              siblingDestination ordinal level+siblingWidth level := by
            simp only [siblingDestination, sibling_offset_next, Nat.add_assoc]
          unfold dest recordBase recordBytes at *
          omega
        exact (lowerFrame _ (by unfold siblingDestination recordBase; omega) prefixTrace).trans
          (siblings level levelBound byte inside)
    · intro i inside
      have insideNodes : i < nodes.length := frontier ▸ inside
      let node := nodes[i]'insideNodes
      have nodeEq : (openingNodes positions)[i] = node := by
        have found := congrArg (fun l : List Nat => l[i]?) frontier
        rw [List.getElem?_eq_getElem inside, List.getElem?_eq_getElem insideNodes] at found
        exact Option.some.inj found
      rw [nodeEq]
      have small : node < 512 := Opening.cap_frontier_nodes_small grouped 1 8 Opening.cap_span_root
        node (List.getElem_mem insideNodes)
      have stable : readBuffer prepared (capDigestAddress node) 32 =
          readBuffer initial (capDigestAddress node) 32 := by
        have ⟨aligned, beforeProof⟩ := Opening.cap_digest_bounds node small
        apply Opening.copied_buffer _ _ _ _ 4 aligned aligned (by decide)
        intro j low
        have aboveHeap : trapdoorBase ≤ capDigestAddress node+8*j := by unfold capDigestAddress; omega
        have belowProof : capDigestAddress node+8*j < proofBase := by omega
        have fit : proofBase < 2^64 := by decide
        exact (cap_preparation_frame lower _ aboveHeap (by omega) atCap.marks).trans
          (atCap.input _ aboveHeap belowProof)
      have digest : readBuffer initial (capDigestAddress node) 32 =
          trapdoor.extractLsb' (256*node) 256 :=
        Opening.input_digest s abi.toOpeningLayout trapdoor positions node
          (small.trans_le (by decide : 512 ≤ 2*LENGTH))
      have written := footerBytes.digest i insideNodes
      rw [stable, digest] at written
      have returnMem : final.mem = after.mem := finalMem
      change readBuffer final (dest+30*i) 30 = _
      have saved : readBuffer final (dest+30*i) 30 = readBuffer after (dest+30*i) 30 := by
        simp only [readBuffer, MachineState.getByte, MachineState.getMem, returnMem]
      exact saved.trans written

theorem opening_success (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    s.openingSucceeded result = true := by
  have bytes : (result.state.getReg .x11).toNat ≤ s.sizes.proof := by
    rw [physical.length]
    exact (proof_fits_every_cardinality positions).trans abi.capacity
  simp [Submission.openingSucceeded, physical.success, bytes]

theorem opening_scored_limits (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (result : Execution) (physical : OpenPhysical s trapdoor positions result)
    (count : positions.card = BATCH) :
    result.cycles ≤ 88311 ∧ (result.state.getReg .x11).toNat ≤ 67584 := by
  rw [physical.cycles, physical.length]
  exact scheduled_scored_limits positions count

end TwoPermutationPrototype.PackedOpening
