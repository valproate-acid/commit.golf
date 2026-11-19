import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCheckerBody
import CommitGolfCandidate.TwoPermutationPackedCapComplete

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame capRootAt checker_positions_bound record_input_root
  checker_honest_cap_nodes record_groups_length)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honestHeap honest_proof_length honest_frontier_digest honest_projected_node)
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

private theorem frontier_node_bounds (groups : List Nat) (node height : Nat)
    (span : Opening.CapSpan node height) (entry : Nat)
    (member : entry ∈ capFrontierNodes groups node height) : 0 < entry ∧ entry < 512 := by
  induction height generalizing node with
  | zero =>
    unfold capFrontierNodes at member
    split at member
    · simp at member
    · rw [List.mem_singleton] at member
      subst entry
      exact Opening.cap_span_node _ _ span
  | succ height ih =>
    unfold capFrontierNodes at member
    split at member
    · obtain ⟨left,right⟩ := Opening.cap_span_children node height span
      rcases List.mem_append.mp member with child | child
      · exact ih _ left child
      · exact ih _ right child
    · rw [List.mem_singleton] at member
      subst entry
      exact Opening.cap_span_node _ _ span

private theorem checker_cap_frontier_bound (input : CheckInput) :
    (capFrontierNodes (Opening.groupsBefore input.positions input.positions.card) 1 8).length ≤ 128 := by
  rw [cap_frontier_length]
  exact production_boundary_bound _

theorem checker_cap_ready (oracle : Oracle) (input : CheckInput) (state : MachineState) (rows : List PublicRow)
    (cursor : RecordCursor input input.positions.card state)
    (table : CollectedTable oracle input input.positions.card state rows) :
    CapSuffixReady (Opening.groupsBefore input.positions input.positions.card) state
      (checkProofByte input.positions.card) 536871424 := by
  refine ⟨cursor.pc.trans (ite_eq_left rfl),
    cursor.proof,cursor.capRoots,cursor.marks,cursor.capCount,cursor.selector,cursor.commitment,?_ ,
    ?_,?_ ,?_ ,by decide,by decide⟩
  · intro node low high
    exact (table.marks node high).trans (Opening.mark_word_leaf _ ⟨node,high⟩ low).symm
  · unfold checkProofByte
    omega
  · unfold checkProofByte
    omega
  · have card := checker_positions_bound input
    have frontier := checker_cap_frontier_bound input
    unfold MEMORY_BYTES checkProofByte
    omega

theorem checker_honest_cap_data (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (rows : List PublicRow) (table : CollectedTable oracle input input.positions.card state rows)
    (framed : RecordInputFrame input input.positions.card state)
    (cursor : RecordCursor input input.positions.card state) (positive : input.positions.card ≠ 0)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let groups := Opening.groupsBefore input.positions input.positions.card
    let pointer := checkProofByte input.positions.card
    let heap := honestHeap oracle message salts
    CapContents groups state 1 8 pointer heap ∧
      readBuffer state (8*536871424) 32 = heap 1 ∧
      state.getReg .x22 = BitVec.ofNat 64 (pointer+30*(capFrontierNodes groups 1 8).length) := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  let pointer := checkProofByte input.positions.card
  let heap := honestHeap oracle message salts
  let honest := honestCheckInput oracle message input.positions salts
  have reframed : RecordInputFrame honest input.positions.card state :=
    Eq.mp (congrArg (fun bytes => RecordInputFrame bytes input.positions.card state) canonical) framed
  have nodes : Opening.openingNodes input.positions = capFrontierNodes groups 1 8 :=
    checker_honest_cap_nodes input.positions positive
  refine ⟨⟨?_,?_⟩,?_ ,?_⟩
  · intro leaf seen _ _ _
    exact table.honest message salts canonical leaf seen
  · intro i bounded
    change i < (capFrontierNodes groups 1 8).length at bounded
    have present : i < (Opening.openingNodes input.positions).length := by rwa [nodes]
    have limit : pointer+30*i+30 ≤ 2^36 := by
      have geom := (checker_cap_ready oracle input state rows cursor table).proofRoom
      change pointer+30*(capFrontierNodes groups 1 8).length ≤ 2^36 at geom
      omega
    have frame := record_proof_frame honest input.positions.card (30*i) 30 state reframed (by rfl) limit
    have raw := honest_frontier_digest oracle message input.positions salts i present
    rw [PackedChecker.initial_state] at raw
    have addr : PackedChecker.submission.layout.proof+(498*input.positions.card+30*i) =
        pointer+30*i := by change 10334769248+(498*input.positions.card+30*i) = _; unfold pointer checkProofByte; omega
    rw [addr] at raw
    have index := List.getElem_of_eq nodes present
    rw [index] at raw
    rw [frame,raw]
    have member := List.getElem_mem (l := capFrontierNodes groups 1 8) bounded
    obtain ⟨positiveNode, capNode⟩ := frontier_node_bounds groups 1 8 Opening.cap_span_root _ member
    have length : 512 ≤ LENGTH := by decide
    exact honest_projected_node _ _ _ positiveNode (by omega)
  · have root := record_input_root input input.positions.card state framed
    exact root.trans (congrArg CheckInput.commitment canonical)
  · rw [cursor.proofEnd]
    have proofLen := congrArg (fun value : CheckInput => value.proof.length) canonical
    change BitVec.ofNat 64 (10334769248+input.proof.length) =
      BitVec.ofNat 64 (pointer+30*(capFrontierNodes groups 1 8).length)
    rw [proofLen,honest_proof_length]
    apply congrArg (BitVec.ofNat 64)
    dsimp only [pointer,checkProofByte,PackedOpening.proofLength,PackedOpening.recordBytes]
    rw [nodes]
    omega

theorem checker_cap_facts (oracle : Oracle) (input : CheckInput) (positive : input.positions.card ≠ 0)
    (state : MachineState) (rows : List PublicRow) (fuel : Nat) (enough : 25056 ≤ fuel)
    (cursor : RecordCursor input input.positions.card state)
    (framed : RecordInputFrame input input.positions.card state)
    (table : CollectedTable oracle input input.positions.card state rows) :
    CheckerCapFacts oracle input state fuel := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  let pointer := checkProofByte input.positions.card
  have ready := checker_cap_ready oracle input state rows cursor table
  have cap := execute_cap_suffix oracle groups state pointer 536871424 fuel ready enough
  refine ⟨cap.terminates,?_,cap.paths,?_⟩
  · have calls := cap.honestCalls
    rw [show groups.length = input.positions.card from record_groups_length input _ (by rfl)] at calls
    exact calls
  · intro message salts canonical
    obtain ⟨data, root, ending⟩ := checker_honest_cap_data oracle input state rows table framed cursor
      positive message salts canonical
    exact cap.honest (honestHeap oracle message salts) (canonical_cap_heap oracle (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)) data root ending

end TwoPermutationPrototype.Packed.Checker
