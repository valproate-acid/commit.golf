import CommitGolfCandidate.TwoPermutationCollectTable
import CommitGolfCandidate.TwoPermutationCheckObservation
import CommitGolfCandidate.TwoPermutationCheckerCapWalk

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

theorem checker_cap_bindings (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (lowerRows capRows : List PublicRow)
    (table : CollectedTable oracle input input.positions.card state lowerRows)
    (framed : RecordInputFrame input input.positions.card state)
    (paths : ∀ leaf ∈ Opening.groupsBefore input.positions input.positions.card, 256 ≤ leaf → leaf < 512 →
      RecordedPath capRows leaf 8 (capRootAt state leaf) (readBuffer state (8*536871424) 32)) :
    ∀ index : {i // i ∈ input.positions},
      Nonempty (RecordedOpening oracle index.val (input.values index) input.commitment (lowerRows++capRows)) := by
  intro index
  obtain ⟨seen, ⟨lower⟩⟩ := collect_authenticated_index oracle input state lowerRows table index
  obtain ⟨low, high⟩ := checker_cap_group index.val
  have cap := paths (capGroup index.val) seen low high
  have root : readBuffer state (8*536871424) 32 = input.commitment :=
    record_input_root input input.positions.card state framed
  rw [root] at cap
  exact ⟨(lower.mono fun _ => List.mem_append_left _).join
    (cap.mono fun _ => List.mem_append_right _)⟩

theorem checker_global_budget (input : CheckInput) (records capQueries : Nat)
    (recordBound : records ≤ input.positions.card)
    (capBound : capQueries ≤ 8*input.positions.card) :
    18*records+capQueries ≤ 26*input.positions.card ∧ 18*records+capQueries ≤ 2^30 := by
  have card := checker_positions_bound input
  omega

theorem checker_footer_address (input : CheckInput) :
    8*checkNonceWord input.positions.card = Assembly.submission.layout.proof+528*input.positions.card := by
  change 8*(1291846156+66*input.positions.card)=10334769248+528*input.positions.card
  omega

theorem checker_honest_footer_end (oracle : Oracle) (message : Message) (positions : Positions)
    (salts : CompleteSaltTape) :
    let input := honestCheckInput oracle message positions salts
    let count := (Opening.openingNodes positions).length
    8*(checkNonceWord positions.card+4*count) = Assembly.submission.layout.proof+input.proof.length := by
  dsimp only
  rw [honest_proof_length]
  unfold Opening.openingLength checkNonceWord
  change 8*(1291846156+66*positions.card+4*(Opening.openingNodes positions).length) =
    10334769248+(528*positions.card+32*(Opening.openingNodes positions).length)
  omega

theorem checker_cap_marks (oracle : Oracle) (input : CheckInput) (state : MachineState) (rows : List PublicRow)
    (table : CollectedTable oracle input input.positions.card state rows) :
    ∀ node, 256 ≤ node → node < 512 →
      machineMarks state node = Opening.markWord (Opening.groupsBefore input.positions input.positions.card) node := by
  intro node low high
  exact (table.marks node high).trans (Opening.mark_word_leaf _ ⟨node,high⟩ low).symm

theorem checker_cap_memory_room (input : CheckInput) :
    let groups := Opening.groupsBefore input.positions input.positions.card
    4096 ≤ checkNonceWord input.positions.card ∧
      checkNonceWord input.positions.card+4*(capFrontierNodes groups 1 8).length ≤ 2^33 := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  have cardinal := checker_positions_bound input
  have frontier : (capFrontierNodes groups 1 8).length ≤ 128 := by
    rw [cap_frontier_length]
    exact production_boundary_bound _
  change 4096 ≤ 1291846156+66*input.positions.card ∧
    1291846156+66*input.positions.card+4*(capFrontierNodes groups 1 8).length ≤ 2^33
  omega

theorem checker_honest_cap_nodes (positions : Positions) (nonempty : positions.card ≠ 0) :
    Opening.openingNodes positions = capFrontierNodes (Opening.groupsBefore positions positions.card) 1 8 := by
  rw [Opening.openingNodes, ite_eq_right nonempty]

theorem checker_honest_cap_heap (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) :
    CapHeapCorrect oracle (honestHeap oracle message salts) := by
  intro node positive internal
  have limit : 256 ≤ LENGTH := by decide
  exact transcript_heap_parent false oracle.compression _ node positive (by omega)

theorem checker_honest_cap_data (oracle : Oracle) (input : CheckInput) (state : MachineState)
    (rows : List PublicRow) (table : CollectedTable oracle input input.positions.card state rows)
    (framed : RecordInputFrame input input.positions.card state)
    (cursor : RecordCursor input input.positions.card state) (positive : input.positions.card ≠ 0)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let groups := Opening.groupsBefore input.positions input.positions.card
    let pointer := checkNonceWord input.positions.card
    let heap := honestHeap oracle message salts
    CapContents groups state 1 8 pointer heap ∧
      readBuffer state (8*536871424) 32 = heap 1 ∧
      state.getReg .x22 = wordAddress (pointer+4*(capFrontierNodes groups 1 8).length) := by
  let groups := Opening.groupsBefore input.positions input.positions.card
  let pointer := checkNonceWord input.positions.card
  let heap := honestHeap oracle message salts
  have reframed : RecordInputFrame (honestCheckInput oracle message input.positions salts) input.positions.card state :=
    canonical ▸ framed
  have nodes : Opening.openingNodes input.positions = capFrontierNodes groups 1 8 :=
    checker_honest_cap_nodes input.positions positive
  refine ⟨⟨?_,?_⟩,?_ ,?_⟩
  · intro leaf seen _ _ _
    exact table.honest message salts canonical leaf seen
  · intro i bounded
    have present : i < (Opening.openingNodes input.positions).length := by rwa [nodes]
    have content := record_honest_frontier oracle message input.positions salts state reframed i present
    have index := List.getElem_of_eq nodes present
    rw [index] at content
    exact content
  · have root := record_input_root input input.positions.card state framed
    exact root.trans (congrArg CheckInput.commitment canonical)
  · rw [cursor.proofEnd]
    have finish := checker_honest_footer_end oracle message input.positions salts
    change 8*(pointer+4*(Opening.openingNodes input.positions).length) =
      10334769248+(honestCheckInput oracle message input.positions salts).proof.length at finish
    rw [nodes] at finish
    have proofLen := congrArg (fun value : CheckInput => value.proof.length) canonical
    change BitVec.ofNat 64 (10334769248+input.proof.length) =
      BitVec.ofNat 64 (8*(pointer+4*(capFrontierNodes groups 1 8).length))
    rw [proofLen,finish]

end TwoPermutationPrototype.Checker
