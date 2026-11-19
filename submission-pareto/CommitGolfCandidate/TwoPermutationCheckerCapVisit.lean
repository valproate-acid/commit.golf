import CommitGolfCandidate.TwoPermutationCheckerCapTransitions
import CommitGolfCandidate.TwoPermutationOpeningCapStructure

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

structure CapContext (groups : List Nat) (state : MachineState) : Prop where
  controls : CapControls state
  marked : ∀ node, 0 < node → node < 512 →
    memoryView state (512+node) = Opening.markWord groups node

theorem CapContext.transport {groups : List Nat} {before after : MachineState}
    (context : CapContext groups before) (stable : CapStable before after)
    (markFrame : ∀ word, 513 ≤ word → word < 1024 → memoryView after word = memoryView before word) :
    CapContext groups after :=
  ⟨context.controls.transport stable, fun node pos bound =>
    (markFrame _ (by omega) (by omega)).trans (context.marked node pos bound)⟩

structure CapPosition (groups : List Nat) (state : MachineState) (node pointer : Nat) : Prop where
  context : CapContext groups state
  heap : state.getReg .x6 = BitVec.ofNat 64 node
  proof : state.getReg .x21 = wordAddress pointer
  above : 4096 ≤ pointer

theorem cap_lookup_is_marked {groups : List Nat} {state : MachineState} {node height proof : Nat}
    (position : CapPosition groups state node proof) (span : Opening.CapSpan node height) :
    capMarkedWord state = 0#64 ↔ capIsMarked groups node height = false := by
  obtain ⟨pos, bound⟩ := Opening.cap_span_node node height span
  rw [cap_lookup_observation state node position.context.controls position.heap,
    position.context.marked node pos bound, Opening.markWord, Opening.cap_span_height node height span]
  cases capIsMarked groups node height <;> decide

theorem cap_lookup_position {groups : List Nat} {state : MachineState} {node height proof : Nat}
    (position : CapPosition groups state node proof) (span : Opening.CapSpan node height) :
    let next := capLookup state
    let marked := capIsMarked groups node height
    next.pc = (if marked then if height = 0 then 0x12e4 else 0x1294 else 0x12b0) ∧
    CapPosition groups next (if marked && height != 0 then 2*node else node) proof ∧ next.mem = state.mem := by
  obtain ⟨pc, heap, mem⟩ := cap_lookup_post state
  dsimp only at pc heap mem ⊢
  have proofReg : (capLookup state).getReg .x21 = wordAddress proof :=
    (cap_lookup_register state .x21 (by decide) (by decide) (by decide)).trans position.proof
  have ctxt := position.context.transport (cap_lookup_stable state) (fun _ _ _ => congrFun mem _)
  have marked := cap_lookup_is_marked position span
  have leaf := cap_lookup_leaf_iff state node (Opening.cap_span_node node height span).2
    position.context.controls position.heap
  constructor
  · rw [pc]
    simp only [marked, leaf]
    cases height with
    | zero =>
      have valid := Opening.cap_span_is_leaf node span
      cases capIsMarked groups node 0 <;> simp [valid]
    | succ height =>
      have internal := Opening.cap_span_is_internal node height span
      cases capIsMarked groups node (height+1) <;> simp [Nat.not_le_of_gt internal]
  · refine ⟨⟨ctxt, ?_, proofReg, position.above⟩, mem⟩
    have leaf' := leaf
    rw [position.heap] at leaf'
    rw [heap, position.heap]
    simp only [marked, leaf']
    cases height with
    | zero =>
      have valid := Opening.cap_span_is_leaf node span
      cases capIsMarked groups node 0 <;> simp [valid]
    | succ height =>
      have internal := Opening.cap_span_is_internal node height span
      have shift := cap_lookup_left_word state node position.heap
      rw [position.heap] at shift
      cases capIsMarked groups node (height+1) <;> simp [Nat.not_le_of_gt internal, shift]

theorem cap_frontier_position {groups : List Nat} {state : MachineState} {node pointer : Nat}
    (position : CapPosition groups state node pointer)
    (ready : FrontierReady state node pointer) :
    CapPosition groups (frontierRead state) node (pointer+4) := by
  refine ⟨position.context.transport (cap_frontier_stable state) ?_,
    (frontier_register state .x6 (by decide) (by decide) (by decide) (by decide)).trans position.heap,
    (frontier_read_pointer ready).2, by have := position.above; omega⟩
  intro word low high
  exact frontier_read_frame ready word (by omega) (Or.inl (by omega))

theorem cap_next_sibling {groups : List Nat} {state : MachineState} {node pointer : Nat}
    (oracle : Oracle) (position : CapPosition groups state (2*node) pointer)
    (pc : state.pc = 0x12e4) (nodeBound : 0 < node ∧ 2*node < 512) :
    let next := capRight (capAfterTests state)
    ∃ segment : Segment oracle state next, segment.steps = 6 ∧ segment.rows = [] ∧
      next.pc = 0x1294 ∧ CapPosition groups next (2*node+1) pointer ∧ next.mem = state.mem := by
  obtain ⟨after, heap⟩ := cap_after_tests state (2*node) (by omega) pc position.heap
  have nextPC : (capAfterTests state).pc = 0x1310 := by rw [after, ite_eq_left (by omega)]
  have post := cap_right_post _ nextPC
  have stable := (cap_tests_stable state).trans (cap_right_stable (capAfterTests state))
  have mem := post.2.2.trans (cap_tests_memory state)
  refine ⟨(capTestsSegment oracle state (2*node) (by omega) pc position.heap).append
      (capRightSegment oracle (capAfterTests state) nextPC),
    rfl,rfl,post.1,⟨position.context.transport stable (fun _ _ _ => congrFun mem _), ?_, ?_, position.above⟩,mem⟩
  · rw [post.2.1, heap, BitVec.ofNat_add]
  · exact (cap_right_register _ .x21 (by decide)).trans ((cap_tests_cursor state).trans position.proof)

structure CapParentResult (oracle : Oracle) (groups : List Nat) (before : MachineState) (node pointer : Nat) where
  state : MachineState
  segment : Segment oracle before state
  steps : segment.steps = 11
  row : segment.rows =
    [.compression (capRootAt before (2*node+1) ++ capRootAt before (2*node)) (capRootAt state node)]
  pc : state.pc = 0x12e4
  position : CapPosition groups state node pointer
  stable : CapStable before state
  frame : ∀ word < 2^61, (word < 2048+4*node ∨ 2048+4*node+4 ≤ word) →
    memoryView state word = memoryView before word
  digest : capRootAt state node =
    oracle.compression (capRootAt before (2*node+1) ++ capRootAt before (2*node))

attribute [local irreducible] capAfterTests capHashReply capRootAt

noncomputable def cap_return_parent {groups : List Nat} {state : MachineState} {node pointer : Nat}
    (oracle : Oracle) (position : CapPosition groups state (2*node+1) pointer)
    (pc : state.pc = 0x12e4) (nodeBound : 0 < node ∧ 2*node+1 < 512) :
    CapParentResult oracle groups state node pointer := by
  let beforeCall := capAfterTests state
  obtain ⟨target, heap⟩ := cap_after_tests state (2*node+1) (by omega) pc position.heap
  have hashPC : beforeCall.pc = 0x12f4 := by rw [target, ite_eq_right (by omega)]
  have stableTests := cap_tests_stable state
  have mem := cap_tests_memory state
  have ctx := position.context.transport stableTests (fun _ _ _ => congrFun mem _)
  let ready : CapHashReady beforeCall (2*node+1) :=
    ⟨hashPC, heap, ctx.controls.roots, ctx.controls.selector, ctx.controls.size, ctx.controls.primitive, nodeBound.2⟩
  let parent := (2*node+1)/2
  let pair := capRootAt beforeCall (2*parent+1) ++ capRootAt beforeCall (2*parent)
  let answer := oracle.compression pair
  let next := capHashReply beforeCall parent answer
  have half : (2*node+1)/2 = node := by omega
  let hashSegment : Segment oracle beforeCall next := capHashSegment oracle ready
  let tested := capTestsSegment oracle state (2*node+1) (by omega) pc position.heap
  have hashed : capRootAt next node = answer := (congrArg (capRootAt next) half).symm.trans (cap_hash_digest beforeCall parent answer)
  have bytes (i : Nat) : capRootAt beforeCall i = capRootAt state i := by
    unfold capRootAt
    exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun mem _)
  have afterStable : CapStable beforeCall next := cap_hash_stable _ _ _
  have stable := stableTests.trans afterStable
  have frame (word : Nat) (bound : word < 2^61) (outside : word < 2048+4*node ∨ 2048+4*node+4 ≤ word) :
      memoryView next word = memoryView state word := by
    have kept := cap_hash_frame ready answer word bound (by simpa only [half] using outside)
    exact kept.trans (congrFun mem _)
  have finalPC : next.pc = 0x12e4 := by unfold next capHashReply; rfl
  refine ⟨next, tested.append hashSegment, ?_, ?_, finalPC, ?_, stable, frame, ?_⟩
  · rfl
  · change (tested.append hashSegment).rows = _
    have exactRows : hashSegment.rows = [.compression pair answer] := by
      dsimp [hashSegment, capHashSegment, Segment.query]
    rw [show (tested.append hashSegment).rows = hashSegment.rows from rfl, exactRows, ← hashed]
    have parentEq : parent = node := half
    simp only [pair, parentEq, bytes]
  · refine ⟨position.context.transport stable (fun word _ bound => frame word (by omega) (Or.inl (by omega))),
      ?_, ?_, position.above⟩
    · exact (cap_hash_heap ready answer).trans (congrArg (BitVec.ofNat 64) half)
    · exact (cap_hash_register beforeCall parent answer .x21 (by decide) (by decide) (by decide)).trans
        ((cap_tests_cursor state).trans position.proof)
  · have parentEq : parent = node := half
    exact hashed.trans (by simp only [answer, pair, parentEq, bytes]; rfl)

end TwoPermutationPrototype.Checker
