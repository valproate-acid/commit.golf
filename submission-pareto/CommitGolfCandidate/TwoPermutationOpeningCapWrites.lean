import CommitGolfCandidate.TwoPermutationOpeningCapMoves
import CommitGolfCandidate.TwoPermutationOpeningCopyBytes

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling RiscvZkvm.Rv64

attribute [local simp] getReg_setReg getReg_setMem

def capDigestAddress (node : Nat) : Nat := trapdoorBase + 32 * node

/-- A segment appends the listed cap digests and preserves every word outside
that output span, including the marks and the heap. -/
structure CapWrites (before after : MachineState) (dest : Nat) (nodes : List Nat) : Prop where
  frame : ∀ address < 2^64, address < dest ∨ dest + 32 * nodes.length ≤ address →
    after.getMem (BitVec.ofNat 64 address) = before.getMem (BitVec.ofNat 64 address)
  digest : ∀ i (inside : i < nodes.length),
    readBuffer after (dest + 32*i) 32 = readBuffer before (capDigestAddress nodes[i]) 32

theorem cap_writes_empty (before after : MachineState) (dest : Nat) (memory : after.mem = before.mem) :
    CapWrites before after dest [] :=
  ⟨fun address _ _ => congrFun memory (BitVec.ofNat 64 address), fun i hi => by simp at hi⟩

private theorem read_buffer_memory (before after : MachineState) (address size : Nat)
    (memory : before.mem = after.mem) :
    readBuffer before address size = readBuffer after address size := by
  simp only [readBuffer, MachineState.getByte, MachineState.getMem, memory]

theorem cap_digest_bounds (node : Nat) (bounded : node < 512) :
    capDigestAddress node % 8 = 0 ∧ capDigestAddress node + 32 ≤ proofBase := by
  norm_num [capDigestAddress, trapdoorBase, proofBase, indicesBase, trapdoorBytes, LENGTH, LOG_LENGTH]
  omega

private theorem emitted_source (state : MachineState) (node : Nat)
    (heap : state.getReg .x25 = BitVec.ofNat 64 trapdoorBase)
    (cursor : state.getReg .x6 = BitVec.ofNat 64 node) :
    capSource state = BitVec.ofNat 64 (capDigestAddress node) := by
  rw [capSource, heap, cursor, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 trapdoorBase + BitVec.ofNat 64 node * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm node]
  rfl

private theorem emitted_register (state : MachineState) (r : Reg)
    (temp : r ≠ .x7) (dest : r ≠ .x21) (scratch : r ≠ .x31) :
    (capEmitPrefix state 11).getReg r = state.getReg r := by
  simp [capEmitPrefix, capWalkInstructions, execInstrBr, Ne.symm temp, Ne.symm dest, Ne.symm scratch]

private theorem observed_copy_outside (before after : MachineState) (source dest address : Word)
    (memory : after.mem = (fourWordStore before source dest).mem)
    (outside : ∀ i : Fin 4, address ≠ dest + BitVec.ofNat 64 (8 * i.val)) :
    after.getMem address = before.getMem address := by
  have copied : after.getMem address = (fourWordStore before source dest).getMem address :=
    congrFun memory address
  exact copied.trans (four_word_store_outside before source dest address outside)

attribute [local irreducible] capEmitPrefix

theorem cap_emit_step (groups : List Nat) (state : MachineState) (node dest : Nat)
    (bounded : node < 512) (position : CapPosition groups state node dest)
    (pc : state.pc = 0x10fc) (separate : proofBase ≤ dest)
    (aligned : dest % 8 = 0) (fits : dest + 32 ≤ MEMORY_BYTES) :
    RunsOpeningBlock state (capEmitPrefix state 11) 11 ∧
    (capEmitPrefix state 11).pc = 0x1128 ∧
    CapPosition groups (capEmitPrefix state 11) node (dest + 32) ∧
    CapWrites state (capEmitPrefix state 11) dest [node] := by
  let source := capDigestAddress node
  have ⟨srcAligned, srcBefore⟩ := cap_digest_bounds node bounded
  have sourceFits : source + 32 ≤ dest := srcBefore.trans separate
  have pointer := emitted_source state node position.context.heap position.nodeWord
  have checks (i j : Fin 4) : capSource state + BitVec.ofNat 64 (8 * i.val) ≠
      state.getReg .x21 + BitVec.ofNat 64 (8 * j.val) := by
    rw [pointer, position.destWord]
    exact separated_words source dest 4 sourceFits fits i j
  have memory := cap_emit_memory state checks
  rw [pointer, position.destWord] at memory
  have stable (address : Nat) (fit : address < 2^64) (outside : address < dest ∨ dest + 32 ≤ address) :
      (capEmitPrefix state 11).getMem (BitVec.ofNat 64 address) =
        state.getMem (BitVec.ofNat 64 address) := by
    have disjoint (j : Fin 4) : BitVec.ofNat 64 address ≠
        BitVec.ofNat 64 dest + BitVec.ofNat 64 (8*j.val) := by
      rw [word_at]
      intro equal
      have within := j.isLt
      unfold MEMORY_BYTES at fits
      have natural := nat_address_injective fit (by omega) equal
      rcases outside with before | after <;> omega
    exact observed_copy_outside state _ (BitVec.ofNat 64 source) (BitVec.ofNat 64 dest) _ memory disjoint
  have ⟨nextPC, nextNode, nextDest⟩ := cap_emit_post state pc
  refine ⟨?_, nextPC, ⟨?_, nextNode.trans position.nodeWord, ?_⟩, ⟨?_, ?_⟩⟩
  · intro fuel coins
    apply execute_cap_emit _ pc
    · intro i
      rw [pointer, word_at]
      have small := i.isLt
      apply aligned_access _ (by omega) (by omega)
    · intro i
      rw [position.destWord, word_at]
      have small := i.isLt
      apply aligned_access _ (by omega) (by omega)
  · apply position.context.of_preserved
    · intro r member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact emitted_register state _ (by decide) (by decide) (by decide)
    · intro slot _ inside
      have low := marks_before_trapdoor
      have proofAbove : trapdoorBase ≤ proofBase := by decide
      exact stable _ (by unfold markBase; omega) (Or.inl (by omega))
  · rw [nextDest, position.destWord]
    exact (BitVec.ofNat_add (n := 64) dest 32).symm
  · intro address fit outside
    apply stable address fit
    simpa using outside
  · intro i inside
    have zero : i = 0 := by simpa using inside
    subst i
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero]
    exact (read_buffer_memory (capEmitPrefix state 11) _ dest 32 memory).trans
      (four_word_store_bytes state source dest srcAligned aligned fits)

theorem cap_frontier_nodes_small (groups : List Nat) (node height : Nat)
    (span : CapSpan node height) :
    ∀ n ∈ capFrontierNodes groups node height, n < 512 := by
  induction height generalizing node with
  | zero =>
    have bounded := (cap_span_node node 0 span).2
    cases mark : capIsMarked groups node 0 <;> simp [capFrontierNodes, mark, bounded]
  | succ height ih =>
    have ⟨left, right⟩ := cap_span_children node height span
    have bounded := (cap_span_node node (height+1) span).2
    cases mark : capIsMarked groups node (height+1)
    · simp [capFrontierNodes, mark, bounded]
    · intro n member
      simp only [capFrontierNodes, mark, Bool.true_eq, ite_true, List.mem_append] at member
      exact member.elim (ih _ left n) (ih _ right n)

theorem CapWrites.join {before midway after : MachineState} {dest : Nat} {left right : List Nat}
    (first : CapWrites before midway dest left)
    (second : CapWrites midway after (dest + 32 * left.length) right)
    (aligned : dest % 8 = 0) (afterHeap : proofBase ≤ dest)
    (rightBound : ∀ node ∈ right, node < 512)
    (fits : dest + 32 * (left ++ right).length ≤ MEMORY_BYTES) :
    CapWrites before after dest (left ++ right) := by
  have fit64 : dest + 32 * (left ++ right).length < 2^64 := by
    unfold MEMORY_BYTES at fits
    omega
  constructor
  · intro address bounded outside
    simp only [List.length_append, Nat.mul_add] at outside
    exact (second.frame address bounded (outside.imp (by omega) (by omega))).trans
      (first.frame address bounded (outside.imp (by omega) (by omega)))
  · intro i inside
    by_cases isLeft : i < left.length
    · rw [List.getElem_append_left isLeft]
      have stable : readBuffer after (dest + 32*i) 32 = readBuffer midway (dest + 32*i) 32 := by
        apply copied_buffer _ _ _ _ 4 (by omega) (by omega) (by decide)
        intro j hj
        simp only [List.length_append, Nat.mul_add] at fit64
        exact second.frame _ (by omega) (Or.inl (by omega))
      exact stable.trans (first.digest i isLeft)
    · have isRight : i - left.length < right.length := by
        simp only [List.length_append] at inside
        omega
      rw [List.getElem_append_right (by omega)]
      have coordinates : dest + 32*i = dest + 32*left.length + 32*(i - left.length) := by omega
      rw [coordinates, second.digest (i-left.length) isRight]
      let node := right[i-left.length]
      have bounded : node < 512 := rightBound _ (List.getElem_mem _)
      have ⟨srcAligned, srcBefore⟩ := cap_digest_bounds node bounded
      apply copied_buffer _ _ _ _ 4 srcAligned srcAligned (by decide)
      intro j hj
      exact first.frame _ (by omega) (Or.inl (by omega))

end TwoPermutationPrototype.Opening
