import CommitGolfCandidate.TwoPermutationOpeningCapFlow

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem moves_pc_set (state : MachineState) (pc : Word) :
    (state.setPC pc).pc = pc := rfl

@[local simp] private theorem moves_reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

private theorem mem_setReg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by cases reg <;> rfl

attribute [local simp] mem_setReg

def RunsOpeningBlock (before after : MachineState) (cycles : Nat) : Prop :=
  ∀ fuel allowCoins, execute openingImage (cycles + fuel) before allowCoins =
    (do let result ← execute openingImage fuel after allowCoins
        return result.charge cycles 0)

attribute [local irreducible] execute

theorem RunsOpeningBlock.next {first middle last : MachineState} {a b : Nat}
    (head : RunsOpeningBlock first middle a) (tail : RunsOpeningBlock middle last b) :
    RunsOpeningBlock first last (a + b) := by
  intro fuel coins
  rw [Nat.add_assoc, head (b+fuel) coins, tail fuel coins]
  simp [Execution.charge, ← Nat.add_assoc]

structure CapPosition (groups : List Nat) (state : MachineState) (node dest : Nat) : Prop where
  context : CapContext groups state
  nodeWord : state.getReg .x6 = BitVec.ofNat 64 node
  destWord : state.getReg .x21 = BitVec.ofNat 64 dest

private theorem context_memory {groups : List Nat} {before after : MachineState}
    (context : CapContext groups before)
    (register : ∀ r, r ∈ ([.x25,.x26,.x27,.x20] : List Reg) → after.getReg r = before.getReg r)
    (memory : after.mem = before.mem) : CapContext groups after :=
  context.of_preserved register (fun n _ _ => congrFun memory (BitVec.ofNat 64 (markBase+8*n)))

/-- A marked leaf emits no bytes and goes straight to its own advance label. -/
theorem cap_prune_step (groups : List Nat) (state : MachineState) (node dest : Nat)
    (position : CapPosition groups state node dest) (span : CapSpan node 0)
    (pc : state.pc = 0x10f0) :
    RunsOpeningBlock state (cursorKnownPrefix state 1) 1 ∧
    (cursorKnownPrefix state 1).pc = 0x1128 ∧
    CapPosition groups (cursorKnownPrefix state 1) node dest ∧
    (cursorKnownPrefix state 1).mem = state.mem := by
  have leaf := cap_span_is_leaf node span
  have bounded := (cap_span_node node 0 span).2
  have comparison : BitVec.ult (state.getReg .x6) (state.getReg .x27) = false := by
    rw [position.nodeWord, position.context.capLeavesWord, BitVec.ult_eq_decide]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : node < 2 ^ 64)]
    simp [show ¬ node < 256 by omega]
  have next := cursor_prune_post state pc comparison
  refine ⟨fun fuel coins => execute_cursor_prune _ pc fuel coins, ?_⟩
  rw [next]
  exact ⟨rfl, ⟨context_memory position.context (fun _ _ => rfl) rfl,
    position.nodeWord, position.destWord⟩, rfl⟩

/-- A marked internal node descends to the left child with no output. -/
theorem cap_descend_step (groups : List Nat) (state : MachineState) (node height dest : Nat)
    (position : CapPosition groups state node dest) (span : CapSpan node (height + 1))
    (pc : state.pc = 0x10f0) :
    RunsOpeningBlock state (cursorKnownPrefix state 3) 3 ∧
    (cursorKnownPrefix state 3).pc = 0x10e0 ∧
    CapPosition groups (cursorKnownPrefix state 3) (2 * node) dest ∧
    (cursorKnownPrefix state 3).mem = state.mem := by
  have internal := cap_span_is_internal node height span
  have comparison : BitVec.ult (state.getReg .x6) (state.getReg .x27) = true := by
    rw [position.nodeWord, position.context.capLeavesWord, BitVec.ult_eq_decide]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : node < 2 ^ 64)]
    simp [internal]
  have ⟨target, nodeAfter, destAfter, memAfter⟩ := cursor_descend_post state pc comparison
  refine ⟨fun fuel coins => execute_cursor_descend _ pc fuel coins comparison, target, ⟨?_, ?_, ?_⟩, memAfter⟩
  · apply context_memory position.context _ memAfter
    intro r member
    have notNode : r ≠ .x6 := by intro same; subst r; simp at member
    simp [cursorKnownPrefix, capWalkInstructions, execInstrBr, comparison, Ne.symm notNode]
  · rw [nodeAfter, position.nodeWord, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 node * BitVec.ofNat 64 2 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm node]
  · exact destAfter.trans position.destWord

private theorem root_check_mem (state : MachineState) :
    (advancePrefix state 19 2).mem = state.mem := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, root]
  all_goals rfl

private theorem root_check_reg (state : MachineState) (reg : Reg) (distinct : reg ≠ .x7) :
    (advancePrefix state 19 2).getReg reg = state.getReg reg := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, root, Ne.symm distinct]

private theorem parity_check_mem (state : MachineState) :
    (advancePrefix state 21 2).mem = state.mem := by
  by_cases even : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, even]
  all_goals rfl

private theorem parity_check_reg (state : MachineState) (reg : Reg) (distinct : reg ≠ .x7) :
    (advancePrefix state 21 2).getReg reg = state.getReg reg := by
  by_cases even : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [advancePrefix, capWalkInstructions, execInstrBr, signExtend12, even, Ne.symm distinct]

def afterAdvanceChecks (state : MachineState) : MachineState :=
  advancePrefix (advancePrefix state 19 2) 21 2

theorem advance_checks (groups : List Nat) (state : MachineState) (node dest : Nat)
    (position : CapPosition groups state node dest) (nonroot : 1 < node) (bounded : node < 512)
    (pc : state.pc = 0x1128) :
    RunsOpeningBlock state (afterAdvanceChecks state) 4 ∧
    (afterAdvanceChecks state).pc = (if node % 2 = 0 then 0x1140 else 0x1138) ∧
    CapPosition groups (afterAdvanceChecks state) node dest ∧
    (afterAdvanceChecks state).mem = state.mem := by
  let tested := advancePrefix state 19 2
  have notRoot : state.getReg .x6 ≠ 1#64 := by
    rw [position.nodeWord]
    intro equal
    have root := nat_address_injective (left := node) (right := 1) (by omega) (by decide) equal
    omega
  have parityPC : tested.pc = 0x1130 := by rw [advance_root_target state pc, ite_eq_right notRoot]
  have memory : (afterAdvanceChecks state).mem = state.mem :=
    (parity_check_mem tested).trans (root_check_mem state)
  have saved (reg : Reg) (different : reg ≠ .x7) :
      (afterAdvanceChecks state).getReg reg = state.getReg reg :=
    (parity_check_reg tested reg different).trans (root_check_reg state reg different)
  have testedNode := (root_check_reg state .x6 (by decide)).trans position.nodeWord
  refine ⟨RunsOpeningBlock.next (fun fuel coins => execute_advance_root_test state pc fuel coins)
    (fun fuel coins => execute_advance_parity_test tested parityPC fuel coins), ?_,
    ⟨?_, (saved .x6 (by decide)).trans position.nodeWord, (saved .x21 (by decide)).trans position.destWord⟩,
    memory⟩
  · unfold afterAdvanceChecks
    rw [advance_parity_target tested parityPC, testedNode]
    have lowBits : (BitVec.ofNat 64 node &&& 1#64) = BitVec.ofNat 64 (node % 2) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : node < 2 ^ 64)]
      have small : node % 2 < 2 ^ 64 := by omega
      rw [Nat.mod_eq_of_lt small]
      exact Nat.and_two_pow_sub_one_eq_mod _ 1
    rw [lowBits]
    have zero : BitVec.ofNat 64 (node % 2) = 0#64 ↔ node % 2 = 0 := by
      constructor
      · exact nat_address_injective (left := node%2) (right := 0) (by omega) (by decide)
      · intro h
        rw [h]
    simp only [zero]
  · apply context_memory position.context _ memory
    intro r member
    have different : r ≠ .x7 := by intro same; subst r; simp at member
    exact saved r different

def advanceRight (state : MachineState) : MachineState :=
  advancePrefix (afterAdvanceChecks state) 25 2

def advanceUp (state : MachineState) : MachineState :=
  advancePrefix (afterAdvanceChecks state) 23 2

theorem advance_left_to_right (groups : List Nat) (state : MachineState) (parent dest : Nat)
    (positive : 0 < parent) (bounded : 2 * parent < 512)
    (position : CapPosition groups state (2 * parent) dest) (pc : state.pc = 0x1128) :
    RunsOpeningBlock state (advanceRight state) 6 ∧
    (advanceRight state).pc = 0x10e0 ∧
    CapPosition groups (advanceRight state) (2 * parent + 1) dest ∧
    (advanceRight state).mem = state.mem := by
  have ⟨checks, target, pos, memory⟩ :=
    advance_checks groups state (2*parent) dest position (by omega) bounded pc
  have right : (afterAdvanceChecks state).pc = 0x1140 := by simpa [show (2*parent) % 2 = 0 by omega] using target
  have ⟨nextPC, nextNode, nextDest, nextMem⟩ := advance_right_post _ right
  refine ⟨checks.next (fun fuel coins => execute_advance_right _ right fuel coins), nextPC,
    ⟨?_, ?_, nextDest.trans pos.destWord⟩, nextMem.trans memory⟩
  · apply context_memory pos.context _ nextMem
    intro reg member
    have different : reg ≠ .x6 := by intro same; subst reg; simp at member
    simp [advanceRight, advancePrefix, capWalkInstructions, execInstrBr, Ne.symm different]
  · rw [advanceRight, nextNode, pos.nodeWord]
    exact (BitVec.ofNat_add (n := 64) (2*parent) 1).symm

theorem advance_right_to_parent (groups : List Nat) (state : MachineState) (parent dest : Nat)
    (positive : 0 < parent) (bounded : 2 * parent + 1 < 512)
    (position : CapPosition groups state (2 * parent + 1) dest) (pc : state.pc = 0x1128) :
    RunsOpeningBlock state (advanceUp state) 6 ∧
    (advanceUp state).pc = 0x1128 ∧
    CapPosition groups (advanceUp state) parent dest ∧
    (advanceUp state).mem = state.mem := by
  have ⟨checks, target, pos, memory⟩ :=
    advance_checks groups state (2*parent+1) dest position (by omega) bounded pc
  have up : (afterAdvanceChecks state).pc = 0x1138 := by
    simpa [show (2 * parent + 1) % 2 ≠ 0 by omega] using target
  have ⟨nextPC, nextNode, nextDest, nextMem⟩ := advance_up_post _ up
  refine ⟨checks.next (fun fuel coins => execute_advance_up _ up fuel coins), nextPC,
    ⟨?_, ?_, nextDest.trans pos.destWord⟩, nextMem.trans memory⟩
  · apply context_memory pos.context _ nextMem
    intro reg member
    have different : reg ≠ .x6 := by intro same; subst reg; simp at member
    simp [advanceUp, advancePrefix, capWalkInstructions, execInstrBr, Ne.symm different]
  · rw [advanceUp, nextNode, pos.nodeWord]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : 2*parent+1 < 2^64), Nat.mod_eq_of_lt (by omega : parent < 2^64)]
    omega

end TwoPermutationPrototype.Opening
