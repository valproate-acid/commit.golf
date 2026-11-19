import CommitGolfCandidate.TwoPermutationCheckerCapFrame
import CommitGolfCandidate.TwoPermutationCheckerSegment

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- The cap never changes any of these ABI registers. The heap node and proof
cursor have separate geometry because both move during the traversal. -/
def capFixedRegisters : List Reg := [.x5,.x9,.x11,.x13,.x22,.x25,.x26,.x27]

def CapStable (before after : MachineState) : Prop :=
  ∀ reg ∈ capFixedRegisters, after.getReg reg = before.getReg reg

theorem CapStable.trans {a b c : MachineState} (ab : CapStable a b) (bc : CapStable b c) :
    CapStable a c := fun reg found => (bc reg found).trans (ab reg found)

structure CapControls (state : MachineState) : Prop where
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 64
  primitive : state.getReg .x13 = 0
  roots : state.getReg .x25 = 16384#64
  markBase : state.getReg .x26 = 4096#64
  capLeaves : state.getReg .x27 = 256#64

theorem CapControls.transport {before after : MachineState} (controls : CapControls before)
    (stable : CapStable before after) : CapControls after :=
  ⟨(stable _ (by decide)).trans controls.selector,
   (stable _ (by decide)).trans controls.size,
   (stable _ (by decide)).trans controls.primitive,
   (stable _ (by decide)).trans controls.roots,
   (stable _ (by decide)).trans controls.markBase,
   (stable _ (by decide)).trans controls.capLeaves⟩

theorem cap_lookup_stable (state : MachineState) : CapStable state (capLookup state) := by
  intro r found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact cap_lookup_register _ _ (by decide) (by decide) (by decide)

theorem cap_frontier_stable (state : MachineState) : CapStable state (frontierRead state) := by
  intro r found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact frontier_register _ _ (by decide) (by decide) (by decide) (by decide)

theorem cap_hash_stable (state : MachineState) (parent : Nat) (reply : BitVec 256) :
    CapStable state (capHashReply state parent reply) := by
  intro r found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact cap_hash_register _ _ _ _ (by decide) (by decide) (by decide)

theorem cap_lookup_observation (state : MachineState) (node : Nat)
    (controls : CapControls state) (heap : state.getReg .x6 = BitVec.ofNat 64 node) :
    capMarkedWord state = memoryView state (512+node) := by
  rw [capMarkedWord, cap_lookup_mark_address state node heap controls.markBase]
  rfl

def capLookupSegment (oracle : Oracle) (state : MachineState) (node : Nat)
    (controls : CapControls state) (heap : state.getReg .x6 = BitVec.ofNat 64 node)
    (pc : state.pc = 0x1294) (bounded : node < 512) : Segment oracle state (capLookup state) :=
  Segment.ordinary oracle _ _ fun fuel =>
    execute_cap_lookup state pc fuel (by
      rw [cap_lookup_mark_address state node heap controls.markBase]
      exact aligned_access _ (by omega))

theorem cap_lookup_limit (state : MachineState) : capLookupSteps state ≤ 7 := by
  unfold capLookupSteps
  split
  · decide
  · split <;> decide

theorem cap_lookup_leaf_iff (state : MachineState) (node : Nat) (bounded : node < 512)
    (controls : CapControls state) (heap : state.getReg .x6 = BitVec.ofNat 64 node) :
    (state.getReg .x27 ≤ state.getReg .x6) ↔ 256 ≤ node := by
  rw [controls.capLeaves, heap]
  change 256 ≤ (BitVec.ofNat 64 node).toNat ↔ 256 ≤ node
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem cap_lookup_left_word (state : MachineState) (node : Nat)
    (heap : state.getReg .x6 = BitVec.ofNat 64 node) :
    state.getReg .x6 <<< 1 = BitVec.ofNat 64 (2*node) := by
  rw [heap, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 node * BitVec.ofNat 64 2 = _
  rw [← BitVec.ofNat_mul, Nat.mul_comm node]

def capFrontierSegment (oracle : Oracle) {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) (fits : ¬ state.getReg .x22 < state.getReg .x21+32#64) :
    Segment oracle state (frontierRead state) :=
  Segment.ordinary oracle _ _ fun fuel => execute_frontier_read ready fuel fits

theorem cap_short_frontier_reject (state : MachineState) (pc : state.pc = 0x12b0)
    (short : state.getReg .x22 < state.getReg .x21+32#64) :
    (frontierPrefix state 4).pc = 0x1368 := by
  rw [(frontier_prefix_post state pc).1, ite_eq_left short]

def capHashSegment (oracle : Oracle) {state : MachineState} {node : Nat}
    (ready : CapHashReady state node) :
    let parent := node/2
    let pair := capRootAt state (2*parent+1) ++ capRootAt state (2*parent)
    Segment oracle state (capHashReply state parent (oracle.compression pair)) :=
  Segment.query oracle 7 14 (capHashQuery state (node/2)) _
    (execute_cap_hash ready) (cap_hash_rows oracle state (node/2))

attribute [local simp] MachineState.getReg_setPC Opening.getReg_setReg

theorem root_test_register (state : MachineState) (r : Reg) (stable : r ≠ .x7) :
    (capRootTest state).getReg r = state.getReg r := by
  by_cases atRoot : state.getReg .x6 = 1#64 <;>
    simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12,
      show state.getReg .x0 = 0#64 from rfl, atRoot, Ne.symm stable]

private theorem parity_test_register (state : MachineState) (r : Reg) (stable : r ≠ .x7) :
    (capParityTest state).getReg r = state.getReg r := by
  by_cases even : state.getReg .x6 &&& 1#64 = 0#64 <;>
    simp [capParityTest, blockPrefix, capParityTestCode, execInstrBr, signExtend12,
      show state.getReg .x0 = 0#64 from rfl, even, Ne.symm stable]

private theorem odd_word_eq {node : Nat} (bound : node < 2^64) :
    (BitVec.ofNat 64 node &&& 1#64 = 0#64) ↔ node%2 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  change (node &&& 1 = 0) ↔ _
  rw [Nat.and_one_is_mod]

def capAfterTests (state : MachineState) : MachineState := capParityTest (capRootTest state)

theorem cap_after_tests (state : MachineState) (node : Nat) (bound : 2 ≤ node ∧ node < 512)
    (pc : state.pc = 0x12e4) (heap : state.getReg .x6 = BitVec.ofNat 64 node) :
    let next := capAfterTests state
    next.pc = (if node%2 = 0 then 0x1310 else 0x12f4) ∧ next.getReg .x6 = BitVec.ofNat 64 node := by
  have nRoot : state.getReg .x6 ≠ 1#64 := by
    intro h
    have equal := congrArg BitVec.toNat (heap.symm.trans h)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at equal
    change node = 1 at equal
    omega
  have start : (capRootTest state).pc = 0x12ec := by rw [cap_root_post state pc, ite_eq_right nRoot]
  have before : (capRootTest state).getReg .x6 = BitVec.ofNat 64 node :=
    (root_test_register state .x6 (by decide)).trans heap
  refine ⟨?_, (parity_test_register _ .x6 (by decide)).trans before⟩
  unfold capAfterTests
  rw [cap_parity_post _ start, before]
  simp only [odd_word_eq (by omega : node < 2^64)]

def capTestsSegment (oracle : Oracle) (state : MachineState) (node : Nat)
    (bound : 2 ≤ node ∧ node < 512) (pc : state.pc = 0x12e4)
    (heap : state.getReg .x6 = BitVec.ofNat 64 node) : Segment oracle state (capAfterTests state) := by
  have nRoot : state.getReg .x6 ≠ 1#64 := by
    intro h
    have equal := congrArg BitVec.toNat (heap.symm.trans h)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at equal
    change node = 1 at equal
    omega
  have mid : (capRootTest state).pc = 0x12ec := by rw [cap_root_post state pc, ite_eq_right nRoot]
  exact (Segment.ordinary oracle 2 2 (execute_cap_root_test state pc)).append
    (Segment.ordinary oracle 2 2 (execute_cap_parity_test _ mid))

theorem cap_tests_stable (state : MachineState) : CapStable state (capAfterTests state) := by
  intro r found
  have h : r ≠ .x7 := by
    intro equal
    subst r
    simp [capFixedRegisters] at found
  exact (parity_test_register _ r h).trans (root_test_register state r h)

theorem cap_tests_cursor (state : MachineState) :
    (capAfterTests state).getReg .x21 = state.getReg .x21 :=
  (parity_test_register _ _ (by decide)).trans (root_test_register _ _ (by decide))

theorem cap_tests_memory (state : MachineState) : (capAfterTests state).mem = state.mem := by
  have root (current : MachineState) : (capRootTest current).mem = current.mem := by
    by_cases atRoot : current.getReg .x6 = 1#64 <;>
      simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12,
        show current.getReg .x0 = 0#64 from rfl, atRoot] <;> rfl
  have parity (current : MachineState) : (capParityTest current).mem = current.mem := by
    by_cases even : current.getReg .x6 &&& 1#64 = 0#64 <;>
      simp [capParityTest, blockPrefix, capParityTestCode, execInstrBr, signExtend12,
        show current.getReg .x0 = 0#64 from rfl, even] <;> rfl
  exact (parity _).trans (root _)

def capRightSegment (oracle : Oracle) (state : MachineState) (pc : state.pc = 0x1310) :
    Segment oracle state (capRight state) :=
  Segment.ordinary oracle 2 2 (execute_cap_right state pc)

theorem cap_right_register (state : MachineState) (r : Reg) (node : r ≠ .x6) :
    (capRight state).getReg r = state.getReg r := by
  simp [capRight, blockPrefix, capRightCode, execInstrBr, Ne.symm node]

theorem cap_right_stable (state : MachineState) : CapStable state (capRight state) := by
  intro r found
  apply cap_right_register
  rintro rfl
  simp [capFixedRegisters] at found

theorem cap_hash_heap {state : MachineState} {node : Nat} (ready : CapHashReady state node)
    (answer : BitVec 256) :
    (capHashReply state (node/2) answer).getReg .x6 = BitVec.ofNat 64 (node/2) := by
  rw [capHashReply, MachineState.getReg_setPC, writeBits_register, (cap_parent_post state ready.pc).2.1, ready.nodeReg]
  have bound := ready.bound
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : node < 2^64), Nat.mod_eq_of_lt (by omega : node/2 < 2^64),
    Nat.shiftRight_eq_div_pow]

end TwoPermutationPrototype.Checker
