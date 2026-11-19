import CommitGolfCandidate.TwoPermutationPackedCapVisit
import CommitGolfCandidate.TwoPermutationPackedCapBytes

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt)

structure FrontierReady (state : MachineState) (node proof : Nat) : Prop where
  pc : state.pc = 0x1498
  nodeReg : state.getReg .x6 = BitVec.ofNat 64 node
  capReg : state.getReg .x25 = 16384#64
  proofReg : state.getReg .x21 = BitVec.ofNat 64 proof
  below : node < 512
  above : 32768 ≤ proof
  even : proof%2 = 0
  room : proof+30 ≤ MEMORY_BYTES

/-- The one 36-step packed read, exposed separately from the DFS induction. -/
structure FrontierKernel where
  after : MachineState → MachineState
  run : ∀ (state : MachineState) (node proof : Nat), FrontierReady state node proof →
    ¬ state.getReg .x22 < state.getReg .x21+30#64 →
    ∀ fuel, execute packedImage (36+fuel) state false = do
      let result ← execute packedImage fuel (after state) false
      return result.charge 36 0
  digest : ∀ (state : MachineState) (node proof : Nat), FrontierReady state node proof →
    ¬ state.getReg .x22 < state.getReg .x21+30#64 →
    capRootAt (after state) node = (0#16 ++ readBuffer state proof 30)
  register : ∀ state reg, reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x28 → reg ≠ .x31 →
    (after state).getReg reg = state.getReg reg
  pointer : ∀ (state : MachineState) (node proof : Nat), FrontierReady state node proof →
    (after state).pc = 0x1528 ∧ (after state).getReg .x21 = BitVec.ofNat 64 (proof+30)
  frame : ∀ (state : MachineState) (node proof : Nat), FrontierReady state node proof →
    ¬ state.getReg .x22 < state.getReg .x21+30#64 →
    ∀ word < 2^61, (word < 2048+4*node ∨ 2048+4*node+4 ≤ word) →
      memoryView (after state) word = memoryView state word

theorem cap_frontier_stable (codec : FrontierKernel) (state : MachineState) :
    CapStable state (codec.after state) := by
  intro r found
  simp [capFixedRegisters] at found
  rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact codec.register _ _ (by decide) (by decide) (by decide) (by decide)

def capFrontierSegment (codec : FrontierKernel) (oracle : Oracle) {state : MachineState} {node proof : Nat}
    (ready : FrontierReady state node proof) (fits : ¬ state.getReg .x22 < state.getReg .x21+30#64) :
    Segment oracle state (codec.after state) :=
  Segment.ordinary oracle 36 36 (codec.run state node proof ready fits)

theorem cap_frontier_position (codec : FrontierKernel) {groups : List Nat}
    {state : MachineState} {node pointer : Nat}
    (position : CapPosition groups state node pointer) (ready : FrontierReady state node pointer)
    (fits : ¬ state.getReg .x22 < state.getReg .x21+30#64) :
    CapPosition groups (codec.after state) node (pointer+30) := by
  refine ⟨position.context.transport (cap_frontier_stable codec state) ?_,
    (codec.register state .x6 (by decide) (by decide) (by decide) (by decide)).trans position.heap,
    (codec.pointer state node pointer ready).2, by have := position.above; omega,
    by have := position.even; omega⟩
  intro word low high
  exact codec.frame state node pointer ready fits word (by omega) (Or.inl (by omega))

end TwoPermutationPrototype.Packed.Checker
