import CommitGolfCandidate.TwoPermutationPackedCapAdvance
import CommitGolfCandidate.TwoPermutationPackedParent
import CommitGolfCandidate.TwoPermutationCheckerCapHash

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

open TwoPermutationPrototype.Checker (capRootAt compressed_digest)
open CommitGolfCandidate (capCompressionAnswer)
open ShortTree

private theorem cap_node_shift (node : Nat) (bounded : node < 2^64) :
    BitVec.ofNat 64 node >>> 1 = BitVec.ofNat 64 (node/2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt bounded, Nat.mod_eq_of_lt (by omega : node/2 < 2^64), Nat.shiftRight_eq_div_pow]

private theorem cap_address (node : Nat) :
    16384#64 + (BitVec.ofNat 64 node <<< 5) = wordAddress (2048+4*node) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384 + BitVec.ofNat 64 node * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
  congr 1
  omega

theorem execute_cap_parent_jump (state : MachineState) (pc : state.pc = 0x1554) (fuel : Nat) :
    execute packedImage (1+fuel) state false =
      (do let result ← execute packedImage fuel (state.setPC 0x1528) false
          return result.charge 1 0) := by
  have fetched := cap_fetch state 341 (.JAL .x0 2097108) (by decide) pc rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 2097108)) = some (state.setPC 0x1528) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setReg, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

structure CapHashReady (state : MachineState) (node : Nat) where
  pc : state.pc = 0x1538
  nodeReg : state.getReg .x6 = BitVec.ofNat 64 node
  roots : state.getReg .x25 = 16384#64
  selector : state.getReg .x5 = 0
  size : state.getReg .x11 = 64
  primitive : state.getReg .x13 = 0
  bound : node < 512

def capHashReply (state : MachineState) (parent : Nat) (answer : BitVec 256) : MachineState :=
  (writeBits (capParent state) (wordAddress (2048+4*parent)) (padLow answer)).setPC 0x1528

def capHashQuery (state : MachineState) (parent : Nat) : OracleComp World MachineState := do
  let answer ← World.query (.inr (.inl (capRootAt state (2*parent+1) ++ capRootAt state (2*parent))))
  return capHashReply state parent answer

set_option maxRecDepth 4096
attribute [local irreducible] execute readBuffer writeBits

theorem execute_cap_hash {state : MachineState} {node : Nat} (ready : CapHashReady state node) (fuel : Nat) :
    execute packedImage (8+fuel) state false =
      (do let next ← capHashQuery state (node/2)
          let result ← execute packedImage fuel next false
          return result.charge 15 1) := by
  obtain ⟨pc, parent, source, dest, mem⟩ := cap_parent_post state ready.pc
  have room := ready.bound
  have shifted : state.getReg .x6 >>> 1 = BitVec.ofNat 64 (node/2) := by
    rw [ready.nodeReg, cap_node_shift _ (by omega)]
  have src : (capParent state).getReg .x10 = wordAddress (2048+8*(node/2)) := by
    rw [source, ready.roots, shifted, BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (node/2) * BitVec.ofNat 64 64 = _
    rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add, wordAddress]
    congr 1
    omega
  have dst : (capParent state).getReg .x12 = wordAddress (2048+4*(node/2)) := by
    rw [dest, ready.roots, shifted, cap_address]
  let input := 8*(2048+8*(node/2))
  let target := 8*(2048+4*(node/2))
  have control (r : Reg) (n : r ≠ .x6) (a : r ≠ .x10) (b : r ≠ .x12) :
      (capParent state).getReg r = state.getReg r := cap_parent_register state r n a b
  have select : (capParent state).getReg .x5=0 ∧ (capParent state).getReg .x11=64 ∧
      (capParent state).getReg .x13=0 :=
    ⟨(control _ (by decide) (by decide) (by decide)).trans ready.selector,
      (control _ (by decide) (by decide) (by decide)).trans ready.size,
      (control _ (by decide) (by decide) (by decide)).trans ready.primitive⟩
  have memLimit : 32768 ≤ MEMORY_BYTES := by decide
  have call := parent_hash_step .cap (capParent state) input target pc src dst rfl select
    (by dsimp [input]; omega) (by dsimp [target]; omega)
    (by dsimp [input]; omega) (by dsimp [target]; omega) (1+fuel)
  have halves :
      (readBuffer (capParent state) (input+32) 32 ++ readBuffer (capParent state) input 32) =
        capRootAt state (2*(node/2)+1) ++ capRootAt state (2*(node/2)) := by
    unfold capRootAt
    have offset : input+32 = 8*(2048+4*(2*(node/2)+1)) := by unfold input; omega
    have base : input = 8*(2048+4*(2*(node/2))) := by unfold input; omega
    rw [offset, base]
    congr 1 <;> apply read_digest_congr _ _ _ (by omega) <;>
      intro i _ <;> exact congrFun mem _
  rw [show 8+fuel = 5+(2+(1+fuel)) by omega, execute_cap_parent_setup _ ready.pc, call]
  erw [halves]
  simp only [capHashQuery, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  let resumed := (capCompressionAnswer (capParent state) (padLow answer)).setPC ((capParent state).pc+8)
  have resumePC : resumed.pc = 0x1554 := by
    change (capParent state).pc+8#64 = _
    rw [pc]
    rfl
  erw [execute_cap_parent_jump resumed resumePC]
  simp only [Execution.charge, bind_assoc, pure_bind, ← Nat.add_assoc, Nat.reduceAdd, Nat.add_zero]
  have final : resumed.setPC 0x1528 = capHashReply state (node/2) answer := by
    unfold resumed capCompressionAnswer capHashReply
    rw [dst]
    rfl
  rw [final]

theorem cap_hash_digest (state : MachineState) (parent : Nat) (answer : BitVec 256) :
    capRootAt (capHashReply state parent answer) parent = padLow answer := by
  unfold capRootAt capHashReply
  rw [read_digest_congr _ (writeBits (capParent state) (wordAddress (2048+4*parent)) (padLow answer)) _ (by omega)
    (fun _ _ => MachineState.getMem_setPC)]
  exact compressed_digest _ _ (padLow answer)

theorem cap_hash_rows (oracle : Oracle) (state : MachineState) (parent : Nat) :
    let pair := capRootAt state (2*parent+1) ++ capRootAt state (2*parent)
    let reply := oracle.compression pair
    checkEvaluation oracle (recordRows (capHashQuery state parent)) =
      ((capHashReply state parent reply, [.compression pair reply]), 1) := by
  simp only [capHashQuery, record_rows_query, check_evaluation_public_bind, check_evaluation_map,
    record_rows_pure, check_evaluation_pure]
  rfl

end TwoPermutationPrototype.Packed.Checker
