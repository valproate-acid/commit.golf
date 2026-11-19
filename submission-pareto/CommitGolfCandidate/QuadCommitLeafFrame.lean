import CommitGolfCandidate.QuadCommitLeafExec
import CommitGolfCandidate.QuadCommitLeafMemory

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves

theorem after_a_control (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc=leafPC slot 0) (a : BitVec 1600) :
    let prev := repliedA s slot start a
    prev.getReg .x5=0 ∧ prev.getReg .x11=200 ∧ prev.getReg .x13=1 ∧
      prev.getReg .x20=s.getReg .x20 ∧ prev.pc=leafPC slot 2 := by
  refine ⟨(after_a_reg _ _ _ _ _ (by decide) (by decide)).trans ready.selector,
    (after_a_reg _ _ _ _ _ (by decide) (by decide)).trans ready.size,
    (after_a_reg _ _ _ _ _ (by decide) (by decide)).trans ready.primitive,
    after_a_reg _ _ _ _ _ (by decide) (by decide),?_⟩
  change (preparedA s slot).pc+4=_
  rw [(first_execution _ _).2.2.2,pc,BitVec.add_assoc]
  exact leaf_pc_add slot 0 2

theorem finished_reg_frame (s : MachineState) (slot : Fin 4096) (start dst : Nat) (a b : BitVec 1600)
    (r : Reg) (k : r≠.x10) (l : r≠.x12) (p : r≠.x31) :
    (finishedLeaf s slot start dst a b).getReg r=s.getReg r := by
  simp only [finishedLeaf,execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm k),
    repliedB,CommitGolfCandidate.writeBits_register,preparedB,second_keeps _ _ _ k l p,after_a_reg _ _ _ _ _ k l]

end TwoPermutationPrototype.Quad.Commit.Leaves
