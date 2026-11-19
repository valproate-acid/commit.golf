import CommitGolfCandidate.TwoPermutationPackedGroupCode
import CommitGolfCandidate.TwoPermutationGroupGeometry
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

structure GroupReady (node remaining : Nat) (s : MachineState) : Prop where
  pc : s.pc=0x13c0
  nodeReg : s.getReg .x6=BitVec.ofNat 64 node
  low : 256≤node
  high : node<512
  scratch : s.getReg .x23=12288
  rootBase : s.getReg .x25=16384
  markBase : s.getReg .x26=4096
  counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)
  small : remaining<2^64

private theorem shift3 (n : Nat) : (BitVec.ofNat 64 n <<< 3)=BitVec.ofNat 64 (8*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n*BitVec.ofNat 64 8=_
  rw [← BitVec.ofNat_mul,Nat.mul_comm]
private theorem shift5 (n : Nat) : (BitVec.ofNat 64 n <<< 5)=BitVec.ofNat 64 (32*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n*BitVec.ofNat 64 32=_
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

theorem GroupReady.mark {n r : Nat} {s : MachineState} (h : GroupReady n r s) :
    groupMarkAddress s=wordAddress (512+n) := by
  rw [groupMarkAddress,h.markBase,h.nodeReg,shift3]
  change BitVec.ofNat 64 4096+BitVec.ofNat 64 (8*n)=BitVec.ofNat 64 (8*(512+n))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem GroupReady.root {n r : Nat} {s : MachineState} (h : GroupReady n r s) :
    groupRootAddress s=wordAddress (2048+4*n) := by
  rw [groupRootAddress,h.rootBase,h.nodeReg,shift5]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 (32*n)=BitVec.ofNat 64 (8*(2048+4*n))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

end TwoPermutationPrototype.Packed.Checker
