import CommitGolfCandidate.TwoPermutationPackedImage
import CommitGolfCandidate.ProjectedMask

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp OracleSpec ShortTree
set_option maxRecDepth 8192
set_option maxHeartbeats 850000
attribute [local irreducible] execute readBuffer writeBits capCompressionAnswer

theorem parent_hash_step (site : ProjectSite) (s : MachineState) (source target : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*site.start))
    (src : s.getReg .x10=BitVec.ofNat 64 source) (dst : s.getReg .x12=BitVec.ofNat 64 target)
    (mask : s.getReg site.dest=s.getReg .x12)
    (selector : s.getReg .x5=0 ∧ s.getReg .x11=64 ∧ s.getReg .x13=0)
    (srcRoom : source+64≤MEMORY_BYTES) (dstRoom : target+32≤MEMORY_BYTES)
    (srcAlign : source%8=0) (dstAlign : target%8=0) (fuel : Nat) :
    execute packedImage (2+fuel) s false = do
      let answer ← World.query (.inr (.inl (readBuffer s (source+32) 32 ++ readBuffer s source 32)))
      let result ← execute packedImage fuel ((capCompressionAnswer s (padLow answer)).setPC (s.pc+8)) false
      return result.charge 9 1 := by
  have lim : MEMORY_BYTES<2^64 := by decide
  have srcV : rangeValid (s.getReg .x10) 64=true := by
    simp only [src,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),decide_eq_true_eq];exact srcRoom
  have dstV : rangeValid (s.getReg .x12) 32=true := by
    simp only [dst,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target<2^64),decide_eq_true_eq];exact dstRoom
  have asrc : (s.getReg .x10).toNat%8=0 := by simpa [src,Nat.mod_eq_of_lt (by omega : source<2^64)] using srcAlign
  have adst : (s.getReg .x12).toNat%8=0 := by simpa [dst,Nat.mod_eq_of_lt (by omega : target<2^64)] using dstAlign
  have hash := cap_compression_execute packedImage s (project_fetch _ _ pc) selector srcV dstV asrc adst (fuel+1) false
  change execute packedImage (1+(fuel+1)) s false = (do
    let answer ← World.query (.inr (.inl (readBuffer s (s.getReg .x10).toNat 64)))
    let result ← execute packedImage (fuel+1) (capCompressionAnswer s answer) false
    return result.charge 8 1) at hash
  rw [src,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : source<2^64),read_compression_halves s source srcAlign] at hash
  rw [show 2+fuel=1+(fuel+1) by omega,hash]
  congr 1
  funext answer
  change BitVec 256 at answer
  let raw := capCompressionAnswer s answer
  have after : raw.pc=BitVec.ofNat 64 (4096+4*(site.start+1)) := by
    have moved : raw.pc=s.pc+4 := by unfold raw capCompressionAnswer writeBits;rfl
    rw [moved]
    rw [pc,show (4 : Word)=BitVec.ofNat 64 4 by rfl,←BitVec.ofNat_add]
    congr 1
  have reg : raw.getReg site.dest=raw.getReg .x12 := by
    dsimp only [raw]
    rw [cap_compression_register,cap_compression_register,mask]
  have am : accessValid (raw.getReg site.dest + signExtend12 30) 2=true := by
    rw [reg,show raw.getReg .x12=s.getReg .x12 from cap_compression_register _ _ _,dst]
    change accessValid (BitVec.ofNat 64 target + BitVec.ofNat 64 30) 2=true
    rw [←BitVec.ofNat_add]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target+30<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  have masked := masked_reply_step s target answer dst dstAlign (by omega)
  have same : execInstrBr raw (.SH site.dest .x0 30)=execInstrBr raw (.SH .x12 .x0 30) := by
    simp only [execInstrBr,reg]
  have step : ordinaryStep raw (.base (.SH site.dest .x0 30)) =
      some ((capCompressionAnswer s (padLow answer)).setPC (s.pc+8)) := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,am,↓reduceIte]
    exact congrArg some (same.trans masked)
  have actual := execute_ordinary_step packedImage _ raw _ fuel false (project_fetch_mask site raw after) step
  rw [actual]
  simp only [bind_assoc,pure_bind,Execution.charge,instructionCycles,Nat.zero_add,←Nat.add_assoc]

end TwoPermutationPrototype.Packed.Checker
