import CommitGolfCandidate.TwoPermutationPackedImage
import CommitGolfCandidate.TwoPermutationCheckerCompression

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

theorem cap_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 512) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch packedImage state = some (.base instruction) :=
by
  have numeric : state.pc.toNat = 4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, ite_eq_left (by omega), show (4096+4*index-4096)/4=index by omega]
  cases entry : packedImage.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

end TwoPermutationPrototype.Packed.Checker
