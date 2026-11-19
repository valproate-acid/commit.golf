import CommitGolfCandidate.Execution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- Fetch from a bounded word position in an arbitrary image. -/
theorem cap_image_fetch (image : Image) (state : MachineState)
    (index : Nat) (instruction : Instr) (bounded : index < 512)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (image.code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch image state = some (.base instruction) := by
  have numeric : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, numeric, if_pos (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases entry : image.code[index]? with
  | none => simp [entry] at decoded
  | some word => simpa only [entry, Option.bind_some] using decoded

end CommitGolfCandidate
