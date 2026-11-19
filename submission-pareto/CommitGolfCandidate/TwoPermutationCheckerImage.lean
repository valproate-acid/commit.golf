import CommitGolfCandidate.TwoPermutationOpeningImage

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 8192

/-- Default checker image with unpacked 32-byte digests. -/
def checkerImage : Image := ⟨[
  0x00481313, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393,
  0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393,
  0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393,
  0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393, 0x00730333, 0x00581393,
  0x00730333, 0x2e68e263, 0x2c080863, 0x00068413, 0x00058493, 0x00080913, 0xfd870993, 0x01000a37,
  0x00078a93, 0x01178b33, 0x00003bb7, 0x00003c37, 0x100c0c13, 0x00004cb7, 0x00001d37, 0x10000d93,
  0x000011b7, 0xfd818193, 0x00000293, 0x00043303, 0x00831e13, 0x01c18e33, 0x00098513, 0x0c800593,
  0x00100693, 0x01c53023, 0x00053423, 0x00053823, 0x000abf83, 0x01f53c23, 0x008abf83, 0x03f53023,
  0x00050613, 0x00000073, 0x06050513, 0x060e0f93, 0x01f53023, 0x000b8613, 0x00000073, 0x010a8a93,
  0x01430333, 0x04000593, 0x00000693, 0x01000e93, 0x00137393, 0x04038463, 0x000abf83, 0x01fc3023,
  0x008abf83, 0x01fc3423, 0x010abf83, 0x01fc3823, 0x018abf83, 0x01fc3c23, 0x000bbf83, 0x03fc3023,
  0x008bbf83, 0x03fc3423, 0x010bbf83, 0x03fc3823, 0x018bbf83, 0x03fc3c23, 0x0440006f, 0x000bbf83,
  0x01fc3023, 0x008bbf83, 0x01fc3423, 0x010bbf83, 0x01fc3823, 0x018bbf83, 0x01fc3c23, 0x000abf83,
  0x03fc3023, 0x008abf83, 0x03fc3423, 0x010abf83, 0x03fc3823, 0x018abf83, 0x03fc3c23, 0x000c0513,
  0x000b8613, 0x00000073, 0x020a8a93, 0x00135313, 0xfffe8e93, 0xf40e9ee3, 0x00331393, 0x007d03b3,
  0x00531e13, 0x01cc8e33, 0x0003be83, 0x020e8c63, 0x000e3e83, 0x000bbf03, 0x17ee9863, 0x008e3e83,
  0x008bbf03, 0x17ee9263, 0x010e3e83, 0x010bbf03, 0x15ee9c63, 0x018e3e83, 0x018bbf03, 0x15ee9663,
  0x02c0006f, 0x000bbf83, 0x01fe3023, 0x008bbf83, 0x01fe3423, 0x010bbf83, 0x01fe3823, 0x018bbf83,
  0x01fe3c23, 0x00100e93, 0x01d3b023, 0x00840413, 0x10098993, 0xfff90913, 0xe6091ae3, 0x0ff00313,
  0x00431393, 0x007d03b3, 0x0003be03, 0x0083be83, 0x01de6e33, 0x00331393, 0x007d03b3, 0x01c3b023,
  0xfff30313, 0xfc031ee3, 0x04000593, 0x00000693, 0x00100313, 0x00331393, 0x007d03b3, 0x0003be03,
  0x000e0863, 0x05b37063, 0x00131313, 0xfe9ff06f, 0x00531393, 0x007c83b3, 0x020a8e13, 0x0bcb6663,
  0x000abf83, 0x01f3b023, 0x008abf83, 0x01f3b423, 0x010abf83, 0x01f3b823, 0x018abf83, 0x01f3bc23,
  0x020a8a93, 0x00100393, 0x02730863, 0x00137393, 0x02038063, 0x00135313, 0x00631513, 0x00ac8533,
  0x00531613, 0x00cc8633, 0x00000073, 0xfd9ff06f, 0x00130313, 0xf81ff06f, 0x056a9863, 0x020cbe83,
  0x0004bf03, 0x05ee9263, 0x028cbe83, 0x0084bf03, 0x03ee9c63, 0x030cbe83, 0x0104bf03, 0x03ee9663,
  0x038cbe83, 0x0184bf03, 0x03ee9063, 0x00100293, 0x00000513, 0x00000073, 0x00089863, 0x00100293,
  0x00000513, 0x00000073, 0x00100293, 0x00100513, 0x00000073], []⟩

def checkerInstructions : List Instr := [
  -- length, words 0–32
  .SLLI .x6 .x16 4, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5, .ADD .x6 .x6 .x7, .SLLI .x7 .x16 5,
  .ADD .x6 .x6 .x7,
  -- entry, words 33–34
  .BLTU .x17 .x6 740, .BEQ .x16 .x0 720,
  -- setup, words 35–50
  .ADDI .x8 .x13 0, .ADDI .x9 .x11 0, .ADDI .x18 .x16 0, .ADDI .x19 .x14 4056,
  .LUI .x20 4096, .ADDI .x21 .x15 0, .ADD .x22 .x15 .x17, .LUI .x23 3,
  .LUI .x24 3, .ADDI .x24 .x24 256, .LUI .x25 4, .LUI .x26 1,
  .ADDI .x27 .x0 256, .LUI .x3 1, .ADDI .x3 .x3 4056, .ADDI .x5 .x0 0,
  -- record, words 51–56
  .LD .x6 .x8 0, .SLLI .x28 .x6 8, .ADD .x28 .x3 .x28, .ADDI .x10 .x19 0,
  .ADDI .x11 .x0 200, .ADDI .x13 .x0 1,
  -- first permutation, words 57–65
  .SD .x10 .x28 0, .SD .x10 .x0 8, .SD .x10 .x0 16, .LD .x31 .x21 0,
  .SD .x10 .x31 24, .LD .x31 .x21 8, .SD .x10 .x31 32, .ADDI .x12 .x10 0,
  .ECALL,
  -- second permutation, words 66–70
  .ADDI .x10 .x10 96, .ADDI .x31 .x28 96, .SD .x10 .x31 0, .ADDI .x12 .x23 0,
  .ECALL,
  -- sibling setup, words 71–75
  .ADDI .x21 .x21 16, .ADD .x6 .x6 .x20, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0,
  .ADDI .x29 .x0 16,
  -- choose sibling side, words 76–77
  .ANDI .x7 .x6 1, .BEQ .x7 .x0 72,
  -- right child, words 78–94
  .LD .x31 .x21 0, .SD .x24 .x31 0, .LD .x31 .x21 8, .SD .x24 .x31 8,
  .LD .x31 .x21 16, .SD .x24 .x31 16, .LD .x31 .x21 24, .SD .x24 .x31 24,
  .LD .x31 .x23 0, .SD .x24 .x31 32, .LD .x31 .x23 8, .SD .x24 .x31 40,
  .LD .x31 .x23 16, .SD .x24 .x31 48, .LD .x31 .x23 24, .SD .x24 .x31 56,
  .JAL .x0 68,
  -- left child, words 95–110
  .LD .x31 .x23 0, .SD .x24 .x31 0, .LD .x31 .x23 8, .SD .x24 .x31 8,
  .LD .x31 .x23 16, .SD .x24 .x31 16, .LD .x31 .x23 24, .SD .x24 .x31 24,
  .LD .x31 .x21 0, .SD .x24 .x31 32, .LD .x31 .x21 8, .SD .x24 .x31 40,
  .LD .x31 .x21 16, .SD .x24 .x31 48, .LD .x31 .x21 24, .SD .x24 .x31 56,
  -- lower compression, words 111–117
  .ADDI .x10 .x24 0, .ADDI .x12 .x23 0, .ECALL, .ADDI .x21 .x21 32,
  .SRLI .x6 .x6 1, .ADDI .x29 .x29 4095, .BNE .x29 .x0 8028,
  -- group setup, words 118–123
  .SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .SLLI .x28 .x6 5, .ADD .x28 .x25 .x28,
  .LD .x29 .x7 0, .BEQ .x29 .x0 56,
  -- compare group, words 124–136
  .LD .x29 .x28 0, .LD .x30 .x23 0, .BNE .x29 .x30 368, .LD .x29 .x28 8,
  .LD .x30 .x23 8, .BNE .x29 .x30 356, .LD .x29 .x28 16, .LD .x30 .x23 16,
  .BNE .x29 .x30 344, .LD .x29 .x28 24, .LD .x30 .x23 24, .BNE .x29 .x30 332,
  .JAL .x0 44,
  -- write new group, words 137–146
  .LD .x31 .x23 0, .SD .x28 .x31 0, .LD .x31 .x23 8, .SD .x28 .x31 8,
  .LD .x31 .x23 16, .SD .x28 .x31 16, .LD .x31 .x23 24, .SD .x28 .x31 24,
  .ADDI .x29 .x0 1, .SD .x7 .x29 0,
  -- record latch, words 147–150
  .ADDI .x8 .x8 8, .ADDI .x19 .x19 256, .ADDI .x18 .x18 4095, .BNE .x18 .x0 7796,
  -- mark cap, words 151–161
  .ADDI .x6 .x0 255, .SLLI .x7 .x6 4, .ADD .x7 .x26 .x7, .LD .x28 .x7 0,
  .LD .x29 .x7 8, .OR .x28 .x28 .x29, .SLLI .x7 .x6 3, .ADD .x7 .x26 .x7,
  .SD .x7 .x28 0, .ADDI .x6 .x6 4095, .BNE .x6 .x0 8156,
  -- cap setup, words 162–164
  .ADDI .x11 .x0 64, .ADDI .x13 .x0 0, .ADDI .x6 .x0 1,
  -- cap lookup and descent, words 165–171
  .SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .LD .x28 .x7 0, .BEQ .x28 .x0 16,
  .BGEU .x6 .x27 64, .SLLI .x6 .x6 1, .JAL .x0 2097128,
  -- cap proof read, words 172–184
  .SLLI .x7 .x6 5, .ADD .x7 .x25 .x7, .ADDI .x28 .x21 32, .BLTU .x22 .x28 172,
  .LD .x31 .x21 0, .SD .x7 .x31 0, .LD .x31 .x21 8, .SD .x7 .x31 8,
  .LD .x31 .x21 16, .SD .x7 .x31 16, .LD .x31 .x21 24, .SD .x7 .x31 24,
  .ADDI .x21 .x21 32,
  -- cap advance, words 185–189
  .ADDI .x7 .x0 1, .BEQ .x6 .x7 48, .ANDI .x7 .x6 1, .BEQ .x7 .x0 32,
  .SRLI .x6 .x6 1,
  -- cap parent compression, words 190–195
  .SLLI .x10 .x6 6, .ADD .x10 .x25 .x10, .SLLI .x12 .x6 5, .ADD .x12 .x25 .x12,
  .ECALL, .JAL .x0 2097112,
  -- cap right child, words 196–197
  .ADDI .x6 .x6 1, .JAL .x0 2097024,
  -- root comparison, words 198–213
  .BNE .x21 .x22 80, .LD .x29 .x25 32, .LD .x30 .x9 0, .BNE .x29 .x30 68,
  .LD .x29 .x25 40, .LD .x30 .x9 8, .BNE .x29 .x30 56, .LD .x29 .x25 48,
  .LD .x30 .x9 16, .BNE .x29 .x30 44, .LD .x29 .x25 56, .LD .x30 .x9 24,
  .BNE .x29 .x30 32, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL,
  -- empty check, words 214–217
  .BNE .x17 .x0 16, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL,
  -- reject, words 218–220
  .ADDI .x5 .x0 1, .ADDI .x10 .x0 1, .ECALL
  ]

theorem checker_decoded :
    checkerImage.code.map Opening.decodeBase = checkerInstructions.map some := by decide

theorem checker_instruction_at (index : Nat) :
    (checkerImage.code[index]?).bind Opening.decodeBase = checkerInstructions[index]? := by
  have target := congrArg (fun codes : List (Option Instr) => (codes[index]?).getD none) checker_decoded
  simp only [List.getElem?_map] at target
  cases code : checkerImage.code[index]? <;> cases instruction : checkerInstructions[index]? <;>
    simpa [code, instruction] using target

/-- A fixed instruction ordinal fetches its checked bytes at the corresponding PC. -/
theorem checker_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 221) (pc : state.pc = BitVec.ofNat 64 (4096 + 4*index))
    (atIndex : checkerInstructions[index]? = some instruction) :
    fetch checkerImage state = some (.base instruction) := by
  have current : state.pc.toNat = 4096 + 4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hit := (checker_instruction_at index).trans atIndex
  rw [fetch, current, ite_eq_left (by omega), show (4096 + 4*index - 4096) / 4 = index by omega]
  cases code : checkerImage.code[index]? with
  | none => simp [code] at hit
  | some word =>
    simp [code, Opening.decodeBase] at hit
    cases dec : decodeInstruction word with
    | none => simp [dec] at hit
    | some decoded =>
      cases decoded with
      | base inst =>
        simp [dec] at hit
        simpa [hit] using dec
      | word op rd rs₁ rs₂ => simp [dec] at hit
      | sraiw rd rs sh => simp [dec] at hit

end TwoPermutationPrototype.Checker
