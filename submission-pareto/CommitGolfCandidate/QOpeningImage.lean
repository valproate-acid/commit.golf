import CommitGolfCandidate.Execution
import CommitGolfCandidate.QOpeningMemory

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

/-- Default depth-24 opening image emitted by two_permutation.py. -/
def openingImage : Image := ⟨[
  0x00078a13, 0x00078a93, 0x14080063, 0x00068413, 0x00060493, 0x00080913, 0x010009b7, 0x50000b37,
  0x01648b33, 0x00100b93, 0x00048c93, 0x00001d37, 0x10000d93, 0x00043303, 0x00431393, 0x007b03b3,
  0x0003bf83, 0x01fab023, 0x0083bf83, 0x01fab423, 0x010a8a93, 0x01330333, 0x01000e93, 0x00134393,
  0x00539393, 0x007483b3, 0x0003bf83, 0x01fab023, 0x0083bf83, 0x01fab423, 0x0103bf83, 0x01fab823,
  0x0183bf83, 0x01fabc23, 0x020a8a93, 0x00135313, 0xfffe8e93, 0xfc0e94e3, 0x00331393, 0x007d03b3,
  0x0173b023, 0x00840413, 0xfff90913, 0xf80914e3, 0x0ff00313, 0x00431393, 0x007d03b3, 0x0003be03,
  0x0083be83, 0x01de6e33, 0x00331393, 0x007d03b3, 0x01c3b023, 0xfff30313, 0xfc031ee3, 0x00100313,
  0x00331393, 0x007d03b3, 0x0003be03, 0x000e0863, 0x03b37c63, 0x00131313, 0xfe9ff06f, 0x00531393,
  0x007c83b3, 0x0003bf83, 0x01fab023, 0x0083bf83, 0x01fab423, 0x0103bf83, 0x01fab823, 0x0183bf83,
  0x01fabc23, 0x020a8a93, 0x00100393, 0x00730e63, 0x00137393, 0x00038663, 0x00135313, 0xfedff06f,
  0x00130313, 0xf9dff06f, 0x414a85b3, 0x00100293, 0x00000513, 0x00000073], []⟩

theorem opening_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 86) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : (openingImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch openingImage state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, ite_eq_left (by omega)]
  rw [show (4096 + 4 * index - 4096) / 4 = index by omega]
  cases word : openingImage.code[index]? with
  | none => simp [word] at decoded
  | some word => simpa [word] using decoded

/-- The empty case goes directly to the shared return block. -/
def setupInstructions : List Instr :=
  [.ADDI .x20 .x15 0, .ADDI .x21 .x15 0, .BEQ .x16 .x0 320,
   .ADDI .x8 .x13 0, .ADDI .x9 .x12 0, .ADDI .x18 .x16 0,
   .LUI .x19 4096, .LUI .x22 327680, .ADD .x22 .x9 .x22,
   .ADDI .x23 .x0 1, .ADDI .x25 .x9 0, .LUI .x26 1, .ADDI .x27 .x0 256]

def nonceInstructions : List Instr :=
  [.LD .x6 .x8 0, .SLLI .x7 .x6 4, .ADD .x7 .x22 .x7,
   .LD .x31 .x7 0, .SD .x21 .x31 0, .LD .x31 .x7 8, .SD .x21 .x31 8,
   .ADDI .x21 .x21 16, .ADD .x6 .x6 .x19, .ADDI .x29 .x0 16]

def siblingInstructions : List Instr :=
  [.XORI .x7 .x6 1, .SLLI .x7 .x7 5, .ADD .x7 .x9 .x7,
   .LD .x31 .x7 0, .SD .x21 .x31 0, .LD .x31 .x7 8, .SD .x21 .x31 8,
   .LD .x31 .x7 16, .SD .x21 .x31 16, .LD .x31 .x7 24, .SD .x21 .x31 24,
   .ADDI .x21 .x21 32, .SRLI .x6 .x6 1, .ADDI .x29 .x29 4095, .BNE .x29 .x0 8136]

def recordTailInstructions : List Instr :=
  [.SLLI .x7 .x6 3, .ADD .x7 .x26 .x7, .SD .x7 .x23 0,
   .ADDI .x8 .x8 8, .ADDI .x18 .x18 4095, .BNE .x18 .x0 8072]

def decodeBase (word : BitVec 32) : Option Instr :=
  (decodeInstruction word).bind fun
    | .base instruction => some instruction
    | _ => none

theorem opening_prefix_decoded :
    ((openingImage.code.take 44).map decodeBase) =
      ((setupInstructions ++ nonceInstructions ++ siblingInstructions ++ recordTailInstructions).map some) := by
  decide

theorem nonce_decode (i : Fin 10) :
    (openingImage.code[13 + i.val]?).bind decodeInstruction =
      some (.base (nonceInstructions[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> rfl

theorem sibling_decode (i : Fin 15) :
    (openingImage.code[23 + i.val]?).bind decodeInstruction =
      some (.base (siblingInstructions[i.val]?.getD .EBREAK)) := by
  fin_cases i <;> rfl

end TwoPermutationPrototype.QOpening
