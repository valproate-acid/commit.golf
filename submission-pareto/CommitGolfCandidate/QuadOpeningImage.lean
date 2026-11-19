import CommitGolfCandidate.QOpeningImage
import CommitGolfCandidate.TwoPermutationPentaSpec

/-! The penta opening image (479 words, no image data) and its symbolic program.

Registers: `x8` index pointer, `x9` trapdoor, `x18` positions left, `x19 = 5`, `x15` proof start,
`x21` output cursor, `x22` salt base, `x23 = 368`. Per position: load the index into `x6`, copy the
16-byte salt, then for each level `k = 0 … 10` (with `x6 = index / 5^k`): `x24 = x6 / 5`,
`x25 = x6 % 5`, `x30` = trapdoor + group base `k` + 40 + 368 `x24`; `jalr x1` enters copy variant
`x25` (word `159 + 64 x25`, `x26` holds its table base), which copies the four other children
`x30 + 32 ((x25 + j + 1) % 5)` (`j = 0 … 3`) with 16 doubleword loads/stores at fixed offsets,
advances `x21` by 128 and returns; then `x6 = x24`. No footer. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

def openingImage : Image := ⟨[
  0x00078a93, 0x26080263, 0x00068413, 0x00060493, 0x00080913, 0x6c001b37, 0x01648b33, 0x00500993,
  0x17000b93, 0x00001d37, 0x27cd0d13, 0x00043303, 0x00431393, 0x007b03b3, 0x0003bf83, 0x01fab023,
  0x0083bf83, 0x01fab423, 0x010a8a93, 0x03335c33, 0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533,
  0x000015b7, 0x009585b3, 0x00b50f33, 0x008c9393, 0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33,
  0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533, 0x4999c5b7, 0x009585b3, 0x00b50f33, 0x008c9393,
  0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33, 0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533,
  0x585235b7, 0x009585b3, 0x00b50f33, 0x008c9393, 0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33,
  0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533, 0x5b43f5b7, 0x009585b3, 0x00b50f33, 0x008c9393,
  0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33, 0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533,
  0x5bdac5b7, 0x009585b3, 0x00b50f33, 0x008c9393, 0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33,
  0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533, 0x5bf905b7, 0x009585b3, 0x00b50f33, 0x008c9393,
  0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33, 0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533,
  0x5bff25b7, 0x009585b3, 0x00b50f33, 0x008c9393, 0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33,
  0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533, 0x5c0075b7, 0x009585b3, 0x00b50f33, 0x008c9393,
  0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33, 0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533,
  0x5c00c5b7, 0x009585b3, 0x00b50f33, 0x008c9393, 0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33,
  0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533, 0x5c00e5b7, 0x009585b3, 0x00b50f33, 0x008c9393,
  0x01a383b3, 0x000380e7, 0x000c0313, 0x03335c33, 0x002c1c93, 0x018c8cb3, 0x41930cb3, 0x037c0533,
  0x5c0105b7, 0x009585b3, 0x00b50f33, 0x008c9393, 0x01a383b3, 0x000380e7, 0x000c0313, 0x00840413,
  0xfff90913, 0xdc0914e3, 0x40fa85b3, 0x00100293, 0x00000513, 0x00000073, 0x00000013, 0x020f3f83,
  0x01fab023, 0x028f3f83, 0x01fab423, 0x030f3f83, 0x01fab823, 0x038f3f83, 0x01fabc23, 0x040f3f83,
  0x03fab023, 0x048f3f83, 0x03fab423, 0x050f3f83, 0x03fab823, 0x058f3f83, 0x03fabc23, 0x060f3f83,
  0x05fab023, 0x068f3f83, 0x05fab423, 0x070f3f83, 0x05fab823, 0x078f3f83, 0x05fabc23, 0x080f3f83,
  0x07fab023, 0x088f3f83, 0x07fab423, 0x090f3f83, 0x07fab823, 0x098f3f83, 0x07fabc23, 0x080a8a93,
  0x00008067, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x040f3f83,
  0x01fab023, 0x048f3f83, 0x01fab423, 0x050f3f83, 0x01fab823, 0x058f3f83, 0x01fabc23, 0x060f3f83,
  0x03fab023, 0x068f3f83, 0x03fab423, 0x070f3f83, 0x03fab823, 0x078f3f83, 0x03fabc23, 0x080f3f83,
  0x05fab023, 0x088f3f83, 0x05fab423, 0x090f3f83, 0x05fab823, 0x098f3f83, 0x05fabc23, 0x000f3f83,
  0x07fab023, 0x008f3f83, 0x07fab423, 0x010f3f83, 0x07fab823, 0x018f3f83, 0x07fabc23, 0x080a8a93,
  0x00008067, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x060f3f83,
  0x01fab023, 0x068f3f83, 0x01fab423, 0x070f3f83, 0x01fab823, 0x078f3f83, 0x01fabc23, 0x080f3f83,
  0x03fab023, 0x088f3f83, 0x03fab423, 0x090f3f83, 0x03fab823, 0x098f3f83, 0x03fabc23, 0x000f3f83,
  0x05fab023, 0x008f3f83, 0x05fab423, 0x010f3f83, 0x05fab823, 0x018f3f83, 0x05fabc23, 0x020f3f83,
  0x07fab023, 0x028f3f83, 0x07fab423, 0x030f3f83, 0x07fab823, 0x038f3f83, 0x07fabc23, 0x080a8a93,
  0x00008067, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x080f3f83,
  0x01fab023, 0x088f3f83, 0x01fab423, 0x090f3f83, 0x01fab823, 0x098f3f83, 0x01fabc23, 0x000f3f83,
  0x03fab023, 0x008f3f83, 0x03fab423, 0x010f3f83, 0x03fab823, 0x018f3f83, 0x03fabc23, 0x020f3f83,
  0x05fab023, 0x028f3f83, 0x05fab423, 0x030f3f83, 0x05fab823, 0x038f3f83, 0x05fabc23, 0x040f3f83,
  0x07fab023, 0x048f3f83, 0x07fab423, 0x050f3f83, 0x07fab823, 0x058f3f83, 0x07fabc23, 0x080a8a93,
  0x00008067, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x000f3f83,
  0x01fab023, 0x008f3f83, 0x01fab423, 0x010f3f83, 0x01fab823, 0x018f3f83, 0x01fabc23, 0x020f3f83,
  0x03fab023, 0x028f3f83, 0x03fab423, 0x030f3f83, 0x03fab823, 0x038f3f83, 0x03fabc23, 0x040f3f83,
  0x05fab023, 0x048f3f83, 0x05fab423, 0x050f3f83, 0x05fab823, 0x058f3f83, 0x05fabc23, 0x060f3f83,
  0x07fab023, 0x068f3f83, 0x07fab423, 0x070f3f83, 0x07fab823, 0x078f3f83, 0x07fabc23, 0x080a8a93,
  0x00008067, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013,
  0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013], []⟩

/-- `lui` page of the level-`k` group base plus 40. -/
def groupPage (k : Nat) : Nat := (pentaGroupBase k + 40) / 4096

/-- `n` doubleword load/store pairs from `x7` to `x21`. -/
def pairCode (n : Nat) : List Instr :=
  (List.range n).flatMap fun w => [.LD .x31 .x7 (BitVec.ofNat 12 (8*w)), .SD .x21 .x31 (BitVec.ofNat 12 (8*w))]

def setupCode : List Instr :=
  [.ADDI .x21 .x15 0, .BEQ .x16 .x0 612, .ADDI .x8 .x13 0, .ADDI .x9 .x12 0,
   .ADDI .x18 .x16 0, .LUI .x22 442369, .ADD .x22 .x9 .x22, .ADDI .x19 .x0 5, .ADDI .x23 .x0 368,
   .LUI .x26 1, .ADDI .x26 .x26 636]

def saltHead : List Instr := [.LD .x6 .x8 0, .SLLI .x7 .x6 4, .ADD .x7 .x22 .x7]

def saltCode : List Instr := saltHead ++ pairCode 2 ++ [.ADDI .x21 .x21 16]

def levelHead (k : Nat) : List Instr :=
  [.DIVU .x24 .x6 .x19, .SLLI .x25 .x24 2, .ADD .x25 .x25 .x24, .SUB .x25 .x6 .x25,
   .MUL .x10 .x24 .x23, .LUI .x11 (BitVec.ofNat 20 (groupPage k)), .ADD .x11 .x11 .x9,
   .ADD .x30 .x10 .x11]

def dispatchCode : List Instr := [.SLLI .x7 .x25 8, .ADD .x7 .x7 .x26]

def levelCode (k : Nat) : List Instr :=
  levelHead k ++ dispatchCode ++ [.JALR .x1 .x7 0, .ADDI .x6 .x24 0]

def tailCode : List Instr := [.ADDI .x8 .x8 8, .ADDI .x18 .x18 4095, .BNE .x18 .x0 7624]

/-- Trapdoor-group offset of output doubleword `m < 16` in copy variant `v` (rotation by `v`). -/
def variantOffset (v m : Nat) : Nat := 32*((v+m/4+1)%5)+8*(m%4)

/-- `n` load/store pairs of copy variant `v`: source `x30 + variantOffset v m`, target `x21 + 8m`. -/
def variantPairs (v n : Nat) : List Instr :=
  (List.range n).flatMap fun m =>
    [.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v m)), .SD .x21 .x31 (BitVec.ofNat 12 (8*m))]

def variantCode (v : Nat) : List Instr :=
  variantPairs v 16 ++ [.ADDI .x21 .x21 128, .JALR .x0 .x1 0] ++ List.replicate 30 (.ADDI .x0 .x0 0)

def exitCode : List Instr := [.SUB .x11 .x21 .x15, .ADDI .x5 .x0 1, .ADDI .x10 .x0 0, .ECALL]

def program : List Instr :=
  -- Preserve variant addresses with one unreachable word after the ECALL exit.
  setupCode ++ saltCode ++ (List.range 11).flatMap levelCode ++ tailCode ++ exitCode ++ [.ADDI .x0 .x0 0] ++
    (List.range 5).flatMap variantCode

theorem program_length : program.length = 479 := by decide

set_option maxHeartbeats 4000000 in
theorem program_decoded : openingImage.code.map QOpening.decodeBase = program.map some := by
  decide +kernel

theorem image_length : openingImage.code.length = 479 := by decide

theorem program_decode (index : Nat) :
    (openingImage.code[index]?).bind QOpening.decodeBase = program[index]? := by
  have h := congrArg (fun l => l[index]?) program_decoded
  simp only [List.getElem?_map] at h
  cases hc : openingImage.code[index]? <;> cases hp : program[index]? <;> simp_all

theorem fetch_program (state : MachineState) (index : Nat) (instruction : Instr)
    (code : program[index]? = some instruction)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*index)) :
    fetch openingImage state = some (.base instruction) := by
  have bounded : index < 479 := by
    rw [← program_length]
    exact (List.getElem?_eq_some_iff.mp code).1
  have decoded := (program_decode index).trans code
  have current : state.pc.toNat = 4096+4*index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, current, ite_eq_left (by omega), show (4096+4*index-4096)/4 = index by omega]
  cases hcode : openingImage.code[index]? with
  | none => simp [hcode] at decoded
  | some w =>
    simp [hcode, QOpening.decodeBase] at decoded
    cases dec : decodeInstruction w with
    | none => simp [dec] at decoded
    | some result =>
      cases result with
      | base inst =>
        simp [dec] at decoded
        simpa [decoded] using dec
      | word op rd rs₁ rs₂ => simp [dec] at decoded
      | sraiw rd rs sh => simp [dec] at decoded

end TwoPermutationPrototype.QuadOpening
