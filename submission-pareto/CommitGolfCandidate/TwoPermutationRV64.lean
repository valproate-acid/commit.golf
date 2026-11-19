import RiscvZkvm.Rv64.Execution
import RiscvZkvm.Interpreter.Decode

/-! The pinned RV64 decoder and ordinary execution for the two call preambles.
The challenge's two public syscalls and charged execution remain to be linked. -/
namespace TwoPermutationPrototype.RV64
open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

def firstInstructions (slot : Fin 16) : List Instr :=
  [.SD .x10 .x10 0, .SD .x10 .x0 8, .SD .x10 .x0 16,
   .LD .x31 .x22 (BitVec.ofNat 12 (16 * slot.val)), .SD .x10 .x31 24,
   .LD .x31 .x22 (BitVec.ofNat 12 (16 * slot.val + 8)), .SD .x10 .x31 32,
   .ADDI .x12 .x10 0]

def secondInstructions (slot : Fin 16) : List Instr :=
  [.ADDI .x10 .x10 96, .ADDI .x31 .x10 0, .SD .x10 .x31 0,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32 * slot.val))]

def leafInstructions (slot : Fin 16) : List Instr :=
  firstInstructions slot ++ [.ECALL] ++ secondInstructions slot ++ [.ECALL, .ADDI .x10 .x10 160]

def leafWords (slot : Fin 16) : List (BitVec 32) :=
  [0x00a53023, 0x00053423, 0x00053823, BitVec.ofNat 32 (0x000b3f83 + 2 ^ 24 * slot.val),
   0x01f53c23, BitVec.ofNat 32 (0x008b3f83 + 2 ^ 24 * slot.val), 0x03f53023, 0x00050613,
   0x00000073, 0x06050513, 0x00050f93, 0x01f53023,
   BitVec.ofNat 32 (0x000a0613 + 2 ^ 25 * slot.val), 0x00000073, 0x0a050513]

theorem leaf_decode : ∀ slot : Fin 16, (leafWords slot).map decode = (leafInstructions slot).map some := by
  decide

private theorem store_preserves_register (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

private theorem zero_register (state : MachineState) : state.getReg .x0 = 0 := rfl

private theorem nonce_offsets : ∀ slot : Fin 16,
    signExtend12 (BitVec.ofNat 12 (16 * slot.val)) = BitVec.ofNat 64 (16 * slot.val) ∧
    signExtend12 (BitVec.ofNat 12 (16 * slot.val + 8)) = BitVec.ofNat 64 (16 * slot.val + 8) := by
  decide

private theorem output_offset : ∀ slot : Fin 16,
    signExtend12 (BitVec.ofNat 12 (32 * slot.val)) = BitVec.ofNat 64 (32 * slot.val) := by
  decide

def firstMemory (state : MachineState) (slot : Fin 16) : MachineState :=
  let addr := state.getReg .x10
  let nonce := state.getReg .x22
  let nonce₀ := state.getMem (nonce + BitVec.ofNat 64 (16 * slot.val))
  let nonce₁ := state.getMem (nonce + BitVec.ofNat 64 (16 * slot.val + 8))
  let initialized := (((state.setMem addr addr).setMem (addr + 8) 0).setMem (addr + 16) 0)
  (initialized.setMem (addr + 24) nonce₀).setMem (addr + 32) nonce₁

theorem first_execution (state : MachineState) (slot : Fin 16)
    (firstDisjoint : ∀ offset ∈ ([0, 8, 16] : List Word),
      state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val) ≠ state.getReg .x10 + offset)
    (secondDisjoint : ∀ offset ∈ ([0, 8, 16, 24] : List Word),
      state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val + 8) ≠ state.getReg .x10 + offset) :
    let before := (firstInstructions slot).foldl execInstrBr state
    before.mem = (firstMemory state slot).mem ∧
    before.getReg .x10 = state.getReg .x10 ∧ before.getReg .x12 = state.getReg .x10 ∧
    before.getReg .x5 = state.getReg .x5 ∧ before.getReg .x11 = state.getReg .x11 ∧
    before.getReg .x13 = state.getReg .x13 ∧ before.pc = state.pc + 32 := by
  have d0 := firstDisjoint 0 (by decide)
  have d8 := firstDisjoint 8 (by decide)
  have d16 := firstDisjoint 16 (by decide)
  have e0 := secondDisjoint 0 (by decide)
  have e8 := secondDisjoint 8 (by decide)
  have e16 := secondDisjoint 16 (by decide)
  have e24 := secondDisjoint 24 (by decide)
  have d0' : state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val) ≠ state.getReg .x10 := by
    simpa using d0
  have e0' : state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val + 8) ≠ state.getReg .x10 := by
    simpa using e0
  have offset := nonce_offsets slot
  simp only [firstInstructions, firstMemory, List.foldl_cons, List.foldl_nil, execInstrBr,
    show signExtend12 0 = (0 : Word) by decide, show signExtend12 8 = (8 : Word) by decide,
    show signExtend12 16 = (16 : Word) by decide, show signExtend12 24 = (24 : Word) by decide,
    show signExtend12 32 = (32 : Word) by decide,
    MachineState.getReg_setPC, store_preserves_register,
    MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x22),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x13),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x13),
    MachineState.getMem_setReg, MachineState.getMem_setPC,
    MachineState.getMem_setMem_ne d8, MachineState.getMem_setMem_ne d16,
    MachineState.getMem_setMem_ne e8, MachineState.getMem_setMem_ne e16,
    MachineState.getMem_setMem_ne e24, offset.1, offset.2]
  simp [MachineState.setReg, MachineState.setMem, MachineState.setPC, MachineState.getMem,
    BitVec.add_assoc, zero_register, d0', e0']

theorem second_execution (state : MachineState) (slot : Fin 16) :
    let before := (secondInstructions slot).foldl execInstrBr state
    let addr := state.getReg .x10 + 96
    before.mem = (state.setMem addr (addr + 0)).mem ∧ before.getReg .x10 = addr ∧
    before.getReg .x12 = state.getReg .x20 + BitVec.ofNat 64 (32 * slot.val) ∧
    before.getReg .x5 = state.getReg .x5 ∧ before.getReg .x11 = state.getReg .x11 ∧
    before.getReg .x13 = state.getReg .x13 ∧ before.pc = state.pc + 16 := by
  simp only [secondInstructions, List.foldl_cons, List.foldl_nil, execInstrBr,
    show signExtend12 0 = (0 : Word) by decide, 
    show signExtend12 96 = (96 : Word) by decide,
    MachineState.getReg_setPC, store_preserves_register,
    MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x13),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x31 ≠ .x13),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x5),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x11),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x13), output_offset]
  simp [MachineState.setReg, MachineState.setMem, MachineState.setPC, BitVec.add_assoc]

end TwoPermutationPrototype.RV64
