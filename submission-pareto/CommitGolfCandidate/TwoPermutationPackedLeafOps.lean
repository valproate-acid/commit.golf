import CommitGolfCandidate.TwoPermutationPinnedWindows
import CommitGolfCandidate.TwoPermutationLeafRun
import CommitGolfCandidate.TwoPermutationOpeningCopy

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 950000

def firstInstructions (_slot : Fin 4096) : List Instr := [.ADDI .x12 .x10 4064]
def secondInstructions (slot : Fin 4096) : List Instr :=
  [.ADDI .x10 .x10 56,.SD .x10 .x10 0,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot.val%128))),.SD .x10 .x31 8,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot.val%128)+8)),.SD .x10 .x31 16,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32*(slot.val%64)))]

def leafInstructions (slot : Fin 4096) : List Instr :=
  firstInstructions slot ++ [.ECALL] ++ secondInstructions slot ++ [.ECALL,.ADDI .x10 .x10 200]

private theorem nonce_offsets_table : ∀ slot : Fin 128,
    signExtend12 (BitVec.ofNat 12 (16*slot.val)) = BitVec.ofNat 64 (16*slot.val) ∧
    signExtend12 (BitVec.ofNat 12 (16*slot.val + 8)) = BitVec.ofNat 64 (16*slot.val + 8) := by decide

private theorem nonce_offsets (slot : Fin 4096) :
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128))) = BitVec.ofNat 64 (16*(slot.val%128)) ∧
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128) + 8)) = BitVec.ofNat 64 (16*(slot.val%128) + 8) :=
  nonce_offsets_table ⟨slot.val%128, Nat.mod_lt _ (by decide)⟩

private theorem output_offset_table : ∀ slot : Fin 64,
    signExtend12 (BitVec.ofNat 12 (32*slot.val)) = BitVec.ofNat 64 (32*slot.val) := by decide

private theorem output_offset (slot : Fin 4096) :
    signExtend12 (BitVec.ofNat 12 (32*(slot.val%64))) = BitVec.ofNat 64 (32*(slot.val%64)) :=
  output_offset_table ⟨slot.val%64, Nat.mod_lt _ (by decide)⟩


def nonceWords (state : MachineState) (slot : Fin 4096) : Words 2 := fun i =>
  if i.val=0 then state.getMem (state.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128)))
  else state.getMem (state.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128)+8))

def secondMemory (s : MachineState) (slot : Fin 4096) : MachineState :=
  let tag := s.getReg .x10+56
  ((s.setMem tag tag).setMem (tag+8) (nonceWords s slot 0)).setMem (tag+16) (nonceWords s slot 1)

def preparedA (s : MachineState) (slot : Fin 4096) := (firstInstructions slot).foldl execInstrBr s
def repliedA (s : MachineState) (slot : Fin 4096) (start : Nat) (answer : BitVec 1600) :=
  writeBits (preparedA s slot) (wordAddress (start+1)) answer
def preparedB (s : MachineState) (slot : Fin 4096) (start : Nat) (a : BitVec 1600) :=
  (secondInstructions slot).foldl execInstrBr (repliedA s slot start a)
def repliedB (s : MachineState) (slot : Fin 4096) (start dst : Nat) (a b : BitVec 1600) :=
  writeBits (preparedB s slot start a) (wordAddress dst) b
def finishedLeaf (s : MachineState) (slot : Fin 4096) (start dst : Nat) (a b : BitVec 1600) :=
  execInstrBr (repliedB s slot start dst a b) (.ADDI .x10 .x10 200)

theorem first_execution (s : MachineState) (slot : Fin 4096) :
    let before := preparedA s slot
    before.mem=s.mem ∧ before.getReg .x10=s.getReg .x10 ∧ before.getReg .x12=s.getReg .x10+signExtend12 4064 ∧
    before.pc=s.pc+4 := ⟨rfl,rfl,rfl,rfl⟩

theorem first_keeps (s : MachineState) (slot : Fin 4096) (r : Reg) (p : r≠.x10) (q : r≠.x12) :
    (preparedA s slot).getReg r=s.getReg r := by
  simp only [preparedA,firstInstructions,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm p),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm q)]

private theorem store_regs (s : MachineState) (addr val : Word) (r : Reg) : (s.setMem addr val).getReg r=s.getReg r := by cases r <;> rfl

def StampSeparate (s : MachineState) (slot : Fin 4096) : Prop :=
  let base := s.getReg .x10+56
  let salt := s.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128))
  salt≠base ∧ salt+8≠base ∧ salt+8≠base+8

theorem second_execution (s : MachineState) (slot : Fin 4096) (apart : StampSeparate s slot) :
    let before := (secondInstructions slot).foldl execInstrBr s
    before.mem=(secondMemory s slot).mem ∧ before.getReg .x10=s.getReg .x10+56 ∧
    before.getReg .x12=s.getReg .x20+BitVec.ofNat 64 (32*(slot.val%64)) ∧ before.pc=s.pc+28 := by
  have ⟨d0,e0,e1⟩ := apart
  have offsets := nonce_offsets slot
  have add8 : s.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128)+8)=
      (s.getReg .x22+BitVec.ofNat 64 (16*(slot.val%128)))+8 := by
    rw [BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  simp only [secondInstructions,secondMemory,List.foldl_cons,List.foldl_nil,execInstrBr,
    show signExtend12 56=56#64 by decide, show signExtend12 0=0#64 by decide,
    show signExtend12 8=8#64 by decide, show signExtend12 16=16#64 by decide,
    offsets.1,offsets.2,output_offset,MachineState.getReg_setPC,store_regs,Opening.getReg_setReg,
    MachineState.getMem_setPC,MachineState.getMem_setReg]
  simp [MachineState.setReg,MachineState.setMem,MachineState.setPC,MachineState.getMem,nonceWords,add8,
    BitVec.add_assoc] at *
  simp only [ite_eq_right d0,ite_eq_right e0,ite_eq_right e1]

theorem second_keeps (s : MachineState) (slot : Fin 4096) (r : Reg) (a : r≠.x10) (b : r≠.x12) (c : r≠.x31) :
    ((secondInstructions slot).foldl execInstrBr s).getReg r=s.getReg r := by
  simp only [secondInstructions,List.foldl_cons,List.foldl_nil,execInstrBr,MachineState.getReg_setPC,store_regs,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm c)]

end TwoPermutationPrototype.RV64.PackedLeaves
