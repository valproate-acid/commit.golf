import CommitGolfCandidate.TwoPermutationPackedCheckerSteps
import CommitGolfCandidate.TwoPermutationOpeningBlocks

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000
attribute [local simp] Opening.getReg_setReg MachineState.getReg_setPC
@[local simp] private theorem setup_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl

def checkPrepareWords : List Instr :=
  [.ADDI .x8 .x13 0,.ADDI .x9 .x11 0,.ADDI .x18 .x16 0,.ADDI .x19 .x14 4056,
   .LUI .x20 4096,.ADDI .x21 .x15 0,.ADD .x22 .x15 .x17,.LUI .x23 3,
   .LUI .x24 3,.ADDI .x24 .x24 256,.LUI .x25 4,.LUI .x26 1,
   .ADDI .x27 .x0 256,.LUI .x4 3,.ADDI .x4 .x4 4080,.LUI .x3 1,.ADDI .x3 .x3 4056,.ADDI .x5 .x0 0]

def checkPreparePrefix (s : MachineState) (count : Nat) :=
  (checkPrepareWords.take count).foldl execInstrBr s

theorem check_prepare_hop (s : MachineState) (pc : s.pc=0x1010) :
    GroupHop s (checkPreparePrefix s 18) 18 := by
  intro fuel
  apply execute_unit_steps (states := checkPreparePrefix s)
  intro i inside
  refine ⟨.base (checkPrepareWords[i]?.getD .EBREAK), fetch_at _ (4+i) _ (by omega) ?_ ?_,?_,?_⟩
  · interval_cases i <;> simp [checkPreparePrefix,checkPrepareWords,execInstrBr,pc]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure CheckPrepared (s t : MachineState) : Prop where
  pc : t.pc=0x1058
  index : t.getReg .x8=s.getReg .x13
  root : t.getReg .x9=s.getReg .x11
  count : t.getReg .x18=s.getReg .x16
  value : t.getReg .x19=s.getReg .x14-40
  length : t.getReg .x20=16777216
  proof : t.getReg .x21=s.getReg .x15
  proofEnd : t.getReg .x22=s.getReg .x15+s.getReg .x17
  digest : t.getReg .x23=12288
  pair : t.getReg .x24=12544
  capRoots : t.getReg .x25=16384
  marks : t.getReg .x26=4096
  capCount : t.getReg .x27=256
  nonceScratch : t.getReg .x4=12272
  tag : t.getReg .x3=4056
  selector : t.getReg .x5=0
  memory : t.mem=s.mem

theorem check_prepare_view (s : MachineState) (pc : s.pc=0x1010) :
    CheckPrepared s (checkPreparePrefix s 18) := by
  have zero (st : MachineState) : st.getReg .x0=0#64 := rfl
  constructor <;> simp [checkPreparePrefix,checkPrepareWords,execInstrBr,pc,
    signExtend12,zero,BitVec.sub_eq_add_neg] <;> rfl

inductive CheckGuard where | short | empty | tail

def CheckGuard.index : CheckGuard → Nat | .short => 2 | .empty => 3 | .tail => 360

def CheckGuard.instr : CheckGuard → Instr
  | .short => .BLTU .x17 .x6 1448
  | .empty => .BEQ .x16 .x0 1428
  | .tail => .BNE .x17 .x0 16

def CheckGuard.next (g : CheckGuard) (s : MachineState) := execInstrBr s g.instr

theorem check_guard_hop (g : CheckGuard) (s : MachineState)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*g.index)) : GroupHop s (g.next s) 1 := by
  intro fuel
  rw [Nat.add_comm 1 fuel]
  have fetched := fetch_at s g.index g.instr (by cases g <;> decide) pc (by cases g <;> rfl)
  rw [execute,fetched]
  cases g <;> rfl

theorem check_guard_register (g : CheckGuard) (s : MachineState) (r : Reg) : (g.next s).getReg r=s.getReg r := by
  cases g <;> simp only [CheckGuard.next,CheckGuard.instr,execInstrBr] <;> split <;> rfl

theorem check_guard_memory (g : CheckGuard) (s : MachineState) : (g.next s).mem=s.mem := by
  cases g <;> simp only [CheckGuard.next,CheckGuard.instr,execInstrBr] <;> split <;> rfl

theorem check_short_guard (s : MachineState) (pc : s.pc=4104) :
    (CheckGuard.short.next s).pc = if s.getReg .x17<s.getReg .x6 then 0x15b0 else 4108 := by
  simp only [CheckGuard.next,CheckGuard.instr,execInstrBr,BitVec.ult_iff_toNat_lt]
  by_cases short : s.getReg .x17<s.getReg .x6
  · change (s.getReg .x17).toNat < (s.getReg .x6).toNat at short
    simp [short,pc,signExtend13]
    exact short
  · have no : ¬(s.getReg .x17).toNat < (s.getReg .x6).toNat := short
    simp [short,no,pc]

theorem check_empty_guard (s : MachineState) (pc : s.pc=4108) :
    (CheckGuard.empty.next s).pc = if s.getReg .x16=0 then 0x15a0 else 4112 := by
  simp only [CheckGuard.next,CheckGuard.instr,execInstrBr,beq_iff_eq,show s.getReg .x0=0#64 by rfl]
  by_cases z : s.getReg .x16=0#64 <;> simp [z,pc,signExtend13]

theorem check_tail_guard (s : MachineState) (pc : s.pc=0x15a0) :
    (CheckGuard.tail.next s).pc = if s.getReg .x17=0 then 0x15a4 else 0x15b0 := by
  simp only [CheckGuard.next,CheckGuard.instr,execInstrBr,bne_iff_ne,show s.getReg .x0=0#64 by rfl]
  by_cases z : s.getReg .x17=0#64 <;> simp [z,pc,signExtend13]

end TwoPermutationPrototype.Packed.Checker
