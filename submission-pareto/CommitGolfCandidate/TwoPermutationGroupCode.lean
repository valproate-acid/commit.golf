import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationCheckerRecordSetup

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

inductive GroupBlock where
  | setup | compare (i : Fin 4) | duplicate | mark | latch

def GroupBlock.words : GroupBlock → List Instr
  | .setup => [.SLLI .x7 .x6 3,.ADD .x7 .x26 .x7,.SLLI .x28 .x6 5,.ADD .x28 .x25 .x28,
      .LD .x29 .x7 0,.BEQ .x29 .x0 56]
  | .compare i => [.LD .x29 .x28 (BitVec.ofNat 12 (8*i.val)),
      .LD .x30 .x23 (BitVec.ofNat 12 (8*i.val)),.BNE .x29 .x30 (BitVec.ofNat 13 (368-12*i.val))]
  | .duplicate => [.JAL .x0 44]
  | .mark => [.ADDI .x29 .x0 1,.SD .x7 .x29 0]
  | .latch => [.ADDI .x8 .x8 8,.ADDI .x19 .x19 256,.ADDI .x18 .x18 4095,.BNE .x18 .x0 7796]

def GroupBlock.start : GroupBlock → Nat
  | .setup => 118 | .compare i => 124+3*i.val | .duplicate => 136 | .mark => 145 | .latch => 147

def GroupBlock.partialState (block : GroupBlock) (state : MachineState) (count : Nat) :=
  (block.words.take count).foldl execInstrBr state

def GroupBlock.done (block : GroupBlock) (state : MachineState) :=
  block.words.foldl execInstrBr state

def groupMarkAddress (s : MachineState) := s.getReg .x26+(s.getReg .x6 <<< 3)
def groupRootAddress (s : MachineState) := s.getReg .x25+(s.getReg .x6 <<< 5)

def GroupBlock.Valid (block : GroupBlock) (s : MachineState) : Prop :=
  match block with
  | .setup => accessValid (groupMarkAddress s) 8=true
  | .compare i => accessValid (s.getReg .x28+BitVec.ofNat 64 (8*i.val)) 8=true ∧
      accessValid (s.getReg .x23+BitVec.ofNat 64 (8*i.val)) 8=true
  | .duplicate | .latch => True
  | .mark => accessValid (s.getReg .x7) 8=true

private theorem group_prefix_succ (block : GroupBlock) (s : MachineState) (i : Nat)
    (inside : i<block.words.length) :
    block.partialState s (i+1)=execInstrBr (block.partialState s i) (block.words[i]?.getD .EBREAK) := by
  simp only [GroupBlock.partialState,List.take_succ_eq_append_getElem inside,List.foldl_append,
    List.getElem?_eq_getElem inside,Option.getD_some,List.foldl_cons,List.foldl_nil]

private theorem group_decode (block : GroupBlock) (i : Nat) (inside : i<block.words.length) :
    checkerInstructions[block.start+i]?=some (block.words[i]?.getD .EBREAK) := by
  cases block with
  | compare n => fin_cases n <;> change i<3 at inside <;> interval_cases i <;> rfl
  | setup => change i<6 at inside; interval_cases i <;> rfl
  | duplicate => change i<1 at inside; interval_cases i <;> rfl
  | mark => change i<2 at inside; interval_cases i <;> rfl
  | latch => change i<4 at inside; interval_cases i <;> rfl

private theorem prefix_pc (block : GroupBlock) (s : MachineState) (i : Nat)
    (inside : i<block.words.length) :
    (block.partialState s i).pc=s.pc+BitVec.ofNat 64 (4*i) := by
  have short : i<6 := by cases block <;> simp [GroupBlock.words] at inside <;> omega
  cases block <;> simp [GroupBlock.words] at inside <;> interval_cases i <;> first | omega |
    simp [GroupBlock.partialState,GroupBlock.words,execInstrBr,MachineState.setPC,BitVec.add_assoc]

private theorem group_ordinary (block : GroupBlock) (s : MachineState) (i : Nat)
    (inside : i<block.words.length) (valid : block.Valid s) :
    ordinaryStep (block.partialState s i) (.base (block.words[i]?.getD .EBREAK)) =
      some (block.partialState s (i+1)) := by
  rw [group_prefix_succ _ _ _ inside]
  cases block with
  | compare n =>
    have l:=valid.1
    have r:=valid.2
    fin_cases n <;> change i<3 at inside <;> interval_cases i <;>
      simp_all [GroupBlock.partialState,GroupBlock.words,ordinaryStep,memoryArgumentsValid,
        memAccess,execInstrBr,signExtend12]
  | setup =>
    change accessValid (s.getReg .x26+(s.getReg .x6 <<< 3)) 8=true at valid
    change i<6 at inside
    interval_cases i <;> simp [GroupBlock.partialState,GroupBlock.words,ordinaryStep,memoryArgumentsValid,
      memAccess,execInstrBr,signExtend12,valid]
  | mark =>
    change accessValid (s.getReg .x7) 8=true at valid
    change i<2 at inside
    interval_cases i <;> simp [GroupBlock.partialState,GroupBlock.words,ordinaryStep,memoryArgumentsValid,
      memAccess,execInstrBr,signExtend12,valid]
  | duplicate => change i<1 at inside; interval_cases i <;> rfl
  | latch => change i<4 at inside; interval_cases i <;> rfl

theorem group_block_execute (block : GroupBlock) (s : MachineState)
    (here : s.pc=BitVec.ofNat 64 (4096+4*block.start)) (valid : block.Valid s) (fuel : Nat) :
    execute checkerImage (block.words.length+fuel) s false = do
      let result ← execute checkerImage fuel (block.done s) false
      return result.charge block.words.length 0 := by
  have enough : block.start+block.words.length≤221 := by
    cases block <;> simp [GroupBlock.start,GroupBlock.words] <;> omega
  have final : block.done s=block.partialState s block.words.length := by simp [GroupBlock.done,GroupBlock.partialState]
  rw [final]
  apply execute_unit_steps (states := block.partialState s)
  intro i inside
  refine ⟨.base (block.words[i]?.getD .EBREAK),checker_fetch _ (block.start+i) _ (by omega) ?_
    (group_decode _ _ inside),group_ordinary block s i inside valid,?_⟩
  · rw [prefix_pc _ _ _ inside,here,← BitVec.ofNat_add]
    congr 1
    omega
  · cases block with
    | setup => change i<6 at inside; interval_cases i <;> rfl
    | compare n => change i<3 at inside; interval_cases i <;> rfl
    | duplicate => change i<1 at inside; interval_cases i <;> rfl
    | mark => change i<2 at inside; interval_cases i <;> rfl
    | latch => change i<4 at inside; interval_cases i <;> rfl

end TwoPermutationPrototype.Checker
