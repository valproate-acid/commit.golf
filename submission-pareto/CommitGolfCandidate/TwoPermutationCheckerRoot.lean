import CommitGolfCandidate.TwoPermutationCheckerCapFrontier

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
attribute [local simp] Opening.getReg_setMem Opening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem pc_after (s : MachineState) (pc : Word) : (s.setPC pc).pc = pc := rfl

def rootCompareCode (i : Fin 4) : List Instr :=
  [.LD .x29 .x25 (BitVec.ofNat 12 (32+8*i.val)),
   .LD .x30 .x9 (BitVec.ofNat 12 (8*i.val)),
   .BNE .x29 .x30 (BitVec.ofNat 13 (68-12*i.val))]

def rootComparePrefix (state : MachineState) (i : Fin 4) (count : Nat) : MachineState :=
  ((rootCompareCode i).take count).foldl execInstrBr state

def rootCompare (state : MachineState) (i : Fin 4) := rootComparePrefix state i 3

def rootWordMatches (state : MachineState) (i : Fin 4) : Prop :=
  state.getMem (state.getReg .x25 + BitVec.ofNat 64 (32+8*i.val)) =
    state.getMem (state.getReg .x9 + BitVec.ofNat 64 (8*i.val))

instance rootWordMatchesDec (state : MachineState) (i : Fin 4) : Decidable (rootWordMatches state i) :=
  inferInstanceAs (Decidable (_ = _))

theorem execute_root_compare (state : MachineState) (i : Fin 4) (fuel : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(199+3*i.val)))
    (cap : accessValid (state.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true)
    (claim : accessValid (state.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true) :
    execute checkerImage (3+fuel) state false =
      (do let result ← execute checkerImage fuel (rootCompare state i) false
          return result.charge 3 0) := by
  apply execute_unit_steps (states := rootComparePrefix state i)
  intro j bounded
  refine ⟨.base ((rootCompareCode i)[j]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply checker_fetch _ (199+3*i.val+j) _ (by omega)
    · fin_cases i <;> interval_cases j <;>
        simp [rootComparePrefix, rootCompareCode, execInstrBr, pc, MachineState.setPC]
    · fin_cases i <;> interval_cases j <;> rfl
  · fin_cases i <;> interval_cases j <;>
      simp_all [rootComparePrefix, rootCompareCode, execInstrBr, ordinaryStep, memoryArgumentsValid,
        memAccess, signExtend12]
  · interval_cases j <;> rfl

private theorem compare_bne_pc (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).pc = if s.getReg a=s.getReg b then s.pc+4 else s.pc+signExtend13 d := by
  simp only [execInstrBr,bne_iff_ne]
  by_cases eq : s.getReg a=s.getReg b <;> simp [eq]

private theorem compare_bne_reg (s : MachineState) (a b r : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).getReg r=s.getReg r := by simp only [execInstrBr]; split <;> rfl

private theorem compare_bne_mem (s : MachineState) (a b : Reg) (d : BitVec 13) :
    (execInstrBr s (.BNE a b d)).mem=s.mem := by simp only [execInstrBr]; split <;> rfl

private theorem getMem_pc (s : MachineState) (p a : Word) : (s.setPC p).getMem a=s.getMem a := rfl
private theorem getMem_reg (s : MachineState) (r : Reg) (v a : Word) : (s.setReg r v).getMem a=s.getMem a := by cases r <;> rfl
attribute [local simp] getMem_pc getMem_reg

theorem root_compare_post (s : MachineState) (i : Fin 4)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(199+3*i.val))) :
    let t := rootCompare s i
    t.pc=(if rootWordMatches s i then BitVec.ofNat 64 (4096+4*(202+3*i.val)) else 0x1368) ∧
      t.mem=s.mem ∧ ∀ r : Reg, r≠.x29 → r≠.x30 → t.getReg r=s.getReg r := by
  dsimp only
  simp only [rootCompare,rootComparePrefix,rootCompareCode,List.take,List.foldl_cons,List.foldl_nil,
    compare_bne_pc,compare_bne_reg,compare_bne_mem]
  fin_cases i <;> simp [rootWordMatches,execInstrBr,signExtend12,signExtend13,pc]
  all_goals first
    | (refine ⟨rfl, rfl, ?_⟩; intro r m p; simp [Ne.symm m, Ne.symm p])
    | (refine ⟨rfl, ?_⟩; intro r m p; simp [Ne.symm m, Ne.symm p])
    | (intro r m p; simp [Ne.symm m, Ne.symm p])

def rootLength (state : MachineState) := execInstrBr state (.BNE .x21 .x22 80)

theorem execute_root_length (state : MachineState) (pc : state.pc = 0x1318) (fuel : Nat) :
    execute checkerImage (1+fuel) state false =
      (do let next ← execute checkerImage fuel (rootLength state) false
          return next.charge 1 0) := by
  have fetched := checker_fetch state 198 (.BNE .x21 .x22 80) (by decide) pc rfl
  have next : ordinaryStep state (.base (.BNE .x21 .x22 80)) = some (rootLength state) := rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched next]
  rfl

theorem root_length_post (state : MachineState) (pc : state.pc = 0x1318) :
    (rootLength state).pc = (if state.getReg .x21 = state.getReg .x22 then 0x131c else 0x1368) ∧
      (rootLength state).mem = state.mem ∧
      ∀ reg, (rootLength state).getReg reg = state.getReg reg := by
  by_cases length : state.getReg .x21 = state.getReg .x22 <;>
    simp [rootLength, compare_bne_pc, compare_bne_reg, compare_bne_mem, pc, length, signExtend13] <;> rfl

def rejectState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 1).setPC 0x1370

theorem execute_reject (state : MachineState) (pc : state.pc = 0x1368) (fuel : Nat) :
    execute checkerImage (3+fuel) state false = pure ⟨.failure, rejectState state, 3, 0⟩ := by
  let first := (state.setReg .x5 1).setPC 0x136c
  have a := checker_fetch state 218 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := checker_fetch first 219 (.ADDI .x10 .x0 1) (by decide) rfl rfl
  have c := checker_fetch (rejectState state) 220 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 1)) = some (rejectState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, rejectState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl

def acceptState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 0x1354

theorem execute_accept (state : MachineState) (pc : state.pc = 0x134c) (fuel : Nat) :
    execute checkerImage (3+fuel) state false = pure ⟨.success, acceptState state, 3, 0⟩ := by
  let first := (state.setReg .x5 1).setPC 0x1350
  have a := checker_fetch state 211 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := checker_fetch first 212 (.ADDI .x10 .x0 0) (by decide) rfl rfl
  have c := checker_fetch (acceptState state) 213 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 0)) = some (acceptState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, acceptState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl

end TwoPermutationPrototype.Checker
