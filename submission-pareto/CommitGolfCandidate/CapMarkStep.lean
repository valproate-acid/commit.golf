import CommitGolfCandidate.CapOrdinary

/-! One descending occupancy iteration. The ten real instructions load the two
child words, OR their 0/1 marks, store the parent, and decrement the node.
Fetching, memory access validity, and the low-memory frame remain explicit. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capMarkInstructions (marks : Reg) : List Instr :=
  [.SLLI .x30 .x20 4, .ADD .x30 marks .x30,
   .LD .x6 .x30 0, .LD .x7 .x30 8, .OR .x6 .x6 .x7,
   .SLLI .x23 .x20 3, .ADD .x23 marks .x23,
   .SD .x23 .x6 0, .ADDI .x20 .x20 4095, .BNE .x20 .x0 8156]

def capMarkPrefix (marks : Reg) (state : MachineState) (count : Nat) : MachineState :=
  ((capMarkInstructions marks).take count).foldl execInstrBr state

def CapMarkFetched (image : Image) (marks : Reg) (start : Word) : Prop :=
  ∀ state : MachineState, ∀ i < 10, state.pc = start →
    fetch image (capMarkPrefix marks state i) =
      some (.base (((capMarkInstructions marks)[i]?).getD .EBREAK))

private theorem fold_take_next {A S : Type} (step : S → A → S)
    (code : List A) (state : S) (fallback : A) (i : Nat)
    (hi : i < code.length) :
    (code.take (i + 1)).foldl step state =
      step ((code.take i).foldl step state) ((code[i]?).getD fallback) := by
  rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos code i hi,
    Option.getD_some]

theorem cap_mark_prefix_succ (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count < 10) :
    capMarkPrefix marks state (count + 1) =
      execInstrBr (capMarkPrefix marks state count)
        (((capMarkInstructions marks)[count]?).getD .EBREAK) := by
  exact fold_take_next execInstrBr (capMarkInstructions marks) state .EBREAK count
    (by simpa only [capMarkInstructions, List.length_cons, List.length_nil] using bounded)

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x20 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x20 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

private theorem zero_offset (address : Word) :
    address + signExtend12 (0 : BitVec 12) = address := by
  simp [signExtend12]

/-- Only these scratch registers can be changed by a mark iteration. -/
theorem cap_mark_prefix_register (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 10) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧ reg ≠ .x30) :
    (capMarkPrefix marks state count).getReg reg = state.getReg reg := by
  have memory (current : MachineState) (address value : Word) :
      (current.setMem address value).getReg reg = current.getReg reg := by
    cases reg <;> rfl
  have step (current : MachineState) (i : Nat) (hi : i < 10) :
      (execInstrBr current (((capMarkInstructions marks)[i]?).getD .EBREAK)).getReg reg =
        current.getReg reg := by
    interval_cases i <;>
      simp only [capMarkInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some,
        execInstrBr, MachineState.getReg_setPC, memory,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.1),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2.1),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2.2.2)]
    split <;> exact MachineState.getReg_setPC
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [cap_mark_prefix_succ marks state count (by omega), step _ count (by omega)]
      exact ih (by omega)

/-- This bridge charges ten ordinary cycles and no queries. Its access premises
are checked in the actual prefix states, including the store destination. -/
theorem cap_mark_execute (image : Image) (marks : Reg) (start : Word)
    (fetched : CapMarkFetched image marks start) (state : MachineState)
    (pc : state.pc = start)
    (leftValid : accessValid ((capMarkPrefix marks state 2).getReg .x30) 8 = true)
    (rightValid : accessValid ((capMarkPrefix marks state 3).getReg .x30 + 8) 8 = true)
    (parentValid : accessValid ((capMarkPrefix marks state 7).getReg .x23) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (10 + fuel) state allowCoins =
      (do let result ← execute image fuel (capMarkPrefix marks state 10) allowCoins
          return result.charge 10 0) := by
  apply execute_unit_steps (states := capMarkPrefix marks state)
  intro i hi
  refine ⟨.base (((capMarkInstructions marks)[i]?).getD .EBREAK),
    fetched state i hi pc, ?_, ?_⟩
  · have valid : memoryArgumentsValid (capMarkPrefix marks state i)
        (((capMarkInstructions marks)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capMarkInstructions, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, memoryArgumentsValid,
          memAccess]
      · simpa only [zero_offset] using leftValid
      · exact rightValid
      · simpa only [zero_offset] using parentValid
    rw [cap_mark_prefix_succ marks state i hi]
    interval_cases i <;>
      simp only [capMarkInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte]
  · interval_cases i <;> rfl

/-- The first seven instructions only change registers and PC. -/
theorem cap_mark_prefix_memory (marks : Reg) (state : MachineState) (count : Nat)
    (bounded : count ≤ 7) :
    (capMarkPrefix marks state count).mem = state.mem := by
  have step (current : MachineState) (i : Nat) (hi : i < 7) :
      (execInstrBr current (((capMarkInstructions marks)[i]?).getD .EBREAK)).mem =
        current.mem := by
    interval_cases i <;>
      simp only [capMarkInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, execInstrBr,
        MachineState.setReg, MachineState.setPC]
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [cap_mark_prefix_succ marks state count (by omega), step _ count (by omega)]
      exact ih (by omega)

/-- A checked low parent store preserves all later ABI input bytes. -/
theorem cap_mark_frame (marks : Reg) (state reference : MachineState)
    (low : ((capMarkPrefix marks state 7).getReg .x23).toNat < 32768)
    (frame : CapHighBytes state reference) :
    CapHighBytes (capMarkPrefix marks state 10) reference := by
  have before : CapHighBytes (capMarkPrefix marks state 7) reference :=
    cap_high_bytes_memory state _ reference (cap_mark_prefix_memory marks state 7 (by omega))
      frame
  have stored := cap_mark_store_frame (capMarkPrefix marks state 7) reference low before
  apply cap_high_bytes_memory (capMarkStoreState (capMarkPrefix marks state 7)) _ reference
    ?_ stored
  rw [cap_mark_prefix_succ marks state 9 (by omega)]
  simp only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, branch_memory]
  rw [cap_mark_prefix_succ marks state 8 (by omega)]
  simp only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, execInstrBr, MachineState.setPC,
    MachineState.setReg]
  rw [cap_mark_prefix_succ marks state 7 (by omega)]
  simp only [capMarkInstructions, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, execInstrBr, capMarkStoreState,
    zero_offset]

end CommitGolfCandidate
