import CommitGolfCandidate.TwoPermutationCheckerLowerTrace

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- The concrete lower loop reaches this state after the given recorded
compression rows. Its step and cycle amounts account for the chosen branches. -/
structure LowerResult where
  state : MachineState
  rows : List PublicRow
  steps : Nat
  cycles : Nat

def lowerRun (oracle : Oracle) : Nat → MachineState → LowerResult
  | 0, state => ⟨state, [], 0, 0⟩
  | left+1, state =>
    let first := (checkEvaluation oracle (recordRows (lowerQuery state))).1
    let tail := lowerRun oracle left first.1
    ⟨tail.state, first.2 ++ tail.rows, lowerPreparationSteps state+7+tail.steps,
      lowerPreparationSteps state+14+tail.cycles⟩

private theorem lower_steps_one (state : MachineState) :
    lowerPreparationSteps state+7 ≤ 26 := by unfold lowerPreparationSteps; split <;> omega

theorem lower_run_steps (oracle : Oracle) (left : Nat) (state : MachineState) :
    (lowerRun oracle left state).steps ≤ 26*left := by
  induction left generalizing state with
  | zero => exact Nat.le_refl 0
  | succ left ih =>
    have tail := ih (checkEvaluation oracle (recordRows (lowerQuery state))).1.1
    have one := lower_steps_one state
    unfold lowerRun
    dsimp only
    omega

theorem check_recorded_bind {α β : Type} (oracle : Oracle) (first : OracleComp World α)
    (next : α → OracleComp World β) :
    checkEvaluation oracle (recordRows (first >>= next)) =
      let earlier := checkEvaluation oracle (recordRows first)
      let later := checkEvaluation oracle (recordRows (next earlier.1.1))
      ((later.1.1, earlier.1.2 ++ later.1.2), earlier.2 + later.2) := by
  rw [record_rows_bind]
  simp only [check_evaluation_bind, check_evaluation_pure]
  rfl

theorem check_recorded_map {α β : Type} (oracle : Oracle) (first : OracleComp World α)
    (f : α → β) :
    checkEvaluation oracle (recordRows (f <$> first)) =
      ((f (checkEvaluation oracle (recordRows first)).1.1,
          (checkEvaluation oracle (recordRows first)).1.2),
        (checkEvaluation oracle (recordRows first)).2) := by
  rw [map_eq_bind_pure_comp, check_recorded_bind]
  simp [record_rows_pure, check_evaluation_pure, Function.comp_def]

attribute [local irreducible] execute lowerRun checkEvaluation lowerReply readBuffer

theorem execute_lower_run {state : MachineState} {node proof : Nat}
    (oracle : Oracle) (left : Nat) (bounded : left ≤ 16)
    (ready : left ≠ 0 → LowerReady state node proof) (nodeBound : node < 2^64)
    (counter : state.getReg .x29 = BitVec.ofNat 64 left)
    (room : proof+4*left ≤ 2^33) (fuel : Nat) :
    let lower := lowerRun oracle left state
    let observed := checkEvaluation oracle (recordRows (execute checkerImage fuel lower.state false))
    checkEvaluation oracle (recordRows (execute checkerImage (lower.steps+fuel) state false)) =
      ((observed.1.1.charge lower.cycles left, lower.rows ++ observed.1.2), left + observed.2) := by
  induction left generalizing state node proof with
  | zero => simp [lowerRun, Execution.charge]
  | succ left ih =>
    have current := ready (by omega)
    have row := lower_recorded_query oracle current nodeBound
    dsimp only at row
    rw [lowerRun, row]
    dsimp only
    let pair := pathPair node (readBuffer state 12288 32) (readBuffer state (8*proof) 32)
    let reply := oracle.compression pair
    let middle := lowerReply state reply
    let tail := lowerRun oracle left middle
    have geometry := lower_reply_geometry current nodeBound reply left counter (by omega)
    have nextReady (more : left ≠ 0) : LowerReady middle (node/2) (proof+4) :=
      lower_reply_ready current nodeBound reply left counter (by omega) (by omega) (by omega)
    have tailRun := ih (state := middle) (node := node/2) (proof := proof+4) (by omega)
      nextReady (by omega) geometry.2.2.1 (by omega)
    rw [show lowerPreparationSteps state+7+tail.steps+fuel =
        lowerPreparationSteps state+7+(tail.steps+fuel) by omega, execute_lower_level current]
    rw [check_recorded_bind, row]
    dsimp only
    erw [show (do
        let result ← execute checkerImage (tail.steps+fuel) middle false
        pure (result.charge (lowerPreparationSteps state+14) 1)) =
        (fun result => result.charge (lowerPreparationSteps state+14) 1) <$>
          execute checkerImage (tail.steps+fuel) middle false from bind_pure_comp _ _]
    rw [check_recorded_map, tailRun]
    simp only [Execution.charge, List.append_assoc, Nat.add_assoc, Nat.add_left_comm 1 left]
    rfl

theorem lower_run_trace {state : MachineState} {node proof : Nat} (oracle : Oracle)
    (left : Nat) (bounded : left ≤ 16) (ready : left ≠ 0 → LowerReady state node proof)
    (nodeBound : node < 2^64) (counter : state.getReg .x29 = BitVec.ofNat 64 left)
    (pointer0 : state.getReg .x21 = wordAddress proof) (node0 : state.getReg .x6 = BitVec.ofNat 64 node)
    (room : proof+4*left ≤ 2^33) :
    let lower := lowerRun oracle left state
    RecordedPath lower.rows node left (readBuffer state 12288 32) (readBuffer lower.state 12288 32) ∧
    lower.state.getReg .x21 = wordAddress (proof+4*left) ∧
    lower.state.getReg .x6 = BitVec.ofNat 64 (node/2^left) ∧
    lower.state.getReg .x29 = 0 ∧ (left ≠ 0 → lower.state.pc = 0x11d8) := by
  induction left generalizing state node proof with
  | zero =>
    simp only [lowerRun, Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one]
    exact ⟨.done node _, pointer0, node0, counter, by omega⟩
  | succ left ih =>
    have current := ready (by omega)
    have row := lower_recorded_query oracle current nodeBound
    dsimp only at row
    rw [lowerRun, row]
    dsimp only
    let pair := pathPair node (readBuffer state 12288 32) (readBuffer state (8*proof) 32)
    let reply := oracle.compression pair
    let middle := lowerReply state reply
    have geometry := lower_reply_geometry current nodeBound reply left counter (by omega)
    have digest := lower_reply_digest state reply
    by_cases zero : left = 0
    · subst left
      simp only [lowerRun, List.append_nil, Nat.mul_one, Nat.pow_one]
      refine ⟨?_, geometry.1, geometry.2.1, geometry.2.2.1, fun _ => geometry.2.2.2⟩
      change RecordedPath [PublicRow.compression pair reply] node 1 (readBuffer state 12288 32)
        (readBuffer middle 12288 32)
      rw [digest]
      exact .step (sibling := readBuffer state (8*proof) 32) (by simp [pair, reply]) (.done _ _)
    · have nextReady : LowerReady middle (node/2) (proof+4) :=
        lower_reply_ready current nodeBound reply left counter (by omega) (by omega) (by omega)
      obtain ⟨path, pointer, heap, ended, pc⟩ :=
        ih (state := middle) (node := node/2) (proof := proof+4) (by omega)
          (fun _ => nextReady) (by omega) geometry.2.2.1 geometry.1 geometry.2.1 (by omega)
      refine ⟨?_, ?_, ?_, ended, fun _ => pc zero⟩
      · rw [digest] at path
        exact .step (sibling := readBuffer state (8*proof) 32) (by simp [pair, reply])
          (path.mono (fun _ hit => List.mem_append_right _ hit))
      · simpa only [show proof+4+4*left = proof+4*(left+1) by omega] using pointer
      · simpa only [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2] using heap

theorem lower_run_frame {state : MachineState} {node proof : Nat} (oracle : Oracle)
    (left : Nat) (bounded : left ≤ 16) (ready : left ≠ 0 → LowerReady state node proof)
    (nodeBound : node < 2^64) (counter : state.getReg .x29 = BitVec.ofNat 64 left)
    (room : proof+4*left ≤ 2^33) :
    let lower := lowerRun oracle left state
    (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r ≠ .x6 → r ≠ .x21 → r ≠ .x29 → r ≠ .x31 → r ≠ .x7 →
      lower.state.getReg r = state.getReg r) ∧
    (∀ word < 2^61, (word < 1536 ∨ 1540 ≤ word) → (word < 1568 ∨ 1576 ≤ word) →
      memoryView lower.state word = memoryView state word) := by
  induction left generalizing state node proof with
  | zero => simp [lowerRun]
  | succ left ih =>
    have current := ready (by omega)
    have row := lower_recorded_query oracle current nodeBound
    dsimp only at row
    rw [lowerRun, row]
    dsimp only
    let reply := oracle.compression (pathPair node (readBuffer state 12288 32)
      (readBuffer state (8*proof) 32))
    let middle := lowerReply state reply
    have regs := lower_reply_geometry current nodeBound reply left counter (by omega)
    have nextReady (more : left ≠ 0) : LowerReady middle (node/2) (proof+4) :=
      lower_reply_ready current nodeBound reply left counter (by omega) (by omega) (by omega)
    obtain ⟨afterRegs, afterMem⟩ := ih (state := middle) (node := node/2) (proof := proof+4)
      (by omega) nextReady (by omega) regs.2.2.1 (by omega)
    constructor
    · intro r input output nodeReg proofReg counterReg temp odd
      exact (afterRegs r input output nodeReg proofReg counterReg temp odd).trans
        (lower_reply_register state reply r input output nodeReg proofReg counterReg temp odd)
    · intro word limit digestOutside pairOutside
      exact (afterMem word limit digestOutside pairOutside).trans
        (lower_reply_frame current reply word limit digestOutside pairOutside)

end TwoPermutationPrototype.Checker
