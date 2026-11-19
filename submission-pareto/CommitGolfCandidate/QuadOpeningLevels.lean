import CommitGolfCandidate.QuadOpeningLevel

/-! The eleven levels of one penta record. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- Levels `0 … count-1`. -/
def levelsRun (count : Nat) (state : MachineState) : MachineState :=
  (List.range count).foldl (fun current k => levelRun k current) state

theorem levels_run_succ (count : Nat) (state : MachineState) :
    levelsRun (count+1) state = levelRun count (levelsRun count state) := by
  simp only [levelsRun, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem levels_run (init : MachineState) (positions : Positions) (o : Nat)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH) (state : MachineState)
    (at_ : LevelAt init state positions o 0) :
    ∀ count ≤ 11,
      Runs state (levelsRun count state) (46*count) (52*count) ∧ LevelAt init (levelsRun count state) positions o count ∧
      ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 →
        r ≠ .x31 → (levelsRun count state).getReg r = state.getReg r := by
  intro count
  induction count with
  | zero => intro _; exact ⟨Runs.zero state, at_, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ count ih =>
    intro le
    obtain ⟨run, at', regs⟩ := ih (by omega)
    obtain ⟨run₂, at₂, regs₂⟩ := level_step init (levelsRun count state) positions o count (by omega)
      inside ordinal at'
    rw [levels_run_succ]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), at₂, ?_⟩
    intro r a b c d e f g h l m
    exact (regs₂ r a b c d e f g h l m).trans (regs r a b c d e f g h l m)

end TwoPermutationPrototype.QuadOpening
