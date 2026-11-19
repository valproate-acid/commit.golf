import CommitGolfCandidate.TwoPermutationPackedCapFetch
import CommitGolfCandidate.TwoPermutationCheckerLowerRun

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_recorded_bind check_recorded_map)

/-- An exact contiguous machine segment, observed with genuine oracle replies.
Empty rows distinguish ordinary instructions from public calls in composition. -/
structure Segment (oracle : Oracle) (before after : MachineState) where
  rows : List PublicRow
  steps : Nat
  cycles : Nat
  checked : ∀ fuel,
    let next := checkEvaluation oracle (recordRows (execute packedImage fuel after false))
    checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false)) =
      ((next.1.1.charge cycles rows.length, rows ++ next.1.2), rows.length + next.2)

def Segment.refl (oracle : Oracle) (state : MachineState) : Segment oracle state state :=
  ⟨[], 0, 0, by intro fuel; simp [Execution.charge]⟩

def Segment.append {oracle : Oracle} {before middle after : MachineState}
    (first : Segment oracle before middle) (rest : Segment oracle middle after) : Segment oracle before after where
  rows := first.rows ++ rest.rows
  steps := first.steps + rest.steps
  cycles := first.cycles + rest.cycles
  checked := by
    intro fuel
    dsimp only
    rw [Nat.add_assoc, first.checked, rest.checked]
    simp [Execution.charge, List.length_append, List.append_assoc, Nat.add_assoc]

def Segment.ordinary (oracle : Oracle) {before after : MachineState} (steps cycles : Nat)
    (run : ∀ fuel, execute packedImage (steps+fuel) before false =
      (do let result ← execute packedImage fuel after false
          return result.charge cycles 0)) : Segment oracle before after where
  rows := []
  steps := steps
  cycles := cycles
  checked := by
    intro fuel
    dsimp only
    rw [run, bind_pure_comp, check_recorded_map]
    simp

def Segment.query (oracle : Oracle) {before after : MachineState} (steps cycles : Nat)
    (call : OracleComp World MachineState) (row : PublicRow)
    (run : ∀ fuel, execute packedImage (steps+fuel) before false =
      (do let middle ← call
          let result ← execute packedImage fuel middle false
          return result.charge cycles 1))
    (record : checkEvaluation oracle (recordRows call) = ((after,[row]),1)) :
    Segment oracle before after where
  rows := [row]
  steps := steps
  cycles := cycles
  checked := by
    intro fuel
    dsimp only
    rw [run, check_recorded_bind, record]
    simp only [bind_pure_comp, check_recorded_map, List.length_singleton]

end TwoPermutationPrototype.Packed.Checker
