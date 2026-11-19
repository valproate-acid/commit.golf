import CommitGolfCandidate.TwoPermutationHidingProgramming
import CommitGolfCandidate.HidingReprogram

/-! The observer may use both oracle directions and adapt every query. The
distance from programming hidden rows is charged on the original experiment. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate

local instance discreteSpace {α : Type} : MeasurableSpace α := ⊤

def fixedOracle (compress : Compression) (p : BiPermutation Block) : Oracle :=
  ⟨compress, (BiPermutation.equiv Block).symm p⟩

def marksReferencePair (p : BiPermutation Block) (rows : List (Block × Block)) : World.Domain → Bool
  | .inl _ => false
  | .inr (.inl _) => false
  | .inr (.inr (.inl input)) =>
    rows.any fun row => decide (input = row.1 ∨ p.forward input = row.2)
  | .inr (.inr (.inr output)) =>
    rows.any fun row => decide (p.inverse output = row.1 ∨ output = row.2)

private theorem unchanged_of_unmarked (compress : Compression) (p : BiPermutation Block)
    (rows : List (Block × Block)) (query : World.Domain) (unmarked : marksReferencePair p rows query = false) :
    (fixedOracle compress p).world query = (fixedOracle compress (p.programRows rows)).world query := by
  rcases query with coins | (input | (input | output))
  · rfl
  · rfl
  · have disjoint (row) (present : row ∈ rows) :
        input ≠ row.1 ∧ p.forward input ≠ row.2 := by
      apply not_or.mp
      intro hit
      have marked : marksReferencePair p rows (.inr (.inr (.inl input))) = true :=
        List.any_eq_true.mpr ⟨row, present, decide_eq_true hit⟩
      rw [marked] at unmarked
      contradiction
    change (pure (p.forward input) : ProbComp Block) = pure ((p.programRows rows).forward input)
    rw [p.program_rows_forward_unchanged rows input disjoint]
  · have disjoint (row) (present : row ∈ rows) :
        p.inverse output ≠ row.1 ∧ output ≠ row.2 := by
      apply not_or.mp
      intro hit
      have marked : marksReferencePair p rows (.inr (.inr (.inr output))) = true :=
        List.any_eq_true.mpr ⟨row, present, decide_eq_true hit⟩
      rw [marked] at unmarked
      contradiction
    change (pure (p.inverse output) : ProbComp Block) = pure ((p.programRows rows).inverse output)
    rw [p.program_rows_inverse_unchanged rows output disjoint]

theorem programming_distance_le_reference_hit (compress : Compression) (p : BiPermutation Block)
    (rows : List (Block × Block)) {α : Type} (computation : OracleComp World α) :
    measureTVDist (fixedOracleRun (fixedOracle compress p) computation)
      (fixedOracleRun (fixedOracle compress (p.programRows rows)) computation) ≤
    (Pr{let result ← flaggedRun (fixedOracle compress p) (marksReferencePair p rows) computation}[
      result.2.2 = true]).toReal :=
  oracle_change_distance_le_hit _ _ _ (unchanged_of_unmarked compress p rows) computation

end TwoPermutationPrototype.Sampling
