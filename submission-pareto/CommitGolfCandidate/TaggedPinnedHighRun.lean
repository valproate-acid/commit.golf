import CommitGolfCandidate.TaggedPinnedHighStep

namespace TwoPermutationPrototype.Sampling
open OracleComp CommitGolfCandidate
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

local instance pinnedHighRunDiscrete {α : Type} : MeasurableSpace α := ⊤

abbrev PinnedHighPlan := List (BitVec 1344) → Block

def pinnedLiftPlan (plan : PinnedHighPlan) : InputPlan :=
  fun replies => plan (replies.map pinnedOutputTail)

noncomputable def runPinnedHigh {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) : List PinnedHighPlan → ProbComp (List (BitVec 1344) × PinnedHighCache base)
  | [] => pure (answers, cache)
  | plan :: plans => do
      let (answer, next) ← pinnedHighStep cache slot (plan answers)
      runPinnedHigh next (slot + 1) (answer :: answers) plans

noncomputable def runPinnedFull (cache : Cache) (answers : List (BitVec 1344)) :
    List PinnedHighPlan → ProbComp (List (BitVec 1344) × Cache)
  | [] => pure (answers, cache)
  | plan :: plans => do
      let (answer, next) ← pinnedRestrictedForward cache (plan answers)
      runPinnedFull next (pinnedOutputTail answer :: answers) plans

theorem pinned_full_from_restricted {α : Type} (cache : Cache) (answers : List Block)
    (plans : List PinnedHighPlan) (next : List (BitVec 1344) → Cache → ProbComp α) :
    (runPinnedRestricted cache answers (plans.map pinnedLiftPlan) >>= fun result =>
      next (result.1.map pinnedOutputTail) result.2) =
    (runPinnedFull cache (answers.map pinnedOutputTail) plans >>= fun result => next result.1 result.2) := by
  induction plans generalizing cache answers with
  | nil => simp [runPinnedRestricted, runPinnedFull]
  | cons plan rest ih =>
    simp only [List.map_cons, runPinnedRestricted, runPinnedFull, pinnedLiftPlan, bind_assoc]
    apply bind_congr
    rintro ⟨answer, updated⟩
    simp only [← List.map_cons]
    exact ih updated (answer :: answers)

def samplePinnedLows : Nat → ProbComp (List (BitVec 256))
  | 0 => pure []
  | n + 1 => do
      let low ← $ᵗ BitVec 256
      let rest ← samplePinnedLows n
      pure (low :: rest)

def pinnedPlaceLows (low : PinnedLowTape) (slot : Nat) : List (BitVec 256) → PinnedLowTape
  | [] => low
  | next :: rest => pinnedPlaceLows (Function.update low slot next) (slot+1) rest

/-- The honest high-only transcript is sampled first. Every low output value
can be sampled afterward, in its original slot, with the same distribution. -/
theorem pinned_full_high_low_equivalence {α : Type} {base : Cache}
    (cache : PinnedHighCache base) (slot : Nat) (low : PinnedLowTape)
    (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (slots : ∀ row ∈ cache.added, row.slot < slot)
    (room : cache.zero.entries.length + plans.length ≤ 2 ^ 121)
    (next : List (BitVec 1344) → Cache → ProbComp α) :
    (do let result ← runPinnedFull (cache.realize low) answers plans
        next result.1 result.2) =ᵈ
    (do let result ← runPinnedHigh cache slot answers plans
        let draws ← samplePinnedLows plans.length
        next result.1 (result.2.realize (pinnedPlaceLows low slot draws))) := by
  induction plans generalizing cache slot low answers with
  | nil => simp [runPinnedFull, runPinnedHigh, samplePinnedLows, pinnedPlaceLows]
  | cons plan rest ih =>
    let input := plan answers
    let finish (updated : Cache) (answer : BitVec 1344) :=
      runPinnedFull updated (answer :: answers) rest >>= fun final => next final.1 final.2
    have roomHere : cache.zero.entries.length ≤ 2 ^ 121 := by omega
    simp only [runPinnedFull, bind_assoc]
    apply (pinned_split_high_step cache low slot input slots roomHere (fun answer updated => finish updated answer)).trans
    simp only [runPinnedHigh, List.length_cons, samplePinnedLows, bind_assoc, pure_bind]
    apply EvalDistEq.bind_congr_of_support
    intro result reached
    let drawHigh := runPinnedHigh result.2 (slot+1) (result.1 :: answers) rest
    have shape := pinned_high_step_support cache slot input result reached
    have slotsNext : ∀ row ∈ result.2.added, row.slot < slot+1 := by
      intro row found
      rcases shape with nochange | ⟨new, _, _, tag, added⟩
      · rw [nochange] at found
        exact (slots row found).trans (Nat.lt_succ_self _)
      · rw [added] at found
        rcases List.mem_cons.mp found with rfl | tail
        · rw [tag]; exact Nat.lt_succ_self _
        · exact (slots row tail).trans (Nat.lt_succ_self _)
    have roomNext : result.2.zero.entries.length + rest.length ≤ 2 ^ 121 := by
      rw [PinnedHighCache.zero, result.2.entries_length]
      rw [PinnedHighCache.zero, cache.entries_length, List.length_cons] at room
      rcases shape with nochange | ⟨new, _, _, _, added⟩
      · rw [nochange]; omega
      · rw [added, List.length_cons]; omega
    trans (do let bit ← $ᵗ BitVec 256
              let final ← drawHigh
              let later ← samplePinnedLows rest.length
              next final.1 (final.2.realize (pinnedPlaceLows (Function.update low slot bit) (slot+1) later)))
    · apply EvalDistEq.bind_right
      intro bit
      exact ih result.2 (slot+1) (Function.update low slot bit) (result.1 :: answers) slotsNext roomNext
    · exact (EvalDistEq.of_evalDist_eq (distribution_bind_comm drawHigh ($ᵗ BitVec 256)
        (fun final bit => do
          let later ← samplePinnedLows rest.length
          next final.1 (final.2.realize (pinnedPlaceLows (Function.update low slot bit) (slot+1) later))))).symm

end TwoPermutationPrototype.Sampling
