import CommitGolfCandidate.TwoPermutationHidingResample
import CommitGolfCandidate.Probability

/-! Each honest input may depend on its previous replies. Couple the entire
sequence with unrestricted independent proposals and charge the first conflict. -/
namespace TwoPermutationPrototype.Sampling
open OracleComp CommitGolfCandidate

abbrev InputPlan := List Block → Block

local instance sequenceDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

def runPlanned {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (p : BiPermutation Block) (answers : List Block) : List InputPlan → ProbComp α
  | [] => next answers p
  | plan :: rest => runPlanned next p (p.forward (plan answers) :: answers) rest

def runProposed {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (p : BiPermutation Block) (answers : List Block) : List InputPlan → ProbComp α
  | [] => next answers p
  | plan :: rest => do
      let proposal ← $ᵗ Block
      runProposed next (p.program (plan answers) proposal) (proposal :: answers) rest

noncomputable def proposedConflict (cache : Cache) (answers : List Block) :
    List InputPlan → ProbComp Bool
  | [] => pure false
  | plan :: rest => by
      classical
      exact if fresh : UnusedInput cache.entries (plan answers) then do
        let proposal ← $ᵗ Block
        if unused : UnusedOutput cache.entries proposal then
          proposedConflict (cache.extendForward (plan answers) fresh ⟨proposal, unused⟩)
            (proposal :: answers) rest
        else pure true
      else pure true

private theorem initial_draw_exchange {α : Type} (cache : Cache)
    (next : Block → Completion cache.entries → ProbComp α) :
    (do let p ← cache.sample; let y ← $ᵗ Block; next y p) =ᵈ
      (do let y ← $ᵗ Block; let p ← cache.sample; next y p) := by
  have swapped := distribution_bind_comm ($ᵗ Block) cache.sample next
  exact (EvalDistEq.of_evalDist_eq swapped).symm

theorem distance_averaged_event {ι α β : Type} (sample : ProbComp ι)
    (left right : ι → ProbComp α) (tagged : ι → ProbComp β) (event : β → Prop)
    (each : ∀ draw, measureETVDist (left draw) (right draw) ≤ Pr{let result ← tagged draw}[event result]) :
    measureETVDist (sample >>= left) (sample >>= right) ≤ Pr{let result ← sample >>= tagged}[event result] := by
  rw [prEvent_bind_eq_tsum]
  exact (measureETVDist_bind_left_le_tsum sample left right).trans
    (ENNReal.tsum_le_tsum fun draw => mul_le_mul_of_nonneg_left (each draw) zero_le)

/-- The whole private forward-query sequence can use independent full-domain
proposals instead of real replies, at a statistical cost bounded by the
probability of a repeated input or output in that proposal sequence. -/
theorem planned_vs_proposed_distance {α : Type}
    (next : List Block → BiPermutation Block → ProbComp α)
    (cache : Cache) (answers : List Block) (plans : List InputPlan) :
    measureETVDist
      (do let p ← cache.sample; runPlanned next p.val answers plans)
      (do let p ← cache.sample; runProposed next p.val answers plans) ≤
      Pr{let hit ← proposedConflict cache answers plans}[hit = true] := by
  classical
  induction plans generalizing cache answers with
  | nil => simp [runPlanned, runProposed, proposedConflict]
  | cons plan rest ih =>
    let input := plan answers
    by_cases fresh : UnusedInput cache.entries input
    · let : SampleableType (RemainingOutputs cache.entries) := cache.forwardSampler input fresh
      let realTail (answer : RemainingOutputs cache.entries) : ProbComp α := do
        let p ← (cache.extendForward input fresh answer).sample
        runPlanned next p.val (answer.val :: answers) rest
      let real (proposal : Block) : ProbComp α := do
        let fallback ← $ᵗ RemainingOutputs cache.entries
        realTail (repairDraw (UnusedOutput cache.entries) proposal fallback)
      let ideal (proposal : Block) : ProbComp α := do
        let p ← cache.sample
        runProposed next (p.val.program input proposal) (proposal :: answers) rest
      let flag (proposal : Block) : ProbComp Bool :=
        if accepted : UnusedOutput cache.entries proposal then
          proposedConflict (cache.extendForward input fresh ⟨proposal, accepted⟩) (proposal :: answers) rest
        else pure true
      have read := cache.forward_step_eq input
        (fun answer perm => runPlanned next perm (answer :: answers) rest)
      unfold PermutationCache.forward at read
      simp only [fresh, dite_true, bind_assoc, pure_bind] at read
      have left : (do let p ← cache.sample; runPlanned next p.val answers (plan :: rest)) =ᵈ
          (($ᵗ Block) >>= real) :=
        read.trans (repair_uniform (UnusedOutput cache.entries) realTail).symm
      have right : (do let p ← cache.sample; runProposed next p.val answers (plan :: rest)) =ᵈ
          (($ᵗ Block) >>= ideal) :=
        initial_draw_exchange cache (fun proposal p =>
          runProposed next (p.val.program input proposal) (proposal :: answers) rest)
      have tag : proposedConflict cache answers (plan :: rest) = (($ᵗ Block) >>= flag) := by
        simp only [proposedConflict, ← show input = plan answers from rfl, fresh, dite_true, flag]
      rw [tag]
      unfold measureETVDist
      rw [left.evalDist_eq, right.evalDist_eq]
      change measureETVDist (($ᵗ Block) >>= real) (($ᵗ Block) >>= ideal) ≤ _
      apply distance_averaged_event ($ᵗ Block) real ideal flag (· = true)
      intro proposal
      by_cases accepted : UnusedOutput cache.entries proposal
      · let answer : RemainingOutputs cache.entries := ⟨proposal, accepted⟩
        let updated := cache.extendForward input fresh answer
        have leftTail : real proposal =ᵈ realTail answer := by
          dsimp only [real]
          simp only [repairDraw, accepted, dite_true]
          exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)
        have rightTail : ideal proposal =ᵈ (do let p ← updated.sample
                                               runProposed next p.val (proposal :: answers) rest) :=
          program_uniform_completion cache input fresh answer
            (fun p => runProposed next p (proposal :: answers) rest)
        unfold measureETVDist
        rw [leftTail.evalDist_eq, rightTail.evalDist_eq]
        dsimp only [flag]
        simp only [accepted, dite_true]
        exact ih updated (proposal :: answers)
      · simpa only [flag, accepted, dite_false, prEvent_pure, ite_true] using
          measureETVDist_le_one (real proposal) (ideal proposal)
    · have flag : proposedConflict cache answers (plan :: rest) = pure true := by
        simp only [proposedConflict, ← show input = plan answers from rfl, fresh, dite_false]
      rw [flag]
      simpa using measureETVDist_le_one
        (cache.sample >>= fun p => runPlanned next p.val answers (plan :: rest))
        (cache.sample >>= fun p => runProposed next p.val answers (plan :: rest))

end TwoPermutationPrototype.Sampling
