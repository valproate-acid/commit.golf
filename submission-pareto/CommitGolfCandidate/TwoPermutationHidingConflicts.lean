import CommitGolfCandidate.TwoPermutationHidingSequence

/-! Expose the whole independent proposal tape even when its first conflicting
row occurs early. Collision costs depend on the original cache and plan length. -/
namespace TwoPermutationPrototype.Sampling
open OracleComp
set_option exponentiation.threshold 2048

def sampleProposalTape : Nat → ProbComp (List Block)
  | 0 => pure []
  | count + 1 => do
      let first ← $ᵗ Block
      let rest ← sampleProposalTape count
      pure (first :: rest)

def plannedRows (answers : List Block) : List InputPlan → List Block → List Row
  | plan :: rest, proposal :: tail =>
    (plan answers, proposal) :: plannedRows (proposal :: answers) rest tail
  | _, _ => []

noncomputable def rowListConflict (known : List Row) : List Row → Bool
  | [] => false
  | row :: rest => by
      classical
      exact if UnusedInput known row.1 ∧ UnusedOutput known row.2 then
        rowListConflict (row :: known) rest
      else true

noncomputable def outputConflict (known : List Block) : List Block → Bool
  | [] => false
  | output :: rest => if output ∈ known then true else outputConflict (output :: known) rest

theorem rowListConflict_false {known rows : List Row}
    (distinct : (rows.map Prod.fst).Nodup)
    (unseen : ∀ row ∈ rows, UnusedInput known row.1)
    (clean : outputConflict (known.map Prod.snd) (rows.map Prod.snd) = false) :
    rowListConflict known rows = false := by
  classical
  induction rows generalizing known with
  | nil => rfl
  | cons row rest ih =>
    have input : UnusedInput known row.1 := unseen row (by simp)
    have output : UnusedOutput known row.2 := by
      intro old earlier equal
      have seen : row.2 ∈ known.map Prod.snd := List.mem_map.mpr ⟨old, earlier, equal⟩
      simp [outputConflict, seen] at clean
    have tailClean : outputConflict ((row :: known).map Prod.snd) (rest.map Prod.snd) = false := by
      change outputConflict (row.2 :: known.map Prod.snd) (rest.map Prod.snd) = false
      simpa [outputConflict, show row.2 ∉ known.map Prod.snd by
        intro present
        obtain ⟨old, earlier, equal⟩ := List.mem_map.mp present
        exact output old earlier equal] using clean
    have separated := List.nodup_cons.mp (show (row.1 :: rest.map Prod.fst).Nodup from distinct)
    simp only [rowListConflict, input, output, and_self, ite_true]
    apply ih separated.2 _ tailClean
    intro next later old knownOld equal
    rcases List.mem_cons.mp knownOld with head | earlier
    · subst old
      exact separated.1 (List.mem_map.mpr ⟨next, later, equal.symm⟩)
    · exact unseen next (by simp [later]) old earlier equal

theorem proposed_conflict_from_full_tape (cache : Cache) (answers : List Block) (plans : List InputPlan) :
    proposedConflict cache answers plans =ᵈ
      ((fun tape => rowListConflict cache.entries (plannedRows answers plans tape)) <$>
        sampleProposalTape plans.length) := by
  classical
  induction plans generalizing cache answers with
  | nil => simp [proposedConflict, sampleProposalTape, plannedRows, rowListConflict]
  | cons plan rest ih =>
    by_cases fresh : UnusedInput cache.entries (plan answers)
    · simp only [proposedConflict, fresh, dite_true, List.length_cons, sampleProposalTape, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      apply EvalDistEq.bind_right
      intro proposal
      simp only [plannedRows, rowListConflict, fresh, true_and]
      by_cases unused : UnusedOutput cache.entries proposal
      · simp only [unused, dite_true, ite_true]
        have inserted :
            (cache.extendForward (plan answers) fresh ⟨proposal, unused⟩).entries =
              (plan answers, proposal) :: cache.entries := rfl
        simpa only [map_eq_bind_pure_comp, Function.comp_def, inserted] using
          ih (cache.extendForward (plan answers) fresh ⟨proposal, unused⟩) (proposal :: answers)
      · simp only [unused, dite_false, ite_false]
        let : MeasurableSpace Bool := ⊤
        exact (EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)).symm
    · simp only [proposedConflict, fresh, dite_false, List.length_cons, sampleProposalTape, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      symm
      trans (($ᵗ Block) >>= fun _ => pure true)
      · apply EvalDistEq.bind_right
        intro proposal
        simp only [plannedRows, rowListConflict, fresh, false_and, ite_false]
        let : MeasurableSpace Bool := ⊤
        exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)
      · let : MeasurableSpace Bool := ⊤
        exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const _ _)

private theorem uniform_guess_list_le (known : List Block) :
    Pr{let draw ← $ᵗ Block}[draw ∈ known] ≤ (known.length : ENNReal) / 2 ^ 1600 := by
  classical
  refine (prEvent_mono _ (p := fun draw => draw ∈ known)
    (q := fun draw => ∃ old ∈ known, draw = old) (fun draw seen => ⟨draw, seen, rfl⟩)).trans ?_
  simpa only [mul_one_div] using prEvent_list_le known ($ᵗ Block) (fun old draw => draw = old)
    (1 / 2 ^ 1600) (fun old _ => public_guess_first_output_le old)

theorem proposal_output_conflict_le (known : List Block) (count maximum : Nat)
    (room : known.length + count ≤ maximum) :
    Pr{let tape ← sampleProposalTape count}[outputConflict known tape = true] ≤
      (count : ENNReal) * ((maximum : ENNReal) / 2 ^ 1600) := by
  classical
  induction count generalizing known with
  | zero => simp [sampleProposalTape, outputConflict]
  | succ count ih =>
    let rate := (maximum : ENNReal) / 2 ^ 1600
    let step (draw : Block) := fun tape => outputConflict known (draw :: tape)
    have one : Pr{let draw ← $ᵗ Block}[draw ∈ known] ≤ rate :=
      (uniform_guess_list_le known).trans (ENNReal.div_le_div_right (by exact_mod_cast (show known.length ≤ maximum by omega)) _)
    have rest (draw : Block) (_ : draw ∈ support ($ᵗ Block)) (unseen : draw ∉ known) :
        Pr{let tape ← sampleProposalTape count}[step draw tape = true] ≤ (count : ENNReal) * rate := by
      have roomNext : (draw :: known).length + count ≤ maximum := by simp only [List.length_cons]; omega
      simpa [step, outputConflict, unseen, rate] using ih (draw :: known) roomNext
    have bound := prEvent_bind_le_prEvent_add_of_support ($ᵗ Block)
      (fun draw => step draw <$> sampleProposalTape count) (· ∈ known) (· = true)
      (fun draw present unseen => by simpa only [prEvent_map, Function.comp_def] using rest draw present unseen)
    simp only [sampleProposalTape, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, step] at bound ⊢
    apply bound.trans
    calc
      _ ≤ rate + (count : ENNReal) * rate := add_le_add one le_rfl
      _ = _ := by rw [Nat.cast_succ, add_mul, one_mul, add_comm]


theorem sampleProposalTape_length {count : Nat} {tape : List Block}
    (possible : tape ∈ support (sampleProposalTape count)) : tape.length = count := by
  induction count generalizing tape with
  | zero =>
    simp only [sampleProposalTape, support_pure, Set.mem_singleton_iff] at possible
    subst tape
    rfl
  | succ count ih =>
    simp only [sampleProposalTape, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at possible
    obtain ⟨draw, _, rest, restPossible, rfl⟩ := possible
    simp only [List.length_cons, ih restPossible]

theorem planned_rows_outputs (answers : List Block) (plans : List InputPlan) (tape : List Block)
    (enough : tape.length = plans.length) :
    (plannedRows answers plans tape).map Prod.snd = tape := by
  induction plans generalizing answers tape with
  | nil =>
    cases tape <;> simp_all [plannedRows]
  | cons plan rest ih =>
    cases tape with
    | nil => simp at enough
    | cons proposal tail =>
      simp only [List.length_cons, Nat.succ.injEq] at enough
      simp only [plannedRows, List.map_cons, ih (proposal :: answers) tail enough]

def plannedInputHit (known : List Row) (answers : List Block) (plans : List InputPlan)
    (tape : List Block) : Prop :=
  ∃ row ∈ plannedRows answers plans tape, ¬ UnusedInput known row.1

/-- Honest input tags can rule out all internal input repeats. After that
restriction, only a hit on the original cache and the output birthday cost remain. -/
theorem proposal_conflict_decompose (cache : Cache) (answers : List Block) (plans : List InputPlan)
    (distinct : ∀ tape ∈ support (sampleProposalTape plans.length),
      ((plannedRows answers plans tape).map Prod.fst).Nodup) :
    Pr{let flag ← proposedConflict cache answers plans}[flag = true] ≤
      Pr{let tape ← sampleProposalTape plans.length}[plannedInputHit cache.entries answers plans tape] +
      (plans.length : ENNReal) * (((cache.entries.length + plans.length : Nat) : ENNReal) / 2 ^ 1600) := by
  classical
  rw [(proposed_conflict_from_full_tape cache answers plans).prEvent_eq (· = true), prEvent_map]
  let sample := sampleProposalTape plans.length
  let input := plannedInputHit cache.entries answers plans
  let output (tape : List Block) := outputConflict (cache.entries.map Prod.snd) tape = true
  have included :
      Pr{let tape ← sample}[rowListConflict cache.entries (plannedRows answers plans tape) = true] ≤
        Pr{let tape ← sample}[input tape ∨ output tape] := by
    apply prEvent_mono_of_support
    intro tape possible bad
    by_contra no
    have noInput (row) (present : row ∈ plannedRows answers plans tape) : UnusedInput cache.entries row.1 :=
      not_not.mp (fun hit => no (Or.inl ⟨row, present, hit⟩))
    have clean : outputConflict (cache.entries.map Prod.snd) tape = false := by
      have noOutput : ¬ outputConflict (cache.entries.map Prod.snd) tape = true :=
        fun bad => no (Or.inr bad)
      simpa using noOutput
    have outputs := planned_rows_outputs answers plans tape (sampleProposalTape_length possible)
    have noConflict := rowListConflict_false (distinct tape possible) noInput (outputs.symm ▸ clean)
    rw [noConflict] at bad
    contradiction
  refine included.trans ((prEvent_or_le sample input output).trans (add_le_add le_rfl ?_))
  exact proposal_output_conflict_le (cache.entries.map Prod.snd) plans.length
    (cache.entries.length + plans.length) (by simp)

end TwoPermutationPrototype.Sampling
