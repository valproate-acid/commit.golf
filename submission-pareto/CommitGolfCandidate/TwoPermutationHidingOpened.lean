import CommitGolfCandidate.TwoPermutationHidingConditional
import CommitGolfCandidate.TwoPermutationPosterior

/-! Move the opened leaf queries ahead of the unopened stage. The opened leaves
seed only rows with opened tags, and their replies retain the uniform posterior. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp

noncomputable def runPrepared (cache : Cache) (answers : List Block) : List InputPlan → ProbComp (List Block × Cache)
  | [] => pure (answers, cache)
  | plan :: rest => do
      let (reply, middle) ← cache.forward (plan answers)
      runPrepared middle (reply :: answers) rest

theorem prepared_posterior_equivalence {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (cache : Cache) (answers : List Block) (plans : List InputPlan) :
    (do let permutation ← cache.sample
        runPlanned next permutation.val answers plans) =ᵈ
      (do let (replies, final) ← runPrepared cache answers plans
          let permutation ← final.sample
          next replies permutation.val) := by
  induction plans generalizing cache answers with
  | nil =>
    simp only [runPlanned, runPrepared, pure_bind]
    rfl
  | cons plan rest ih =>
    simp only [runPlanned, runPrepared, bind_assoc]
    apply (cache.forward_step_eq (plan answers) (fun reply p => runPlanned next p (reply :: answers) rest)).trans
    apply EvalDistEq.bind_right
    intro result
    exact ih result.2 (result.1 :: answers)

private theorem forward_step_rows (cache : Cache) (input : Block) (result : Block × Cache)
    (present : result ∈ support (cache.forward input)) :
    result.2.entries = cache.entries ∨ result.2.entries = (input, result.1) :: cache.entries := by
  unfold PermutationCache.forward at present
  split at present
  · obtain ⟨reply, _, same⟩ := (mem_support_bind_iff _ _ _).mp present
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    exact Or.inr rfl
  · simp only [support_pure, Set.mem_singleton_iff] at present
    subst result
    exact Or.inl rfl

theorem prepared_support_header (cache : Cache) (answers : List Block) (plans : List InputPlan)
    (tagged : Block → Prop) (onlyTagged : ∀ plan ∈ plans, ∀ replies : List Block, tagged (plan replies))
    (result : List Block × Cache) (possible : result ∈ support (runPrepared cache answers plans)) :
    ∃ added : List Row, result.2.entries = added ++ cache.entries ∧ added.length ≤ plans.length ∧
      ∀ row ∈ added, tagged row.1 := by
  induction plans generalizing cache answers result with
  | nil =>
    simp only [runPrepared, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨[], by simp⟩
  | cons plan rest ih =>
    simp only [runPrepared] at possible
    obtain ⟨⟨reply, middle⟩, step, tail⟩ := (mem_support_bind_iff _ _ _).mp possible
    obtain ⟨added, representation, count, tags⟩ :=
      ih middle (reply :: answers) (fun plan inTail => onlyTagged plan (List.mem_cons_of_mem _ inTail)) result tail
    rcases forward_step_rows cache (plan answers) (reply, middle) step with stayed | grew
    · refine ⟨added, ?_, ?_, tags⟩
      exacts [representation.trans (congrArg (added ++ ·) stayed), by simp only [List.length_cons]; omega]
    · refine ⟨added ++ [(plan answers, reply)], ?_, ?_, ?_⟩
      · simp only [List.append_assoc, List.singleton_append]
        exact representation.trans (congrArg (added ++ ·) grew)
      · simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      · intro row inAdded
        rcases List.mem_append.mp inAdded with old | fresh
        · exact tags row old
        · simp only [List.mem_singleton] at fresh
          subst row
          exact onlyTagged plan List.mem_cons_self answers

theorem opened_plan_tag (positions : Positions) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) (allOpened : ∀ i ∈ indices, i ∈ positions)
    (plan : InputPlan) (present : plan ∈ leafPlans messages salts indices) (replies : List Block) :
    exposedInputTag positions (plan replies) := by
  unfold leafPlans at present
  obtain ⟨index, included, phase⟩ := List.mem_flatMap.mp present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at phase
  rcases phase with rfl | rfl
  · exact ⟨index, allOpened index included, Or.inl (hidden_first_tag index _ _)⟩
  · exact ⟨index, allOpened index included, Or.inr (hidden_second_tag index _ _)⟩

/-- The exact partition required by conditional hiding holds on every opened
history, even if a previous adversary already queried one of the honest inputs. -/
theorem prepared_opened_rows (positions : Positions) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (cache : Cache) (result : List Block × Cache)
    (possible : result ∈ support (runPrepared cache [] (leafPlans messages salts positions.toList))) :
    ∃ rows : List Row, result.2.entries = rows ++ cache.entries ∧ rows.length ≤ 2 * positions.card ∧
      ∀ row ∈ rows, exposedInputTag positions row.1 := by
  obtain ⟨rows, layout, count, tags⟩ := prepared_support_header cache [] _ (exposedInputTag positions)
    (opened_plan_tag positions messages salts positions.toList (fun index mem => Finset.mem_toList.mp mem)) result possible
  refine ⟨rows, layout, count.trans_eq ?_, tags⟩
  rw [leaf_plans_length, Finset.length_toList]

end TwoPermutationPrototype.Sampling
