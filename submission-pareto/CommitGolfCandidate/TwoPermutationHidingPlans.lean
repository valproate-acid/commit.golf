import CommitGolfCandidate.TwoPermutationHidingConflicts
import CommitGolfCandidate.TwoPermutationHidingPair

/-! Concrete honest two-call plans for a list of positions. The transcript retains
the two replies at each position, and the cache gains the matching rows. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp

def leafPlans (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) : List InputPlan :=
  indices.flatMap fun i =>
    [fun _ => hiddenFirstInput i (messages i) (salts i),
     fun answers => hiddenSecondInput i (messages i) (answers.headD 0)]

theorem leaf_plans_length (messages : Index → Words 32) (salts : Index → BitVec 128) (indices : List Index) :
    (leafPlans messages salts indices).length = 2 * indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    simp only [leafPlans, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil] at ih ⊢
    omega

def phaseTags (indices : List Index) : List Word :=
  indices.flatMap fun i => [firstTag i.val, secondTag i.val]

theorem phase_tags_distinct {indices : List Index} (distinct : indices.Nodup) : (phaseTags indices).Nodup := by
  induction indices with
  | nil => exact List.nodup_nil
  | cons index rest ih =>
    obtain ⟨notInTail, tailDistinct⟩ := List.nodup_cons.mp distinct
    change (firstTag index.val :: secondTag index.val :: phaseTags rest).Nodup
    have fresh : ∀ x ∈ phaseTags rest, x ≠ firstTag index.val ∧ x ≠ secondTag index.val := by
      intro tag present
      rcases List.mem_flatMap.mp present with ⟨j, earlier, possible⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at possible
      rcases possible with rfl | rfl
      · exact ⟨fun equal => notInTail (hidden_first_tag_indices equal ▸ earlier),
          tags_disjoint j.isLt index.isLt⟩
      · exact ⟨fun equal => tags_disjoint index.isLt j.isLt equal.symm,
          fun equal => notInTail (hidden_second_tag_indices equal ▸ earlier)⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨fun present => (fresh _ present).2 rfl, ih tailDistinct⟩⟩
    intro present
    rcases List.mem_cons.mp present with same | present
    · exact tags_disjoint index.isLt index.isLt same
    · exact (fresh _ present).1 rfl

theorem leaf_plan_rows_tags (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) (answers tape : List Block) (length : tape.length = 2 * indices.length) :
    (plannedRows answers (leafPlans messages salts indices) tape).map
        (fun row => row.1.extractLsb' 0 64) = phaseTags indices := by
  induction indices generalizing answers tape with
  | nil => cases tape <;> simp [leafPlans, plannedRows, phaseTags]
  | cons index rest ih =>
    cases tape with
    | nil => simp at length
    | cons first replies =>
      cases replies with
      | nil => simp at length; omega
      | cons second tail =>
        have exactTail : tail.length = 2 * rest.length := by
          simp only [List.length_cons] at length
          omega
        change (hiddenFirstInput index (messages index) (salts index)).extractLsb' 0 64 ::
          (hiddenSecondInput index (messages index) first).extractLsb' 0 64 ::
          (plannedRows (second :: first :: answers) (leafPlans messages salts rest) tail).map
            (fun row => row.1.extractLsb' 0 64) =
          firstTag index.val :: secondTag index.val :: phaseTags rest
        rw [hidden_first_tag, hidden_second_tag, ih _ _ exactTail]

theorem leaf_plan_inputs_distinct (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) (distinct : indices.Nodup) (answers tape : List Block)
    (possible : tape ∈ support (sampleProposalTape (leafPlans messages salts indices).length)) :
    ((plannedRows answers (leafPlans messages salts indices) tape).map Prod.fst).Nodup := by
  have length := (sampleProposalTape_length possible).trans (leaf_plans_length messages salts indices)
  have tagged : (((plannedRows answers (leafPlans messages salts indices) tape).map Prod.fst).map
      (fun input => input.extractLsb' 0 64)).Nodup := by
    rw [List.map_map]
    exact (leaf_plan_rows_tags messages salts indices answers tape length).symm ▸ phase_tags_distinct distinct
  exact List.Nodup.of_map (fun input : Block => input.extractLsb' 0 64) tagged

theorem proposed_from_full_tape {α : Type} (next : List Block → BiPermutation Block → ProbComp α)
    (p : BiPermutation Block) (answers : List Block) (plans : List InputPlan) :
    runProposed next p answers plans =
      (do let tape ← sampleProposalTape plans.length
          next (tape.reverse ++ answers) (p.programRows (plannedRows answers plans tape))) := by
  induction plans generalizing p answers with
  | nil => simp [runProposed, sampleProposalTape, plannedRows, BiPermutation.programRows]
  | cons plan rest ih =>
    simp only [runProposed, List.length_cons, sampleProposalTape, bind_assoc, pure_bind]
    apply bind_congr
    intro proposal
    rw [ih]
    apply bind_congr
    intro tape
    simp only [plannedRows, BiPermutation.programRows, List.foldl_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append]

end TwoPermutationPrototype.Sampling
