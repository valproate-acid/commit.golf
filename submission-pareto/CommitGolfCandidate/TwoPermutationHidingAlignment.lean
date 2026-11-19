import CommitGolfCandidate.TwoPermutationHidingReplies
import CommitGolfCandidate.TwoPermutationHidingObserver

/-! Align the concrete oracle input plans with the reference tape. Any hit on
a seeded input must come from the adversary's first-stage trace, because
the opened rows have disjoint position tags. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp
set_option maxRecDepth 8192

def hiddenSalts {positions : Positions} (hidden : HiddenTape positions) (index : Index) : BitVec 128 :=
  if closed : index ∉ positions then (hidden ⟨index, closed⟩).1 else 0

def hiddenReplyPairs {positions : Positions} (digests : DigestTape) (hidden : HiddenTape positions)
    (index : HiddenIndex positions) : ReplyPair :=
  ((hidden index).2.1, (hidden index).2.2 ++ digests index.val)

theorem hidden_rows_match_plans {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (hidden : HiddenTape positions) (indices : List (HiddenIndex positions)) (answers : List Block) :
    plannedRows answers (leafPlans messages (hiddenSalts hidden) (indices.map Subtype.val))
      (serializeReplyPairs (indices.map (hiddenReplyPairs digests hidden))) =
      hiddenRowsFor digests messages hidden indices := by
  induction indices generalizing answers with
  | nil => rfl
  | cons index rest ih =>
    have salt : hiddenSalts hidden index.val = (hidden index).1 := by
      unfold hiddenSalts
      exact dite_eq_left index.property
    change (hiddenFirstInput index.val (messages index.val) (hiddenSalts hidden index.val), (hidden index).2.1) ::
      (hiddenSecondInput index.val (messages index.val) (hidden index).2.1,
        (hidden index).2.2 ++ digests index.val) ::
      plannedRows (((hidden index).2.2 ++ digests index.val) :: (hidden index).2.1 :: answers)
        (leafPlans messages (hiddenSalts hidden) (rest.map Subtype.val))
        (serializeReplyPairs (rest.map (hiddenReplyPairs digests hidden))) =
      hiddenFirstRow messages index.val (hidden index) ::
      hiddenSecondRow digests messages index.val (hidden index) :: hiddenRowsFor digests messages hidden rest
    rw [salt, ih]
    rfl

def exposedInputTag (positions : Positions) (input : Block) : Prop :=
  ∃ i : Index, i ∈ positions ∧
    (input.extractLsb' 0 64 = firstTag i.val ∨ input.extractLsb' 0 64 = secondTag i.val)

private theorem hidden_input_tag {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (hidden : HiddenTape positions) (row : Row) (present : row ∈ hiddenRows digests messages hidden) :
    ∃ i : HiddenIndex positions, row.1.extractLsb' 0 64 = firstTag i.val.val ∨
      row.1.extractLsb' 0 64 = secondTag i.val.val := by
  unfold hiddenRows hiddenRowsFor at present
  rcases List.mem_flatMap.mp present with ⟨i, _, possible⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at possible
  rcases possible with rfl | rfl
  · exact ⟨i, Or.inl (hidden_first_tag i _ _)⟩
  · exact ⟨i, Or.inr (hidden_second_tag i _ _)⟩

theorem opened_input_disjoint_hidden {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (hidden : HiddenTape positions) (row : Row) (present : row ∈ hiddenRows digests messages hidden)
    (opened : Block) (tagged : exposedInputTag positions opened) : opened ≠ row.1 := by
  intro equal
  obtain ⟨i, selected, openedTag⟩ := tagged
  obtain ⟨j, closedTag⟩ := hidden_input_tag digests messages hidden row present
  rw [equal] at openedTag
  rcases openedTag with openedTag | openedTag <;> rcases closedTag with closedTag | closedTag
  · exact j.property (hidden_first_tag_indices (openedTag.symm.trans closedTag) ▸ selected)
  · exact tags_disjoint i.isLt j.val.isLt (openedTag.symm.trans closedTag)
  · exact tags_disjoint j.val.isLt i.isLt (closedTag.symm.trans openedTag)
  · exact j.property (hidden_second_tag_indices (openedTag.symm.trans closedTag) ▸ selected)

theorem planned_input_hits_reference {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (hidden : HiddenTape positions) (firstStage opened : List Row)
    (tags : ∀ row ∈ opened, exposedInputTag positions row.1) :
    let indices := hiddenIndices positions
    let plans := leafPlans messages (hiddenSalts hidden) (indices.map Subtype.val)
    let tape := serializeReplyPairs (indices.map (hiddenReplyPairs digests hidden))
    plannedInputHit (opened ++ firstStage) [] plans tape →
      ∃ old ∈ firstStage, pairHitsHidden digests messages old hidden := by
  classical
  dsimp only
  unfold plannedInputHit
  rw [hidden_rows_match_plans]
  rintro ⟨row, present, hit⟩
  change row ∈ hiddenRows digests messages hidden at present
  have found : ∃ old ∈ opened ++ firstStage, old.1 = row.1 := by
    simpa [UnusedInput] using hit
  obtain ⟨old, oldIn, note⟩ := found
  rcases List.mem_append.mp oldIn with exposed | original
  · exact False.elim (opened_input_disjoint_hidden digests messages hidden row present old.1 (tags old exposed) note)
  · refine ⟨old, original, ?_⟩
    unfold hiddenRows hiddenRowsFor at present
    rcases List.mem_flatMap.mp present with ⟨i, _, possible⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at possible
    rcases possible with rfl | rfl
    · exact Or.inl ⟨i, note.symm⟩
    · exact Or.inr (Or.inl ⟨i, note.symm⟩)


open MeasureTheory in
theorem ideal_first_stage_hit_le {positions : Positions} (digests : DigestTape) (messages : Index → Words 32)
    (firstStage opened : List Row) (tags : ∀ row ∈ opened, exposedInputTag positions row.1) :
    Pr{let hidden ← sampleHiddenTape positions}[
      let indices := hiddenIndices positions
      let plans := leafPlans messages (hiddenSalts hidden) (indices.map Subtype.val)
      let tape := serializeReplyPairs (indices.map (hiddenReplyPairs digests hidden))
      plannedInputHit (opened ++ firstStage) [] plans tape] ≤
      (firstStage.length : ENNReal) * hiddenPairRate := by
  apply le_trans _ (fixed_reference_trace_hit_le positions digests messages firstStage)
  apply prEvent_mono
  intro hidden hit
  exact planned_input_hits_reference digests messages hidden firstStage opened tags hit

end TwoPermutationPrototype.Sampling
