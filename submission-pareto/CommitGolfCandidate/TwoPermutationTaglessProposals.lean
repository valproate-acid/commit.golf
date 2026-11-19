import CommitGolfCandidate.TwoPermutationTaglessOpened

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option exponentiation.threshold 2048

noncomputable def taglessSecondConflict (messages : Index → Words 32) (known : List Block) :
    List Index → List Block → Bool
  | index :: rest, a :: _b :: tape => by
    classical
    let address := taglessSecondAddress messages index a
    exact if address ∈ firstDomain ∨ address ∈ known then true
      else taglessSecondConflict messages (address :: known) rest tape
  | _, _ => false

theorem tagless_second_conflict_le (messages : Index → Words 32) (indices : List Index)
    (known : List Block) (maximum : Nat) (room : known.length + indices.length ≤ maximum) :
    Pr{let tape ← sampleProposalTape (2 * indices.length)}[
      taglessSecondConflict messages known indices tape = true] ≤
      (indices.length : ENNReal) * ((1 : ENNReal)/2^168 + (maximum : ENNReal)/2^832) := by
  classical
  induction indices generalizing known with
  | nil => simp [taglessSecondConflict, sampleProposalTape]
  | cons index rest ih =>
    let rate : ENNReal := (1 : ENNReal)/2^168 + (maximum : ENNReal)/2^832
    let address (a : Block) := taglessSecondAddress messages index a
    let bad (a : Block) := address a ∈ firstDomain ∨ address a ∈ known
    let step (a : Block) : ProbComp (List Block) := do
      let b ← $ᵗ Block
      let tape ← sampleProposalTape (2 * rest.length)
      pure (a :: b :: tape)
    let event (tape : List Block) := taglessSecondConflict messages known (index :: rest) tape = true
    have expansion : sampleProposalTape (2 * (index :: rest).length) = ($ᵗ Block >>= step) := by
      rw [List.length_cons, show 2 * (rest.length + 1) = (2 * rest.length + 1) + 1 by omega]
      simp only [sampleProposalTape, step, bind_assoc, pure_bind]
    have one : Pr{let a ← $ᵗ Block}[bad a] ≤ rate := by
      have first := tagless_proposal_first_domain_le (taglessMessageTail (messages index))
      have knownHit := tagless_proposal_repeated_address (taglessMessageTail (messages index)) known
      have repeated : Pr{let a ← $ᵗ Block}[address a ∈ known] ≤ (maximum : ENNReal)/2^832 := by
        refine (prEvent_mono ($ᵗ Block) (p := fun a => address a ∈ known)
          (q := fun a => ∃ guess ∈ known, address a = guess) (fun a hit => ⟨address a, hit, rfl⟩)).trans
          (knownHit.trans (ENNReal.div_le_div_right ?_ _))
        exact_mod_cast (show known.length ≤ maximum by omega)
      exact (prEvent_or_le ($ᵗ Block) (fun a => address a ∈ firstDomain) (fun a => address a ∈ known)).trans
        (add_le_add first repeated)
    have tailBound (a : Block) (_ : a ∈ support ($ᵗ Block)) (safe : ¬ bad a) :
        Pr{let tape ← step a}[event tape] ≤ (rest.length : ENNReal) * rate := by
      unfold step
      apply prEvent_bind_le_of_forall_le_of_support
      intro b _
      have nextRoom : (address a :: known).length + rest.length ≤ maximum := by
        simp only [List.length_cons] at room ⊢
        omega
      rw [bind_pure_comp, prEvent_map]
      change Pr{let tape ← sampleProposalTape (2 * rest.length)}[
        taglessSecondConflict messages known (index :: rest) (a :: b :: tape) = true] ≤ _
      simp only [taglessSecondConflict, ← show address a = taglessSecondAddress messages index a from rfl,
        show ¬ (address a ∈ firstDomain ∨ address a ∈ known) from safe, ite_false]
      exact ih (address a :: known) nextRoom
    rw [expansion]
    refine (prEvent_bind_le_prEvent_add_of_support ($ᵗ Block) step bad event tailBound).trans ?_
    refine (add_le_add one le_rfl).trans_eq ?_
    rw [List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm]

private theorem clean_output_cons (known : List Row) (row : Row) (tape : List Block)
    (clean : outputConflict (known.map Prod.snd) (row.2 :: tape) = false) :
    UnusedOutput known row.2 ∧ outputConflict ((row :: known).map Prod.snd) tape = false := by
  classical
  have unseen : row.2 ∉ known.map Prod.snd := by
    intro seen
    simp [outputConflict, seen] at clean
  refine ⟨?_, ?_⟩
  · intro old present hit
    exact unseen (List.mem_map.mpr ⟨old, present, hit⟩)
  · simpa only [outputConflict, unseen, ite_false, List.map_cons] using clean

/-- A first-round conflict can only be a hit on the original seed. Every
second-round conflict is covered by its domain test or its earlier-address test. -/
theorem tagless_planned_conflict_free (messages : Index → Words 32) (salts : Index → BitVec 128)
    (indices : List Index) (known : List Row) (secondKnown : List Block) (tape replies : List Block)
    (distinct : indices.Nodup)
    (covered : ∀ row ∈ known, row.1 ∈ secondKnown ∨ row.1 ∈ firstDomain)
    (firstFresh : ∀ i ∈ indices, UnusedInput known (taglessFirstAddress messages salts i))
    (secondClean : taglessSecondConflict messages secondKnown indices tape = false)
    (outputClean : outputConflict (known.map Prod.snd) tape = false) :
    rowListConflict known (plannedRows replies (taglessLeafPlans messages salts indices) tape) = false := by
  classical
  induction indices generalizing known secondKnown tape replies with
  | nil => simp [taglessLeafPlans, plannedRows, rowListConflict]
  | cons index rest ih =>
    cases tape with
    | nil => simp [taglessLeafPlans, plannedRows, rowListConflict]
    | cons a tape =>
      let firstRow : Row := (taglessFirstAddress messages salts index, a)
      have freshA : UnusedInput known firstRow.1 := firstFresh index List.mem_cons_self
      obtain ⟨cleanA, nextOutput⟩ := clean_output_cons known firstRow tape outputClean
      cases tape with
      | nil =>
        change rowListConflict known (firstRow :: []) = false
        simp only [rowListConflict, freshA, cleanA, and_self, ite_true]
      | cons b tape =>
        let secondRow : Row := (taglessSecondAddress messages index a, b)
        have safe : ¬ (secondRow.1 ∈ firstDomain ∨ secondRow.1 ∈ secondKnown) := by
          intro bad
          simp only [taglessSecondConflict, show taglessSecondAddress messages index a = secondRow.1 from rfl,
            bad, ite_true, Bool.true_eq_false] at secondClean
        have secondDomain : secondRow.1 ∉ firstDomain := fun inside => safe (Or.inl inside)
        have secondEarlier : secondRow.1 ∉ secondKnown := fun inside => safe (Or.inr inside)
        have freshB : UnusedInput (firstRow :: known) secondRow.1 := by
          intro previous reached equal
          rcases List.mem_cons.mp reached with rfl | earlier
          · exact secondDomain (equal ▸ tagless_first_address_domain messages salts index)
          · rcases covered previous earlier with registered | first
            · exact secondEarlier (equal ▸ registered)
            · exact secondDomain (equal ▸ first)
        obtain ⟨cleanB, tailOutput⟩ := clean_output_cons (firstRow :: known) secondRow tape nextOutput
        change rowListConflict known (firstRow :: secondRow ::
          plannedRows (b :: a :: replies) (taglessLeafPlans messages salts rest) tape) = false
        simp only [rowListConflict, freshA, cleanA, freshB, cleanB, and_self, ite_true]
        apply ih (secondRow :: firstRow :: known) (secondRow.1 :: secondKnown) tape _ (List.nodup_cons.mp distinct).2
        · intro row present
          rcases List.mem_cons.mp present with rfl | present
          · exact Or.inl List.mem_cons_self
          · rcases List.mem_cons.mp present with rfl | earlier
            · exact Or.inr (tagless_first_address_domain messages salts index)
            · exact (covered row earlier).imp (List.mem_cons_of_mem _) id
        · intro i inside row present equal
          rcases List.mem_cons.mp present with rfl | present
          · exact secondDomain (equal.symm ▸ tagless_first_address_domain messages salts i)
          · rcases List.mem_cons.mp present with rfl | earlier
            · have eq := tagless_first_address_injective messages salts equal
              exact (List.nodup_cons.mp distinct).1 (eq.symm ▸ inside)
            · exact firstFresh i (List.mem_cons_of_mem _ inside) row earlier equal
        · simpa only [taglessSecondConflict, show taglessSecondAddress messages index a = secondRow.1 from rfl,
            safe, ite_false] using secondClean
        · exact tailOutput

noncomputable def taglessHiddenPlans (positions : Positions) (messages : Index → Words 32)
    (salts : Index → BitVec 128) : List InputPlan :=
  taglessLeafPlans messages salts ((hiddenIndices positions).map Subtype.val)

noncomputable def taglessProposalRate (budget : Nat) : ENNReal :=
  (budget : ENNReal)/2^128 + ((2 : ENNReal)^24 *
    (1/2^168 + ((budget : ENNReal) + 2^25)/2^832) +
    (2 : ENNReal)^25 * (((budget : ENNReal) + 2^25)/2^1600))

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

theorem tagless_hidden_conflict_le {positions : Positions} (cache : Cache) (messages : Index → Words 32)
    (firstStage openedRows : List Row) (budget : Nat)
    (seed : cache.entries = openedRows ++ firstStage) (firstCount : firstStage.length ≤ budget)
    (openedCount : openedRows.length ≤ 2 * positions.card)
    (guard : ∀ row ∈ openedRows, taglessOpenedAddress positions row.1) :
    Pr{let flag ← (($ᵗ UnopenedSalts positions) >>= fun salts =>
      proposedConflict cache [] (taglessHiddenPlans positions messages (publicSaltTape salts)))}[
        flag = true] ≤ taglessProposalRate budget := by
  classical
  let indices : List Index := (hiddenIndices positions).map Subtype.val
  let known := cache.entries
  let maximum := budget + 2^25
  let plan (salts : UnopenedSalts positions) := taglessHiddenPlans positions messages (publicSaltTape salts)
  let badSalt (salts : UnopenedSalts positions) := ∃ row ∈ firstStage,
    ∃ i : HiddenIndex positions, hiddenFirstInput i.val (messages i.val) (salts i) = row.1
  have initial : Pr{let salts ← $ᵗ UnopenedSalts positions}[badSalt salts] ≤ (budget : ENNReal)/2^128 := by
    have bound := tagless_first_tape_cache_hit (fun i : HiddenIndex positions => i.val)
      Subtype.val_injective messages (firstStage.map Prod.fst)
    simp only [List.length_map] at bound
    refine (prEvent_mono ($ᵗ UnopenedSalts positions) (p := badSalt)
      (q := fun salts => ∃ address ∈ firstStage.map Prod.fst, ∃ i : HiddenIndex positions,
        hiddenFirstInput i.val (messages i.val) (salts i) = address) ?_).trans
      (bound.trans (ENNReal.div_le_div_right ?_ _))
    · rintro salts ⟨row, included, i, hit⟩
      exact ⟨row.1, List.mem_map_of_mem included, i, hit⟩
    · exact_mod_cast firstCount
  have allIndices : indices.length + positions.card = 2 ^ 24 := by
    simpa only [indices, List.length_map] using hidden_index_count positions
  have distinct : indices.Nodup := (Finset.nodup_toList _).map Subtype.val_injective
  have indexed (i : Index) (inside : i ∈ indices) : i ∉ positions := by
    obtain ⟨hidden, _, equal⟩ := List.mem_map.mp inside
    exact equal ▸ hidden.property
  have room : known.length + 2 * indices.length ≤ maximum := by
    simp only [known, seed, List.length_append, maximum]
    omega
  have maximumCast : (maximum : ENNReal) = (budget : ENNReal) + 2^25 := by
    simp only [maximum, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  let secondRate : ENNReal := 2^24 * (1/2^168 + (maximum : ENNReal)/2^832)
  let outputRate : ENNReal := 2^25 * ((maximum : ENNReal)/2^1600)
  have secondCharge : Pr{let tape ← sampleProposalTape (2*indices.length)}[
      taglessSecondConflict messages (known.map Prod.fst) indices tape = true] ≤ secondRate := by
    refine (tagless_second_conflict_le messages indices (known.map Prod.fst) maximum ?_).trans ?_
    · simp only [List.length_map]; omega
    · apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast (show indices.length ≤ 2^24 by omega)
  have outputCharge : Pr{let tape ← sampleProposalTape (2*indices.length)}[
      outputConflict (known.map Prod.snd) tape = true] ≤ outputRate := by
    refine (proposal_output_conflict_le (known.map Prod.snd) (2*indices.length) maximum ?_).trans ?_
    · simpa only [List.length_map] using room
    · apply mul_le_mul_of_nonneg_right _ zero_le
      exact_mod_cast (show 2*indices.length ≤ 2^25 by omega)
  have tail (salts : UnopenedSalts positions) (_ : salts ∈ support ($ᵗ UnopenedSalts positions))
      (safe : ¬ badSalt salts) :
      Pr{let flag ← proposedConflict cache [] (plan salts)}[flag = true] ≤ secondRate + outputRate := by
    rw [(proposed_conflict_from_full_tape cache [] (plan salts)).prEvent_eq (· = true), prEvent_map]
    simp only [show plan salts = taglessLeafPlans messages (publicSaltTape salts) indices from rfl,
      tagless_leaf_plans_length]
    let sample := sampleProposalTape (2 * indices.length)
    let sBad (tape : List Block) := taglessSecondConflict messages (known.map Prod.fst) indices tape = true
    let oBad (tape : List Block) := outputConflict (known.map Prod.snd) tape = true
    apply le_trans (b := Pr{let tape ← sample}[sBad tape ∨ oBad tape])
    · apply prEvent_mono
      intro tape conflict
      by_contra bad
      have noSecond : taglessSecondConflict messages (known.map Prod.fst) indices tape = false := by
        simpa [sBad] using (not_or.mp bad).1
      have noOutput : outputConflict (known.map Prod.snd) tape = false := by
        simpa [oBad] using (not_or.mp bad).2
      have firstFresh (i : Index) (included : i ∈ indices) :
          UnusedInput known (taglessFirstAddress messages (publicSaltTape salts) i) := by
        intro row seen equal
        have closed := indexed i included
        simp only [known, seed, List.mem_append] at seen
        rcases seen with opened | old
        · exact tagless_opened_address_disjoint (guard row opened) _ _ _ closed equal
        · refine safe ⟨row, old, ⟨i, closed⟩, ?_⟩
          have hit : hiddenFirstInput i (messages i) (publicSaltTape salts i) = row.1 := equal.symm
          simpa only [publicSaltTape, dite_eq_left closed] using hit
      have checked := tagless_planned_conflict_free messages (publicSaltTape salts) indices known
        (known.map Prod.fst) tape [] distinct (fun row included => Or.inl (List.mem_map_of_mem included))
        firstFresh noSecond noOutput
      exact Bool.noConfusion (checked.symm.trans conflict)
    · exact (prEvent_or_le sample sBad oBad).trans (add_le_add secondCharge outputCharge)
  unfold taglessProposalRate
  rw [← maximumCast]
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ UnopenedSalts positions)
    (fun salts => proposedConflict cache [] (plan salts)) badSalt (· = true) tail).trans
    (add_le_add initial le_rfl)

end TwoPermutationPrototype.Sampling
