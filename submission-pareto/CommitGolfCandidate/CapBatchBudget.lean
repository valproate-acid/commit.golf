import CommitGolfCandidate.CapBatchReplay

/-! Reachable cap occupancy is fixed by the supplied indices even when replies
are arbitrary. This support invariant tightens the complete replay bound to
thirty-two public calls per opened position, below the contract's ceiling. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

theorem cap_insert_domain (roots next : CapRootMap) (key group : Nat) (value : Digest)
    (inserted : capInsert roots key value = some next) :
    (next group).isSome = true ↔ group = key ∨ (roots group).isSome = true := by
  rw [cap_insert_lookup roots next key group value inserted]
  by_cases same : group = key <;> simp [same]

/-- Every supported successful batch result has exactly the old occupied groups
plus the input records' groups. This statement covers arbitrary reply sequences. -/
theorem cap_lower_batch_support_domain (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap) (inputs : List (BitVec 512))
    (reached : some (finalRoots, inputs) ∈ support (capReplayLowerBatch records roots))
    (group : Nat) :
    (finalRoots group).isSome = true ↔
      (roots group).isSome = true ∨
        ∃ record ∈ records, (capGroup record.index).val = group := by
  induction records generalizing roots finalRoots inputs with
  | nil =>
      have same := eq_of_mem_support_pure (some (roots, [])) reached
      have maps : finalRoots = roots := congrArg (fun result => result.map Prod.fst) same |>
        Option.some.inj
      subst finalRoots
      simp
  | cons record rest ih =>
      rw [capReplayLowerBatch] at reached
      obtain ⟨⟨root, recordInputs⟩, _, afterRecord⟩ := mem_support_bind_peel _ _ reached
      cases inserted : capInsert roots (capGroup record.index).val root with
      | none =>
          simp only [inserted] at afterRecord
          have impossible := eq_of_mem_support_pure (none : Option (CapRootMap × List (BitVec 512))) afterRecord
          contradiction
      | some next =>
          simp only [inserted] at afterRecord
          obtain ⟨result, tailReached, mapped⟩ := mem_support_bind_peel _ _ afterRecord
          have same := eq_of_mem_support_pure
            (result.map fun (tailRoots, tailInputs) => (tailRoots, recordInputs ++ tailInputs)) mapped
          cases result with
          | none => simp at same
          | some pair =>
              rcases pair with ⟨tailRoots, tailInputs⟩
              have maps : finalRoots = tailRoots := by
                simpa using congrArg (fun result => result.map Prod.fst) same
              subst tailRoots
              rw [ih next finalRoots tailInputs tailReached, cap_insert_domain roots next _ group root inserted]
              simp only [List.mem_cons]
              constructor
              · rintro ((head | old) | later)
                · exact Or.inr ⟨record, Or.inl rfl, head.symm⟩
                · exact Or.inl old
                · obtain ⟨laterRecord, member, sameGroup⟩ := later
                  exact Or.inr ⟨laterRecord, Or.inr member, sameGroup⟩
              · rintro (old | ⟨laterRecord, member, sameGroup⟩)
                · exact Or.inl (Or.inr old)
                · rcases member with equal | later
                  · subst laterRecord
                    exact Or.inl (Or.inl sameGroup.symm)
                  · exact Or.inr ⟨laterRecord, later, sameGroup⟩

/-- At most one cap leaf is occupied per record. Repeated groups reduce the count. -/
theorem cap_lower_batch_support_count (records : List CapLowerRecord) (roots : CapRootMap)
    (inputs : List (BitVec 512))
    (reached : some (roots, inputs) ∈ support (capReplayLowerBatch records (fun _ => none))) :
    capMarkedCount (capKnownView roots 8 0) ≤ records.length := by
  classical
  rw [cap_known_view_card]
  have subset :
      (Finset.range 256).filter (fun group => (roots group).isSome = true) ⊆
        (records.map (fun record => (capGroup record.index).val)).toFinset := by
    intro group member
    obtain ⟨_, occupied⟩ := Finset.mem_filter.mp member
    have domain := cap_lower_batch_support_domain records (fun _ => none) roots inputs reached group
    obtain ⟨record, recordMember, same⟩ := by
      simpa using domain.mp occupied
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨record, recordMember, same⟩
  calc
    _ ≤ (records.map (fun record => (capGroup record.index).val)).toFinset.card :=
      Finset.card_le_card subset
    _ ≤ (records.map (fun record => (capGroup record.index).val)).length :=
      List.toFinset_card_le _
    _ = records.length := by simp

/-- Support-aware sequencing avoids requiring an arbitrary, unreachable result
map to obey the occupancy invariant. All actual reply continuations are covered. -/
theorem cap_replay_batch_position_bound (records : List CapLowerRecord)
    (proof : List Digest) (root : Digest) :
    IsTotalQueryBound (capReplayBatch records proof root) (32 * records.length) := by
  unfold capReplayBatch
  have total : 32 * records.length = 24 * records.length + 8 * records.length := by omega
  rw [total]
  apply isTotalQueryBound_bind_of_mem_support
    (cap_replay_lower_batch_query_bound records (fun _ => none))
  intro lowerResult reached
  cases lowerResult with
  | none => trivial
  | some pair =>
      rcases pair with ⟨roots, inputs⟩
      have count := cap_lower_batch_support_count records roots inputs reached
      have capBound : capCalls (capKnownView roots 8 0) ≤ 8 * records.length := by
        exact (cap_calls_bound _).trans (Nat.mul_le_mul_left 8 count)
      simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using
        (cap_replay_query_bound (capKnownView roots 8 0) proof).mono capBound
end CommitGolfCandidate
