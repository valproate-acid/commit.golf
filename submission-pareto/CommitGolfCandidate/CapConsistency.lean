import CommitGolfCandidate.CapGroups

/-! Duplicate-group consistency for reconstructed lower roots. These pure checks
must subsequently be connected to the checker image's comparisons and stores. -/
namespace CommitGolfCandidate
open CommitGolf

abbrev CapRootMap := Nat → Option Digest

/-- An occupied group can only be reused with the same reconstructed root. -/
def capInsert (roots : CapRootMap) (group : Nat) (value : Digest) : Option CapRootMap :=
  match roots group with
  | none => some (fun index => if index = group then some value else roots index)
  | some previous => if previous = value then some roots else none

def capCollect : List (Nat × Digest) → Option CapRootMap
  | [] => some (fun _ => none)
  | (group, value) :: rest => do
      let roots ← capCollect rest
      capInsert roots group value

theorem cap_insert_lookup (roots next : CapRootMap) (group index : Nat) (value : Digest)
    (accepted : capInsert roots group value = some next) :
    next index = if index = group then some value else roots index := by
  cases prior : roots group with
  | none =>
      simp [capInsert, prior] at accepted
      subst next
      rfl
  | some previous =>
      by_cases equal : previous = value
      · simp [capInsert, prior, equal] at accepted
        subst next
        subst value
        by_cases same : index = group
        · subst index; simp [prior]
        · simp [same]
      · simp [capInsert, prior, equal] at accepted

theorem cap_insert_preserves (roots next : CapRootMap) (group index : Nat)
    (value existing : Digest) (accepted : capInsert roots group value = some next)
    (known : roots index = some existing) : next index = some existing := by
  by_cases same : index = group
  · subst index
    have sameValue : existing = value := by
      by_cases equal : existing = value
      · exact equal
      · simp [capInsert, known, equal] at accepted
    rw [cap_insert_lookup roots next group group value accepted]
    simp [sameValue]
  · rw [cap_insert_lookup roots next group index value accepted]
    simp [same, known]

/-- Successful collection proves consistency of every supplied record, including
all repeated group keys. No root from a later duplicate is silently discarded. -/
theorem cap_collect_member (records : List (Nat × Digest)) (roots : CapRootMap)
    (accepted : capCollect records = some roots) (group : Nat) (value : Digest)
    (member : (group, value) ∈ records) : roots group = some value := by
  induction records generalizing roots with
  | nil => simp at member
  | cons head rest ih =>
      rcases head with ⟨headGroup, headValue⟩
      cases tail : capCollect rest with
      | none => simp [capCollect, tail] at accepted
      | some previous =>
          have inserted : capInsert previous headGroup headValue = some roots := by
            simpa [capCollect, tail] using accepted
          simp only [List.mem_cons] at member
          rcases member with same | member
          · cases same
            rw [cap_insert_lookup previous roots group group value inserted]
            simp
          · exact cap_insert_preserves previous roots headGroup group headValue value inserted
              (ih previous tail member)

/-- The collector occupies exactly the groups present in the supplied records. -/
theorem cap_collect_domain (records : List (Nat × Digest)) (roots : CapRootMap)
    (accepted : capCollect records = some roots) (group : Nat) :
    (roots group).isSome = true ↔ ∃ value, (group, value) ∈ records := by
  induction records generalizing roots with
  | nil => simp [capCollect] at accepted; subst roots; simp
  | cons head rest ih =>
      rcases head with ⟨headGroup, headValue⟩
      cases tail : capCollect rest with
      | none => simp [capCollect, tail] at accepted
      | some previous =>
          have inserted : capInsert previous headGroup headValue = some roots := by
            simpa [capCollect, tail] using accepted
          rw [cap_insert_lookup previous roots headGroup group headValue inserted]
          by_cases same : group = headGroup
          · subst group; simp
          · simp [same, ih previous tail, List.mem_cons, Prod.mk.injEq]

/-- Reversal makes the tail-first recursion insert records in their input order,
the order used by the prospective checker loop. -/
def capCollectForward (records : List (Nat × Digest)) : Option CapRootMap :=
  capCollect records.reverse

theorem cap_collect_forward_member (records : List (Nat × Digest)) (roots : CapRootMap)
    (accepted : capCollectForward records = some roots) (group : Nat) (value : Digest)
    (member : (group, value) ∈ records) : roots group = some value := by
  exact cap_collect_member records.reverse roots accepted group value (by simpa using member)

theorem cap_collect_forward_domain (records : List (Nat × Digest)) (roots : CapRootMap)
    (accepted : capCollectForward records = some roots) (group : Nat) :
    (roots group).isSome = true ↔ ∃ value, (group, value) ∈ records := by
  simpa using cap_collect_domain records.reverse roots accepted group

/-- One additional input record is inserted after all preceding records, making
the forward loop refinement boundary explicit. -/
theorem cap_collect_forward_append (records : List (Nat × Digest)) (group : Nat)
    (value : Digest) :
    capCollectForward (records ++ [(group, value)]) =
      (do let roots ← capCollectForward records; capInsert roots group value) := by
  simp [capCollectForward, capCollect]
end CommitGolfCandidate
