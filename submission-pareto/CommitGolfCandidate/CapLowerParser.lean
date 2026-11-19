import CommitGolfCandidate.CapBatchBudget

/-! Digest-level parsing of the fixed seventeen-digest lower records. Supplied
indices and values come from the trusted ABI, while salts and siblings come
from the adversarial proof. Byte packing and actual loader access are separate. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp

def capParseLower (values : Index → Entry) :
    List Index → List Digest → Option (List CapLowerRecord × List Digest)
  | [], proof => some ([], proof)
  | index :: indices, proof =>
      match proof with
      | [] => none
      | salt :: rest =>
          if 16 ≤ rest.length then do
            let (records, capProof) ← capParseLower values indices (rest.drop 16)
            let record : CapLowerRecord :=
              ⟨index, values index, salt, fun level => rest[level.val]?.getD 0⟩
            return (record :: records, capProof)
          else none

def capLowerEncoding (record : CapLowerRecord) : List Digest :=
  record.salt :: List.ofFn record.sibling

def capLowerTranscript (records : List CapLowerRecord) : List Digest :=
  records.flatMap capLowerEncoding

theorem cap_lower_siblings_take (proof : List Digest) (enough : 16 ≤ proof.length) :
    List.ofFn (fun level : Fin 16 => proof[level.val]?.getD 0) = proof.take 16 := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left enough]
  · intro index leftBound rightBound
    have bound : index < proof.length := by
      simp only [List.length_ofFn] at leftBound
      omega
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem?_eq_getElem bound,
      Option.getD_some]

/-- Exact digest slots, not only the total length: each parsed salt and sibling
re-encodes the consumed prefix, and the cap receives precisely the suffix. -/
theorem cap_parse_lower_encoding (values : Index → Entry) (indices : List Index)
    (proof : List Digest) (records : List CapLowerRecord) (rest : List Digest)
    (parsed : capParseLower values indices proof = some (records, rest)) :
    proof = capLowerTranscript records ++ rest := by
  induction indices generalizing proof records rest with
  | nil =>
      simp only [capParseLower, Option.some.injEq, Prod.mk.injEq] at parsed
      rcases parsed with ⟨rfl, rfl⟩
      rfl
  | cons index indices ih =>
      cases proof with
      | nil => simp [capParseLower] at parsed
      | cons salt tail =>
          by_cases enough : 16 ≤ tail.length
          · cases later : capParseLower values indices (tail.drop 16) with
            | none => simp [capParseLower, enough, later] at parsed
            | some pair =>
                rcases pair with ⟨laterRecords, capProof⟩
                have same :
                    (⟨index, values index, salt, fun level => tail[level.val]?.getD 0⟩ ::
                      laterRecords, capProof) = (records, rest) := by
                  simpa [capParseLower, enough, later] using parsed
                cases same
                have suffix := ih _ _ _ later
                change tail.drop 16 = laterRecords.flatMap capLowerEncoding ++ rest at suffix
                simp only [capLowerTranscript, List.flatMap_cons, capLowerEncoding,
                  cap_lower_siblings_take tail enough, List.cons_append, List.append_assoc]
                rw [← suffix, List.take_append_drop]
          · simp [capParseLower, enough] at parsed

/-- An accepted parse neither changes the ABI index order nor invents values,
and consumes exactly seventeen digest words per record. -/
theorem cap_parse_lower_facts (values : Index → Entry) (indices : List Index)
    (proof : List Digest) (records : List CapLowerRecord) (rest : List Digest)
    (parsed : capParseLower values indices proof = some (records, rest)) :
    records.length = indices.length ∧
    records.map CapLowerRecord.index = indices ∧
    proof.length = 17 * records.length + rest.length ∧
    ∀ record ∈ records, record.value = values record.index := by
  induction indices generalizing proof records rest with
  | nil =>
      simp only [capParseLower, Option.some.injEq, Prod.mk.injEq] at parsed
      rcases parsed with ⟨rfl, rfl⟩
      simp
  | cons index indices ih =>
      cases proof with
      | nil => simp [capParseLower] at parsed
      | cons salt tail =>
          by_cases enough : 16 ≤ tail.length
          · cases later : capParseLower values indices (tail.drop 16) with
            | none => simp [capParseLower, enough, later] at parsed
            | some pair =>
                rcases pair with ⟨laterRecords, capProof⟩
                have same :
                    (⟨index, values index, salt, fun level => tail[level.val]?.getD 0⟩ ::
                      laterRecords, capProof) = (records, rest) := by
                  simpa [capParseLower, enough, later] using parsed
                cases same
                obtain ⟨count, order, length, valuesCorrect⟩ := ih _ _ _ later
                refine ⟨by simp [count], by simp [order], ?_, ?_⟩
                · simp only [List.length_cons, List.length_drop] at length ⊢
                  omega
                · intro record member
                  rcases List.mem_cons.mp member with equal | laterMember
                  · subst record; rfl
                  · exact valuesCorrect record laterMember
          · simp [capParseLower, enough] at parsed

/-- The image's up-front minimum-length guard is sufficient for every lower
record read, including the last record's sixteen siblings. -/
theorem cap_parse_lower_exists (values : Index → Entry) (indices : List Index)
    (proof : List Digest) (enough : 17 * indices.length ≤ proof.length) :
    ∃ records rest, capParseLower values indices proof = some (records, rest) := by
  induction indices generalizing proof with
  | nil => exact ⟨[], proof, rfl⟩
  | cons index indices ih =>
      cases proof with
      | nil => simp at enough
      | cons salt tail =>
          have lowerEnough : 16 ≤ tail.length := by
            simp only [List.length_cons] at enough
            omega
          have tailEnough : 17 * indices.length ≤ (tail.drop 16).length := by
            simp only [List.length_cons] at enough
            simp only [List.length_drop]
            omega
          obtain ⟨records, rest, parsed⟩ := ih (tail.drop 16) tailEnough
          exact ⟨⟨index, values index, salt, fun level => tail[level.val]?.getD 0⟩ :: records,
            rest, by simp [capParseLower, lowerEnough, parsed]⟩

/-- The actual empty-position convention is handled outside the nonempty cap
core: only the empty proof accepts, with no public query. -/
def capCheckParsedQ (indices : List Index) (values : Index → Entry)
    (proof : List Digest) (root : Digest) : OracleComp World (Option (List (BitVec 512))) :=
  if indices = [] then pure (if proof = [] then some [] else none)
  else
    match capParseLower values indices proof with
    | none => pure none
    | some (records, capProof) => capReplayBatch records capProof root

theorem cap_check_parsed_query_bound (indices : List Index) (values : Index → Entry)
    (proof : List Digest) (root : Digest) :
    IsTotalQueryBound (capCheckParsedQ indices values proof root) (32 * indices.length) := by
  unfold capCheckParsedQ
  by_cases empty : indices = []
  · simp only [empty, ↓reduceIte]; trivial
  · simp only [empty, ↓reduceIte]
    cases parsed : capParseLower values indices proof with
    | none => trivial
    | some pair =>
        rcases pair with ⟨records, capProof⟩
        have count := (cap_parse_lower_facts values indices proof records capProof parsed).1
        simpa only [count] using cap_replay_batch_position_bound records capProof root

theorem cap_check_parsed_empty (values : Index → Entry) (proof : List Digest) (root : Digest) :
    capCheckParsedQ [] values proof root =
      pure (if proof = [] then some [] else none) := by
  simp [capCheckParsedQ]
end CommitGolfCandidate
