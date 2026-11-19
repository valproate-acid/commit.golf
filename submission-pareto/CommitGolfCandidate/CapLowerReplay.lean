import CommitGolfCandidate.BindingReplay
import CommitGolfCandidate.CapConsistency

/-! Paid replay of the sixteen-level lower records. The parser and machine
bridges remain separate: these records explicitly contain a salt and exactly
sixteen siblings, with every direction fixed by the original ABI index. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

structure CapLowerRecord where
  index : Index
  value : Entry
  salt : Digest
  sibling : Fin 16 → Digest

def CapLowerRecord.path (record : CapLowerRecord) : List (Bool × Digest) :=
  List.ofFn fun level : Fin 16 => (record.index.val.testBit level.val, record.sibling level)

theorem cap_lower_path_length (record : CapLowerRecord) : record.path.length = 16 := by
  simp [CapLowerRecord.path]

theorem cap_lower_path_directions (record : CapLowerRecord) :
    record.path.map Prod.fst = (List.range 16).map record.index.val.testBit := by
  rw [CapLowerRecord.path, List.map_ofFn, List.ofFn_eq_map]
  change (List.finRange 16).map (record.index.val.testBit ∘ Fin.val) = _
  rw [← List.map_map, List.map_coe_finRange_eq_range]

def CapLowerRecord.root (record : CapLowerRecord) (compress : Compression) : Digest :=
  climb compress (leafDigest compress record.salt record.value) record.path

def CapLowerRecord.inputs (record : CapLowerRecord) (compress : Compression) :
    List (BitVec 512) :=
  openingInputs compress record.salt record.value record.path

theorem cap_lower_inputs_length (record : CapLowerRecord) (compress : Compression) :
    (record.inputs compress).length = 24 := by
  rw [CapLowerRecord.inputs, openingInputs_length, cap_lower_path_length]

/-- Each retained input was queried through World before it is returned. -/
def capReplayLower (record : CapLowerRecord) : OracleComp World (Digest × List (BitVec 512)) := do
  let (leaf, leafInputs) ← replayChain record.salt (leafBlocks record.value)
  let (root, lowerInputs) ← replayPath leaf record.path
  return (root, leafInputs ++ lowerInputs)

theorem cap_replay_lower_run (oracle : Oracle) (record : CapLowerRecord) :
    oracle.run (capReplayLower record) =
      pure ((record.root oracle.compression, record.inputs oracle.compression), 24) := by
  simp only [capReplayLower, oracle_run_bind, replay_chain_run, pure_bind,
    bind_pure_comp, oracle_run_map, replay_path_run, map_pure]
  simp [CapLowerRecord.root, CapLowerRecord.inputs, openingInputs,
    leafDigest_eq_fold, leafBlocks, cap_lower_path_length]

/-- This bound holds for all replies, including replies inconsistent with a fixed
compression function. A record always pays eight leaf and sixteen lower calls. -/
theorem cap_replay_lower_query_bound (record : CapLowerRecord) :
    IsTotalQueryBound (capReplayLower record) 24 := by
  unfold capReplayLower
  change IsTotalQueryBound (_ >>= _) (8 + 16)
  apply isTotalQueryBound_bind
  · simpa [leafBlocks] using replay_chain_query_bound record.salt (leafBlocks record.value)
  · rintro ⟨leaf, inputs⟩
    simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff,
      cap_lower_path_length] using replay_path_query_bound leaf record.path

/-- Forward duplicate checking occurs after the current record's paid queries,
before any queries for the next record. -/
def capReplayLowerBatch : List CapLowerRecord → CapRootMap →
    OracleComp World (Option (CapRootMap × List (BitVec 512)))
  | [], roots => pure (some (roots, []))
  | record :: rest, roots => do
      let (root, inputs) ← capReplayLower record
      match capInsert roots (capGroup record.index).val root with
      | none => pure none
      | some next =>
          let result ← capReplayLowerBatch rest next
          return result.map fun (finalRoots, laterInputs) => (finalRoots, inputs ++ laterInputs)

def capLowerBatchRoots (compress : Compression) : List CapLowerRecord → CapRootMap →
    Option CapRootMap
  | [], roots => some roots
  | record :: rest, roots => do
      let next ← capInsert roots (capGroup record.index).val (record.root compress)
      capLowerBatchRoots compress rest next

def capLowerBatchInputs (compress : Compression) (records : List CapLowerRecord) :
    List (BitVec 512) :=
  records.flatMap fun record => record.inputs compress

theorem cap_lower_batch_inputs_length (compress : Compression) (records : List CapLowerRecord) :
    (capLowerBatchInputs compress records).length = 24 * records.length := by
  induction records with
  | nil => simp [capLowerBatchInputs]
  | cons record rest ih =>
      simp only [capLowerBatchInputs, List.flatMap_cons, List.length_append,
        cap_lower_inputs_length] at ih ⊢
      simp only [List.length_cons]
      omega

theorem cap_replay_lower_batch_query_bound (records : List CapLowerRecord) (roots : CapRootMap) :
    IsTotalQueryBound (capReplayLowerBatch records roots) (24 * records.length) := by
  induction records generalizing roots with
  | nil => trivial
  | cons record rest ih =>
      simp only [capReplayLowerBatch, List.length_cons, Nat.mul_add, Nat.mul_one]
      rw [Nat.add_comm]
      apply isTotalQueryBound_bind (cap_replay_lower_query_bound record)
      rintro ⟨root, inputs⟩
      cases inserted : capInsert roots (capGroup record.index).val root with
      | none => trivial
      | some next =>
          simpa only [bind_pure_comp, IsTotalQueryBound, isQueryBound_map_iff] using ih next

/-- Successful fixed-oracle evaluation returns the concatenation of precisely the
paid lower-record inputs. No query is omitted by a duplicate-group reuse. -/
theorem cap_replay_lower_batch_run (oracle : Oracle) (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap)
    (accepted : capLowerBatchRoots oracle.compression records roots = some finalRoots) :
    oracle.run (capReplayLowerBatch records roots) =
      pure (some (finalRoots, capLowerBatchInputs oracle.compression records), 24 * records.length) := by
  induction records generalizing roots with
  | nil =>
      simp only [capLowerBatchRoots, Option.some.injEq] at accepted
      subst finalRoots
      simp [capReplayLowerBatch, capLowerBatchInputs, oracle_run_pure]
  | cons record rest ih =>
      cases inserted : capInsert roots (capGroup record.index).val (record.root oracle.compression) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          have later : capLowerBatchRoots oracle.compression rest next = some finalRoots := by
            simpa [capLowerBatchRoots, inserted] using accepted
          simp only [capReplayLowerBatch]
          erw [oracle_run_bind, cap_replay_lower_run]
          simp only [pure_bind, inserted]
          erw [oracle_run_bind, ih next later]
          simp [oracle_run_pure, capLowerBatchInputs, Nat.mul_add, Nat.add_comm]

/-- An accepted suffix preserves roots that were already known at its entry. -/
theorem cap_lower_batch_preserves (compress : Compression) (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap) (group : Nat) (value : Digest)
    (accepted : capLowerBatchRoots compress records roots = some finalRoots)
    (known : roots group = some value) : finalRoots group = some value := by
  induction records generalizing roots with
  | nil =>
      simp only [capLowerBatchRoots, Option.some.injEq] at accepted
      subst finalRoots
      exact known
  | cons record rest ih =>
      cases inserted : capInsert roots (capGroup record.index).val (record.root compress) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          apply ih next (by simpa [capLowerBatchRoots, inserted] using accepted)
          exact cap_insert_preserves roots next _ group _ value inserted known

/-- Every accepted record, including a duplicate, agrees with the retained group
root. This is the lower-root premise needed by the cap path extractor. -/
theorem cap_lower_batch_member (compress : Compression) (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap)
    (accepted : capLowerBatchRoots compress records roots = some finalRoots)
    (record : CapLowerRecord) (member : record ∈ records) :
    finalRoots (capGroup record.index).val = some (record.root compress) := by
  induction records generalizing roots with
  | nil => simp at member
  | cons head rest ih =>
      cases inserted : capInsert roots (capGroup head.index).val (head.root compress) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          have later : capLowerBatchRoots compress rest next = some finalRoots := by
            simpa [capLowerBatchRoots, inserted] using accepted
          rcases List.mem_cons.mp member with same | laterMember
          · subst head
            apply cap_lower_batch_preserves compress rest next finalRoots _ _ later
            rw [cap_insert_lookup roots next _ _ _ inserted]
            simp
          · exact ih next later laterMember
end CommitGolfCandidate
