import CommitGolfCandidate.TwoPermutationPinnedReplay
import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.ProjectedCompression
import CommitGolfCandidate.TwoPermutationCheckerReplay

/-! Paid binding for the packed two-permutation design. Each compression row
retains the actual full reply while its child authentication step receives
the same two-byte-zeroed digest as the projected checker. -/
namespace TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker OracleComp

private theorem equal_path_pair {node : Nat} {child₀ sibling₀ child₁ sibling₁ : BitVec 256}
    (same : pathPair node child₀ sibling₀ = pathPair node child₁ sibling₁) : child₀ = child₁ := by
  by_cases parity : node % 2 = 0
  · simp only [pathPair, ite_eq_left parity] at same
    have hit := congrArg (fun packed : BitVec 512 => packed.extractLsb' 0 256) same
    exact BitVec.extractLsb'_append_eq_right.symm.trans (hit.trans BitVec.extractLsb'_append_eq_right)
  · simp only [pathPair, ite_eq_right parity] at same
    have hit := congrArg (fun packed : BitVec 512 => packed.extractLsb' 256 256) same
    exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)

/-- A proof path only cites compression rows actually recorded during the check. -/
inductive ProjectedPath (rows : List PublicRow) : Nat → Nat → BitVec 256 → BitVec 256 → Prop where
  | done (node : Nat) (digest : BitVec 256) : ProjectedPath rows node 0 digest digest
  | step {node height : Nat} {child parent sibling root : BitVec 256}
      (call : PublicRow.compression (pathPair node child sibling) parent ∈ rows)
      (next : ProjectedPath rows (node / 2) height (padLow parent) root) :
      ProjectedPath rows node (height + 1) child root

theorem ProjectedPath.mono {first last : List PublicRow} {node height : Nat}
    {start finish : BitVec 256} (path : ProjectedPath first node height start finish)
    (contained : ∀ row ∈ first, row ∈ last) : ProjectedPath last node height start finish := by
  induction path with
  | done node digest => exact .done node digest
  | step call _ ih => exact .step (contained _ call) ih

theorem ProjectedPath.append {rows : List PublicRow} {node m n : Nat} {start middle finish : BitVec 256}
    (first : ProjectedPath rows node m start middle)
    (last : ProjectedPath rows (node / 2 ^ m) n middle finish) :
    ProjectedPath rows node (m + n) start finish := by
  induction first with
  | done node digest =>
    simpa using last
  | @step node height child parent sibling root call next ih =>
    have address : node / 2 ^ (height + 1) = (node / 2) / 2 ^ height := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    rw [address] at last
    rw [show height + 1 + n = (height + n) + 1 by omega]
    exact .step call (ih last)

/-- Two accepted paths for the same leaf either have equal leaf digests or
expose a collision in the recorded compression rows. -/
theorem ProjectedPath.compare {rows : List PublicRow} {node height : Nat}
    {start₀ start₁ root : BitVec 256}
    (left : ProjectedPath rows node height start₀ root)
    (right : ProjectedPath rows node height start₁ root) :
    CompressionWitness rows ∨ start₀ = start₁ := by
  induction height generalizing node start₀ start₁ root with
  | zero =>
    cases left
    cases right
    exact Or.inr rfl
  | succ height ih =>
    cases left with
    | @step _ _ _ parent₀ sibling₀ _ call₀ tail₀ =>
      cases right with
      | @step _ _ _ parent₁ sibling₁ _ call₁ tail₁ =>
        rcases ih tail₀ tail₁ with collision | sameParent
        · exact Or.inl collision
        by_cases sameInput : pathPair node start₀ sibling₀ = pathPair node start₁ sibling₁
        · exact Or.inr (equal_path_pair sameInput)
        · exact Or.inl ⟨_, _, _, _, call₀, call₁, sameInput, (low240_padLow parent₀).symm.trans ((congrArg low240 sameParent).trans (low240_padLow parent₁))⟩

/-- The two forward permutation rows and the subsequent authenticated path for
an opened index, all in a single genuine checker replay. -/
structure ProjectedOpening (oracle : Oracle) (index : Index) (entry : Entry) (root : Commitment)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (pinnedFirstRow oracle.permutation (entryWords entry)).1
    (pinnedFirstRow oracle.permutation (entryWords entry)).2 ∈ rows
  second : PublicRow.permutation
    (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).1
    (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2 ∈ rows
  path : ProjectedPath rows (LENGTH + index.val) LOG_LENGTH
    (outputDigest (pinnedSecondRow oracle.permutation index nonce
      (pinnedFirstRow oracle.permutation (entryWords entry)).2 (entryWords entry)).2) root

theorem projected_openings_conflict (oracle : Oracle) (index : Index) (root : Commitment)
    (value₀ value₁ : Entry) (conflict : value₀ ≠ value₁)
    (rows₀ rows₁ : List PublicRow) (left : ProjectedOpening oracle index value₀ root rows₀)
    (right : ProjectedOpening oracle index value₁ root rows₁) :
    PinnedReplayEvidence (rows₀ ++ rows₁) := by
  rcases (left.path.mono (fun _ h => List.mem_append_left _ h)).compare
    (right.path.mono (fun _ h => List.mem_append_right _ h)) with hash | sameLeaf
  · exact Or.inl hash
  · exact Or.inr ⟨oracle.permutation, index, left.nonce, right.nonce, entryWords value₀, entryWords value₁,
      List.mem_append_left _ left.first, List.mem_append_right _ right.first,
      List.mem_append_left _ left.second, List.mem_append_right _ right.second,
      sameLeaf, fun same => conflict (entry_words_injective same)⟩

def PackedAcceptedTrace (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := checkObservation s oracle input
    observed.1.1.exit = .success →
      observed.2 ≤ 2^30 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (ProjectedOpening oracle index.val (input.values index) input.commitment observed.1.2)

private theorem packed_limited_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^30) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^30))) =
      pure (some (checkObservation s oracle input).1.1, (checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^30)).record.fixed oracle, coinFree.limit_recorded oracle _ fits]
  rfl

theorem packed_replay_extracts (s : Submission) (refines : PackedAcceptedTrace s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), PinnedReplayEvidence result.2 := by
  obtain ⟨⟨index, member₀, member₁, conflict⟩, accepted₀, accepted₁⟩ := breaks
  let x := leftCheck claim
  let y := rightCheck claim
  have good₀ := checked_acceptance s oracle x accepted₀
  have good₁ := checked_acceptance s oracle y accepted₁
  obtain ⟨fits₀, path₀⟩ := refines oracle x good₀
  obtain ⟨fits₁, path₁⟩ := refines oracle y good₁
  have replay : fixedOracleRun oracle (recordRows (checkerReplay s claim)) =
      pure ((), (checkObservation s oracle x).1.2 ++ (checkObservation s oracle y).1.2) := by
    unfold checkerReplay
    change fixedOracleRun oracle
      (recordRows (do
        let _ ← limitPublicQueries (s.run .check x) (2^30)
        let _ ← limitPublicQueries (s.run .check y) (2^30)
        pure ())) = _
    have tail : fixedOracleRun oracle
        (recordRows (do let _ ← limitPublicQueries (s.run .check y) (2^30); pure ())) =
        pure ((), (checkObservation s oracle y).1.2) := by
      rw [record_rows_bind, fixed_oracle_run_bind, packed_limited_check s oracle y fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, packed_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure, Set.mem_singleton_iff] at found
  subst result
  exact projected_openings_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index, member₀⟩).some (path₁ ⟨index, member₁⟩).some

def packed_binding_replay (s : Submission) (specified : PackedAcceptedTrace s) :
    BindingReplayEvidence s.scheme PinnedReplayEvidence :=
  ⟨checkerReplay s, checker_replay_bounded s, packed_replay_extracts s specified⟩

theorem binding_of_packed_trace (candidate : Submission) (trace : PackedAcceptedTrace candidate)
    (bound : PinnedReplayBound) : candidate.scheme.Binding :=
  scheme_binding_of_replay_with candidate.scheme (packed_binding_replay candidate trace)
    (fun contained witness => witness.mono contained) bound

end TwoPermutationPrototype.Packed
