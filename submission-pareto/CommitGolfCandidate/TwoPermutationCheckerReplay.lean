import CommitGolfCandidate.TwoPermutationCheckerRecording

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp
open TwoPermutationPrototype.Sampling

def leftCheck (claim : Scheme.Claim) : CheckInput :=
  ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩

def rightCheck (claim : Scheme.Claim) : CheckInput :=
  ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩

def checkObservation (s : Submission) (oracle : Oracle) (input : CheckInput) :
    (Execution × List PublicRow) × Nat :=
  checkEvaluation oracle (recordRows (s.run .check input))

/-- Every genuinely accepted index has both forward leaf rows and a complete
24-level authentication path in the trace. The replay needs no information
about rejected paths beyond the structural limiter. -/
def AcceptedTraceRefines (s : Submission) : Prop :=
  ∀ (oracle : Oracle) (input : CheckInput),
    let observed := checkObservation s oracle input
    observed.1.1.exit = .success →
      observed.2 ≤ 2^30 ∧
      ∀ index : {i // i ∈ input.positions},
        Nonempty (RecordedOpening oracle index.val (input.values index) input.commitment observed.1.2)

def checkerReplay (s : Submission) (claim : Scheme.Claim) : OracleComp World Unit := do
  let _ ← limitPublicQueries (s.run .check (leftCheck claim)) (2^30)
  let _ ← limitPublicQueries (s.run .check (rightCheck claim)) (2^30)
  pure ()

theorem checker_replay_bounded (s : Submission) (claim : Scheme.Claim) :
    PublicQueryBound (checkerReplay s claim) (2^31) := by
  unfold checkerReplay
  change PublicQueryBound (_ >>= _) (2^30 + 2^30)
  apply public_query_bound_bind (limit_public_bound _ _)
  intro _
  change PublicQueryBound (_ >>= _) (2^30 + 0)
  apply public_query_bound_bind (limit_public_bound _ _)
  intro _
  trivial

theorem checked_acceptance (s : Submission) (oracle : Oracle) (input : CheckInput)
    (accepted : (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).1 = true) :
    (checkObservation s oracle input).1.1.exit = .success := by
  rw [scheme_check_evaluation] at accepted
  have erase := check_record_erase oracle (s.run .check input)
  change ((checkObservation s oracle input).1.1, (checkObservation s oracle input).2) = _ at erase
  rw [← erase] at accepted
  exact (beq_iff_eq).mp accepted

private theorem one_limited_check (s : Submission) (oracle : Oracle) (input : CheckInput)
    (fits : (checkObservation s oracle input).2 ≤ 2^30) :
    fixedOracleRun oracle (recordRows (limitPublicQueries (s.run .check input) (2^30))) =
      pure (some (checkObservation s oracle input).1.1, (checkObservation s oracle input).1.2) := by
  have coinFree := check_public_only s input
  rw [(coinFree.limit (2^30)).record.fixed oracle, coinFree.limit_recorded oracle _ fits]
  rfl

theorem checker_replay_extracts (s : Submission) (refines : AcceptedTraceRefines s)
    (oracle : Oracle) (claim : Scheme.Claim) (breaks : s.scheme.Breaks oracle claim) :
    ∀ result ∈ support (fixedOracleRun oracle (recordRows (checkerReplay s claim))), ReplayEvidence result.2 := by
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
      rw [record_rows_bind, fixed_oracle_run_bind, one_limited_check s oracle y fits₁]
      simp [record_rows_pure, fixed_oracle_run_pure, fixed_oracle_run_bind]
    rw [record_rows_bind, fixed_oracle_run_bind, one_limited_check s oracle x fits₀]
    simp only [pure_bind]
    rw [fixed_oracle_run_bind, tail]
    simp [fixed_oracle_run_pure]
  rw [replay]
  intro result found
  simp only [support_pure, Set.mem_singleton_iff] at found
  subst result
  exact recorded_openings_conflict oracle index claim.root _ _ conflict _ _
    (path₀ ⟨index, member₀⟩).some (path₁ ⟨index, member₁⟩).some

def binding_replay_from_trace (s : Submission) (specified : AcceptedTraceRefines s) :
    BindingReplayRefines s.scheme :=
  ⟨checkerReplay s, checker_replay_bounded s, checker_replay_extracts s specified⟩

end TwoPermutationPrototype.Checker
