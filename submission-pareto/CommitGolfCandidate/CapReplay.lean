import CommitGolfCandidate.CapWitness
import CommitGolfCandidate.CapQueries

/-! Instrumented cap replay. Inputs are retained only after issuing the actual
public compression query. The reply transcript is not a free oracle evaluation. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

abbrev CapReplayResult := Digest × List Digest × List (BitVec 512)

def capReplayQ : {height : Nat} → CapView height → List Digest →
    OracleComp World (Option CapReplayResult)
  | _, view, proof =>
      if capOccupied view then
        match view with
        | .leaf known => pure (known.map (fun value => (value, proof, [])))
        | .node left right => do
            let leftResult ← capReplayQ left proof
            match leftResult with
            | none => pure none
            | some (lroot, rest, leftInputs) =>
                let rightResult ← capReplayQ right rest
                match rightResult with
                | none => pure none
                | some (rroot, rest', rightInputs) =>
                    let input := rroot ++ lroot
                    let root ← (liftM (World.query (.inr (.inl input))) : OracleComp World Digest)
                    return some (root, rest', leftInputs ++ rightInputs ++ [input])
      else pure (match proof with
        | [] => none
        | value :: rest => some (value, rest, []))

/-- Successful witness traces agree with the instrumented public-query replay,
and every recorded compression input is paid once. -/
theorem cap_replay_witness_run (oracle : Oracle) {height : Nat}
    {view : CapView height} {proof rest : List Digest} {root : Digest}
    {inputs : List (BitVec 512)}
    (witness : CapDecodeWitness oracle.compression view proof root rest inputs) :
    oracle.run (capReplayQ view proof) = pure (some (root, rest, inputs), inputs.length) := by
  induction witness with
  | unknown view root rest unoccupied =>
      cases view <;> simp [capReplayQ, unoccupied, oracle_run_pure]
  | known value proof => simp [capReplayQ, capOccupied, oracle_run_pure]
  | node left right proof rest rest' lroot rroot leftInputs rightInputs occupied
      leftDecoded rightDecoded ihLeft ihRight =>
      simp only [capReplayQ, occupied, ↓reduceIte]
      erw [oracle_run_bind, ihLeft]
      simp only [pure_bind]
      erw [oracle_run_bind, ihRight]
      simp only [pure_bind]
      erw [oracle_run_public_bind oracle (.inl _)]
      simp only [oracle_run_pure, pure_bind]
      simp [combine, Oracle.answer, List.length_append]
      rfl

/-- Universal continuation accounting includes early parser failures and arbitrary
compression replies, independently of the successful fixed-oracle witness theorem. -/
theorem cap_replay_query_bound {height : Nat} (view : CapView height) (proof : List Digest) :
    IsTotalQueryBound (capReplayQ view proof) (capCalls view) := by
  induction view generalizing proof with
  | leaf known =>
      by_cases h : known.isSome = true <;>
        simp only [capReplayQ, capOccupied, h, ↓reduceIte, capCalls] <;> trivial
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (.node left right) = true
      · simp only [capReplayQ, h, ↓reduceIte, capCalls]
        rw [Nat.add_assoc]
        apply isTotalQueryBound_bind (ihLeft proof)
        intro leftResult
        cases leftResult with
        | none => trivial
        | some result =>
            rcases result with ⟨lroot, rest, leftInputs⟩
            apply isTotalQueryBound_bind (ihRight rest)
            intro rightResult
            cases rightResult with
            | none => trivial
            | some result =>
                rcases result with ⟨rroot, rest', rightInputs⟩
                erw [isTotalQueryBound_query_bind_iff]
                exact ⟨by decide, fun _ => by trivial⟩
      · simp only [capReplayQ, h, ↓reduceIte, capCalls]
        trivial

/-- Arbitrary accepted cap proofs admit a paid replay trace containing every
known leaf's authentication path to the accepted root. -/
theorem cap_accepted_replay_path (oracle : Oracle) {height : Nat}
    (view : CapView height) (proof rest : List Digest) (root : Digest)
    (accepted : capDecode oracle.compression view proof = some (root, rest))
    (path : Path height) (value : Digest) (known : capLeafValue view path = some value) :
    ∃ inputs : List (BitVec 512),
      oracle.run (capReplayQ view proof) = pure (some (root, rest, inputs), inputs.length) ∧
      ∃ siblings : List (Bool × Digest), siblings.length = height ∧
        siblings.map Prod.fst = capPathBits path ∧
        climb oracle.compression value siblings = root ∧
        ∀ input ∈ pathInputs oracle.compression value siblings, input ∈ inputs := by
  obtain ⟨inputs, witness⟩ := cap_decode_witness oracle.compression view proof rest root accepted
  exact ⟨inputs, cap_replay_witness_run oracle witness,
    cap_witness_path oracle.compression witness path value known⟩
end CommitGolfCandidate
