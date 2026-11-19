import CommitGolfCandidate.CapMultiproof
import CommitGolfCandidate.Counting
import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-! Public-query semantics of cap reconstruction. All hash calls go through World;
this is a reference interpreter, not a machine execution bridge. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec

/-- Canonical left-before-right reconstruction, with explicit public compression queries. -/
def capDecodeQ : {height : Nat} → CapView height → List Digest →
    OracleComp World (Option (Digest × List Digest))
  | _, view, proof =>
      if capOccupied view then
        match view with
        | .leaf known => pure (known.map (fun value => (value, proof)))
        | .node left right => do
            let leftResult ← capDecodeQ left proof
            match leftResult with
            | none => pure none
            | some (lroot, rest) =>
                let rightResult ← capDecodeQ right rest
                match rightResult with
                | none => pure none
                | some (rroot, rest') =>
                    let root ← (liftM (World.query (.inr (.inl (rroot ++ lroot)))) : OracleComp World Digest)
                    return some (root, rest')
      else pure (match proof with
        | [] => none
        | value :: rest => some (value, rest))

/-- Honest canonical reconstruction uses precisely the counted cap queries and no coins. -/
theorem cap_decodeQ_honest_run (oracle : Oracle) {height : Nat} (tree : Tree height)
    (marked : Nat → Bool) (rest : List Digest) :
    oracle.run (capDecodeQ (capView tree marked)
      (capProof oracle.compression tree (capView tree marked) ++ rest)) =
      pure (some (Tree.root oracle.compression tree, rest), capCalls (capView tree marked)) := by
  induction tree generalizing marked rest with
  | leaf value =>
      by_cases h : marked 0 = true <;>
        simp [capView, capProof, capDecodeQ, capOccupied, capCalls, Tree.root, h, oracle_run_pure]
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (capView (.node left right) marked) = true
      · simp only [capView] at h ⊢
        simp only [capProof, h, ↓reduceIte, capDecodeQ, List.append_assoc]
        erw [oracle_run_bind, ihLeft]
        simp only [pure_bind]
        erw [oracle_run_bind, ihRight]
        simp only [pure_bind]
        erw [oracle_run_public_bind oracle (.inl _)]
        simp only [oracle_run_pure, pure_bind]
        simp [capCalls, h, Tree.root, combine, Oracle.answer]
        exact ⟨rfl, by omega⟩
      · simp only [capView] at h ⊢
        simp [capProof, capDecodeQ, capCalls, h, oracle_run_pure]

/-- A structural query bound for every proof and every possible reply continuation,
including malformed proofs and replies not consistent with any fixed oracle. -/
theorem cap_decodeQ_query_bound {height : Nat} (view : CapView height) (proof : List Digest) :
    IsTotalQueryBound (capDecodeQ view proof) (capCalls view) := by
  induction view generalizing proof with
  | leaf known =>
      by_cases h : known.isSome = true <;> simp only [capDecodeQ, capOccupied, h, ↓reduceIte, capCalls] <;> trivial
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (.node left right) = true
      · simp only [capDecodeQ, h, ↓reduceIte, capCalls]
        rw [Nat.add_assoc]
        apply isTotalQueryBound_bind (ihLeft proof)
        intro leftResult
        cases leftResult with
        | none => trivial
        | some result =>
          rcases result with ⟨lroot, rest⟩
          apply isTotalQueryBound_bind (ihRight rest)
          intro rightResult
          cases rightResult with
          | none => trivial
          | some result =>
            rcases result with ⟨rroot, rest'⟩
            erw [isTotalQueryBound_query_bind_iff]
            exact ⟨by decide, fun _ => by trivial⟩
      · simp only [capDecodeQ, h, ↓reduceIte, capCalls]
        trivial
end CommitGolfCandidate
