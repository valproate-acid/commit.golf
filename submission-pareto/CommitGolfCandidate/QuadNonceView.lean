import CommitGolfCandidate.QuadNonceSpec
import CommitGolfCandidate.NonceChainView

/-! Quad analogue of `NonceChainView`: the public view is produced by a public-query computation
(leaf digests `2·LENGTH` queries, then the `LENGTH/4` quad nodes) so the nonce-chain replacement
theorem `nonce_chain_oracle_distance` applies. The quad node function is tabulated on the honest
group inputs only; `QuadBuildLocal` says the builder needs nothing else. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
local instance quadChainDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192

def queryQuadNode (ds : DigestTape) (g : Nat) : OracleComp World (BitVec 256) := do
  let a ← World.query (.inr (.inr (.inl (quadInput (quadGroupLeaves ds g)))))
  return a.extractLsb' 0 256

theorem query_quad_node_bound (ds : DigestTape) (g : Nat) : PublicQueryBound (queryQuadNode ds g) 1 := by
  unfold queryQuadNode
  exact ⟨(by change 1 ≤ 1; omega), fun _ => trivial⟩

theorem query_quad_node_run (o : Oracle) (ds : DigestTape) (g : Nat) :
    fixedOracleRun o (queryQuadNode ds g) = pure (quadFunction o.permutation (quadGroupLeaves ds g)) := by
  rw [queryQuadNode, fixed_oracle_run_public, fixed_oracle_run_pure]
  rfl

open Classical in
/-- Node table read back as a function: value of the first group whose leaves equal the input. -/
noncomputable def quadTable (ds : DigestTape) (ns : List (BitVec 256)) : QuadFunction := fun c =>
  if h : ∃ g, g < LENGTH / 4 ∧ quadGroupLeaves ds g = c then ns[Classical.choose h]?.getD 0 else 0

theorem quad_table_agrees (π : Block → Block) (ds : DigestTape) (g : Nat) (inside : g < LENGTH / 4) :
    quadTable ds ((List.range (LENGTH / 4)).map fun j => quadFunction π (quadGroupLeaves ds j))
      (quadGroupLeaves ds g) = quadFunction π (quadGroupLeaves ds g) := by
  have h : ∃ j, j < LENGTH / 4 ∧ quadGroupLeaves ds j = quadGroupLeaves ds g := ⟨g, inside, rfl⟩
  unfold quadTable
  rw [dif_pos h]
  obtain ⟨lt, eq⟩ := Classical.choose_spec h
  rw [List.getElem?_map, List.getElem?_range lt]
  simp only [Option.map_some, Option.getD_some, eq]

noncomputable def queryQuad (ds : DigestTape) : OracleComp World QuadFunction := do
  let ns ← queryList (queryQuadNode ds) (List.range (LENGTH / 4))
  return quadTable ds ns

attribute [local irreducible] List.range queryList queryQuadNode

theorem query_quad_bound (ds : DigestTape) : PublicQueryBound (queryQuad ds) (LENGTH / 4) := by
  have h := public_query_bound_bind (query_list_bound _ 1 (query_quad_node_bound ds) (List.range (LENGTH / 4)))
    (fun ns => show PublicQueryBound (pure (quadTable ds ns) : OracleComp World _) 0 from trivial)
  simpa only [queryQuad, List.length_range, Nat.add_zero, Nat.mul_one] using h

theorem query_quad_run (o : Oracle) (ds : DigestTape) :
    fixedOracleRun o (queryQuad ds) =
      pure (quadTable ds ((List.range (LENGTH / 4)).map fun j => quadFunction o.permutation (quadGroupLeaves ds j))) := by
  rw [queryQuad, fixed_oracle_run_bind,
    query_list_reference o _ _ _ (fun g _ => query_quad_node_run o ds g), pure_bind, fixed_oracle_run_pure]

noncomputable def chainQuadComp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (build : QuadTranscriptBuilder) (c : Compression) (b : Bool) (r : CompleteSaltTape) :
    OracleComp World O := do
  let ch ← a.choose
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let qf ← queryQuad ds
  let view := build c qf ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] queryDigests guardedView queryQuad

theorem chain_quad_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (c : Compression) (b : Bool)
    (r : CompleteSaltTape) :
    PublicQueryBound (chainQuadComp a t build c b r) (t + 2*LENGTH + LENGTH/4 + t) := by
  unfold chainQuadComp
  rw [show t + 2*LENGTH + LENGTH/4 + t = t + (2*LENGTH + (LENGTH/4 + t)) by omega]
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (query_digests_bound _ _)
  intro ds
  apply public_query_bound_bind (query_quad_bound _)
  intro qf
  exact guarded_view_bound a t ch.aux _ _

theorem chain_quad_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : QuadTranscriptBuilder) (isLocal : QuadBuildLocal build)
    (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (chainQuadComp a t build o.compression b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (quadHonestView build) o.compression ch b
            (BiPermutation.equiv Block o.permutation) r) := by
  rw [chainQuadComp, fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind, query_digests_run, pure_bind, fixed_oracle_run_bind, query_quad_run, pure_bind,
    reached_view o a h ch hit]
  have same := isLocal o.compression _ (quadFunction o.permutation) ch.positions (fun i => r i.val)
    (pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) (if b then ch.message₁ else ch.message₀) r)
    (fun g inside => quad_table_agrees o.permutation _ g inside)
  rw [same]
  simp only [observeTranscriptView, quadHonestView, fixedOracle, Equiv.symm_apply_apply]
  rfl

end TwoPermutationPrototype.Sampling
