import CommitGolfCandidate.QuadNonceView
import CommitGolfCandidate.PentaHidingRows

/-! Penta analogue of `QuadNonceView`: the public view is produced by a public-query computation
(leaf digests `2·LENGTH` queries, then the honest inputs of levels 1 … 11 of the 5-ary tree, level by
level) so the nonce-chain replacement theorem applies. The node function is tabulated on those
inputs only; `PentaBuildLocal` says the builder needs nothing else. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate
local instance pentaChainDiscrete {α : Type} : MeasurableSpace α := ⊤
set_option maxRecDepth 8192

/-- Nodes agree up to level `n` when the two functions agree on `g`'s honest inputs below `n`. -/
theorem penta_node_congr_upto (f g : PentaFunction) (leaves : DigestTape) (n : Nat)
    (same : ∀ k j, k < n → j < pentaCount (k + 1) → f (pentaGroup g leaves k j) = g (pentaGroup g leaves k j)) :
    ∀ k, k ≤ n → ∀ j, pentaNode f leaves k j = pentaNode g leaves k j := by
  intro k
  induction k with
  | zero => intro _ j; rfl
  | succ k ih =>
    intro le j
    rw [pentaNode, pentaNode]
    split_ifs with inside
    · have children : (fun t : Fin 5 => pentaNode f leaves k (5 * j + t.val)) =
          (fun t : Fin 5 => pentaNode g leaves k (5 * j + t.val)) := by
        funext t; exact ih (by omega) _
      rw [children]
      exact same k j (by omega) inside
    · rfl

theorem penta_group_congr_upto (f g : PentaFunction) (leaves : DigestTape) (n : Nat)
    (same : ∀ k j, k < n → j < pentaCount (k + 1) → f (pentaGroup g leaves k j) = g (pentaGroup g leaves k j))
    (k : Nat) (le : k ≤ n) (j : Nat) : pentaGroup f leaves k j = pentaGroup g leaves k j := by
  funext t
  exact penta_node_congr_upto f g leaves n same k le _

def queryPentaNode (T : PentaFunction) (ds : DigestTape) (k j : Nat) : OracleComp World (BitVec 256) := do
  let a ← World.query (.inr (.inr (.inl (pentaInput (pentaGroup T ds k j)))))
  return a.extractLsb' 0 256

theorem query_penta_node_bound (T : PentaFunction) (ds : DigestTape) (k j : Nat) :
    PublicQueryBound (queryPentaNode T ds k j) 1 := by
  unfold queryPentaNode
  exact ⟨(by change 1 ≤ 1; omega), fun _ => trivial⟩

theorem query_penta_node_run (o : Oracle) (T : PentaFunction) (ds : DigestTape) (k j : Nat) :
    fixedOracleRun o (queryPentaNode T ds k j) = pure (pentaFunction o.permutation (pentaGroup T ds k j)) := by
  rw [queryPentaNode, fixed_oracle_run_public, fixed_oracle_run_pure]
  rfl

open Classical in
/-- Add the level-`k+1` inputs (computed with `T`) and their queried values to the table `T`. -/
noncomputable def extendPentaTable (ds : DigestTape) (k : Nat) (T : PentaFunction) (vs : List (BitVec 256)) :
    PentaFunction := fun c =>
  if h : ∃ j, j < pentaCount (k + 1) ∧ pentaGroup T ds k j = c then vs[Classical.choose h]?.getD 0 else T c

noncomputable def queryPentaLevels (ds : DigestTape) : Nat → OracleComp World PentaFunction
  | 0 => pure (fun _ => 0)
  | n + 1 => do
    let T ← queryPentaLevels ds n
    let vs ← queryList (queryPentaNode T ds n) (List.range (pentaCount (n + 1)))
    return extendPentaTable ds n T vs

def pentaQueries : Nat → Nat
  | 0 => 0
  | n + 1 => pentaQueries n + pentaCount (n + 1)

theorem penta_queries_value : pentaQueries PENTA_LEVELS = 4194308 := by decide

noncomputable def truePentaTable (π : Block → Block) (ds : DigestTape) : Nat → PentaFunction
  | 0 => fun _ => 0
  | n + 1 => extendPentaTable ds n (truePentaTable π ds n)
      ((List.range (pentaCount (n + 1))).map fun j => pentaFunction π (pentaGroup (truePentaTable π ds n) ds n j))

theorem query_penta_levels_bound (ds : DigestTape) :
    ∀ n, PublicQueryBound (queryPentaLevels ds n) (pentaQueries n) := by
  intro n
  induction n with
  | zero => trivial
  | succ n ih =>
    unfold queryPentaLevels pentaQueries
    apply public_query_bound_bind ih
    intro T
    have h := public_query_bound_bind
      (query_list_bound _ 1 (query_penta_node_bound T ds n) (List.range (pentaCount (n + 1))))
      (fun vs => show PublicQueryBound (pure (extendPentaTable ds n T vs) : OracleComp World _) 0 from trivial)
    simpa only [List.length_range, Nat.add_zero, Nat.mul_one] using h

theorem query_penta_levels_run (o : Oracle) (ds : DigestTape) :
    ∀ n, fixedOracleRun o (queryPentaLevels ds n) = pure (truePentaTable o.permutation ds n) := by
  intro n
  induction n with
  | zero => exact fixed_oracle_run_pure _ _
  | succ n ih =>
    rw [queryPentaLevels, fixed_oracle_run_bind, ih, pure_bind, fixed_oracle_run_bind,
      query_list_reference o _ _ _ (fun j _ => query_penta_node_run o _ ds n j), pure_bind, fixed_oracle_run_pure]
    rfl

/-- The true table agrees with the permutation on every honest input of levels `1 … n`. -/
theorem true_penta_table_agrees (π : Block → Block) (ds : DigestTape) :
    ∀ n, ∀ k j, k < n → j < pentaCount (k + 1) →
      truePentaTable π ds n (pentaGroup (pentaFunction π) ds k j) =
        pentaFunction π (pentaGroup (pentaFunction π) ds k j) := by
  intro n
  induction n with
  | zero => intro k j lt; omega
  | succ n ih =>
    intro k j lt inside
    have groups : pentaGroup (truePentaTable π ds n) ds n = pentaGroup (pentaFunction π) ds n := by
      funext j'
      exact penta_group_congr_upto _ _ ds n ih n le_rfl j'
    change extendPentaTable ds n (truePentaTable π ds n) _ _ = _
    unfold extendPentaTable
    split_ifs with found
    · obtain ⟨lt', eq⟩ := Classical.choose_spec found
      simp only [List.getElem?_map, List.getElem?_range lt', Option.map_some, Option.getD_some]
      exact congrArg (pentaFunction π) eq
    · have old : k < n := by
        by_contra notLess
        have kn : k = n := by omega
        subst kn
        exact found ⟨j, inside, by rw [groups]⟩
      exact ih k j old inside

theorem penta_table_build (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build) (o : Oracle)
    (ds : DigestTape) (positions : Positions) (salts : OpenedSalts positions) :
    build (truePentaTable o.permutation ds PENTA_LEVELS) positions salts ds =
      build (pentaFunction o.permutation) positions salts ds := by
  have agree := true_penta_table_agrees o.permutation ds PENTA_LEVELS
  apply isLocal
  intro k j lt inside
  rw [penta_group_congr_upto _ _ ds PENTA_LEVELS agree k (le_of_lt lt) j]
  exact agree k j lt inside

noncomputable def chainPentaComp {S O : Type} {n : Nat} (a : Hiding.HidingAdversary S O n)
    (t : Nat) (build : PentaTranscriptBuilder) (b : Bool) (r : CompleteSaltTape) :
    OracleComp World O := do
  let ch ← a.choose
  let ds ← queryDigests (if b then ch.message₁ else ch.message₀) r
  let qf ← queryPentaLevels ds PENTA_LEVELS
  let view := build qf ch.positions (fun i => r i.val) ds
  guardedView a t ch.aux view.1 view.2

attribute [local irreducible] queryDigests guardedView queryPentaLevels

theorem chain_penta_comp_bound {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (b : Bool) (r : CompleteSaltTape) :
    PublicQueryBound (chainPentaComp a t build b r) (t + 2*LENGTH + pentaQueries PENTA_LEVELS + t) := by
  unfold chainPentaComp
  rw [show t + 2*LENGTH + pentaQueries PENTA_LEVELS + t =
    t + (2*LENGTH + (pentaQueries PENTA_LEVELS + t)) by omega]
  apply public_query_bound_bind (hiding_choose_query_bound a h)
  intro ch
  apply public_query_bound_bind (query_digests_bound _ _)
  intro ds
  apply public_query_bound_bind (query_penta_levels_bound _ _)
  intro qf
  exact guarded_view_bound a t ch.aux _ _

theorem chain_penta_comp_run {S O : Type} {n t : Nat} (a : Hiding.HidingAdversary S O n)
    (h : Hiding.QueryBound a t) (build : PentaTranscriptBuilder) (isLocal : PentaBuildLocal build)
    (o : Oracle) (b : Bool) (r : CompleteSaltTape) :
    fixedOracleRun o (chainPentaComp a t build b r) =
      (do let ch ← fixedOracleRun o a.choose
          observeTranscriptView a (pentaView build) o.compression ch b
            (BiPermutation.equiv Block o.permutation) r) := by
  rw [chainPentaComp, fixed_oracle_run_bind]
  apply bind_congr_of_forall_mem_support
  intro ch hit
  rw [fixed_oracle_run_bind, query_digests_run, pure_bind, fixed_oracle_run_bind, query_penta_levels_run,
    pure_bind, reached_view o a h ch hit, penta_table_build build isLocal o]
  simp only [observeTranscriptView, pentaView, pentaHonestView, fixedOracle, Equiv.symm_apply_apply]
  rfl

end TwoPermutationPrototype.Sampling
