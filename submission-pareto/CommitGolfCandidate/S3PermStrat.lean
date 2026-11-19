import CommitGolfCandidate.CompressionSampling
import CommitGolfCandidate.S3PermModel

/-! Read a computation in the contract's oracle world as a strategy against the lazily
sampled permutation, for one fixed compression function: private coins become `rand`
nodes, compression queries are answered by the fixed function, and the two permutation
directions become `fwd` and `inv` nodes. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp OracleSpec
open CommitGolfCandidate.Permutation

abbrev PermState := BitVec PERMUTATION_WIDTH

def toStrat (compression : Compression) {α : Type} (computation : OracleComp World α) :
    Strat PermState α :=
  OracleComp.recOn (motive := fun _ => Strat PermState α) computation
    (fun value => Strat.done value)
    (fun query _ next =>
      match query, next with
      | .inl coins, next => Strat.rand coins next
      | .inr (.inl input), next => next (compression input)
      | .inr (.inr (.inl input)), next => Strat.fwd input next
      | .inr (.inr (.inr input)), next => Strat.inv input next)

theorem to_strat_pure (compression : Compression) {α : Type} (value : α) :
    toStrat compression (pure value : OracleComp World α) = Strat.done value := rfl

theorem to_strat_coins (compression : Compression) {α : Type} (coins : unifSpec.Domain)
    (next : unifSpec.Range coins → OracleComp World α) :
    toStrat compression ((liftM (World.query (.inl coins)) : OracleComp World _) >>= next) =
      Strat.rand coins fun answer => toStrat compression (next answer) := rfl

theorem to_strat_compress (compression : Compression) {α : Type}
    (input : BitVec COMPRESSION_INPUT_LENGTH)
    (next : BitVec COMPRESSION_OUTPUT_LENGTH → OracleComp World α) :
    toStrat compression
        ((liftM (World.query (.inr (.inl input))) : OracleComp World _) >>= next) =
      toStrat compression (next (compression input)) := rfl

theorem to_strat_permute (compression : Compression) {α : Type} (input : PermState)
    (next : PermState → OracleComp World α) :
    toStrat compression
        ((liftM (World.query (.inr (.inr (.inl input)))) : OracleComp World _) >>= next) =
      Strat.fwd input fun answer => toStrat compression (next answer) := rfl

theorem to_strat_inverse (compression : Compression) {α : Type} (input : PermState)
    (next : PermState → OracleComp World α) :
    toStrat compression
        ((liftM (World.query (.inr (.inr (.inr input)))) : OracleComp World _) >>= next) =
      Strat.inv input fun answer => toStrat compression (next answer) := rfl

theorem to_strat_bind (compression : Compression) {α β : Type}
    (computation : OracleComp World α) (next : α → OracleComp World β) :
    toStrat compression (computation >>= next) =
      (toStrat compression computation).bind fun value => toStrat compression (next value) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rw [pure_bind, to_strat_pure]; rfl
  | query_bind query continuation ih =>
    rw [bind_assoc]
    rcases query with coins | input | input | input
    · rw [to_strat_coins, to_strat_coins]
      simp only [Strat.bind, ih]
    · rw [to_strat_compress, to_strat_compress]
      exact ih _
    · rw [to_strat_permute, to_strat_permute]
      simp only [Strat.bind, ih]
    · rw [to_strat_inverse, to_strat_inverse]
      simp only [Strat.bind, ih]

theorem to_strat_map (compression : Compression) {α β : Type} (f : α → β)
    (computation : OracleComp World α) :
    toStrat compression (f <$> computation) =
      (toStrat compression computation).bind fun value => Strat.done (f value) := by
  rw [map_eq_bind_pure_comp, to_strat_bind]
  rfl

/-- A public-query bound bounds the permutation queries of the strategy. -/
theorem to_strat_QB (compression : Compression) {α : Type} {computation : OracleComp World α}
    {budget : Nat} (bounded : PublicQueryBound computation budget) :
    (toStrat compression computation).QB budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => exact Strat.QB.done value budget
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    rcases query with coins | input | input | input
    · rw [to_strat_coins]
      exact Strat.QB.rand _ _ _ fun answer => ih answer (by simpa [Oracle.callCost] using bounded.2 answer)
    · rw [to_strat_compress]
      exact (ih _ (bounded.2 _)).mono (Nat.sub_le _ _)
    · rw [to_strat_permute]
      obtain ⟨rest, rfl⟩ : ∃ rest, budget = rest + 1 := ⟨budget - 1, by
        have := bounded.1; simp only [Oracle.callCost] at this; omega⟩
      exact Strat.QB.fwd _ _ rest fun answer => ih answer (by simpa [Oracle.callCost] using bounded.2 answer)
    · rw [to_strat_inverse]
      obtain ⟨rest, rfl⟩ : ∃ rest, budget = rest + 1 := ⟨budget - 1, by
        have := bounded.1; simp only [Oracle.callCost] at this; omega⟩
      exact Strat.QB.inv _ _ rest fun answer => ih answer (by simpa [Oracle.callCost] using bounded.2 answer)

end CommitGolfCandidate
