import CommitGolf.Oracle
import CommitGolfCandidate.TwoPermutationCache

/-! Deferred sampling for the challenge's two-sided permutation. Compression
may be fixed throughout the proof and averaged independently afterward. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp OracleSpec MeasureTheory

abbrev Block := BitVec PERMUTATION_WIDTH
abbrev Cache := PermutationCache Block

noncomputable def lazyHandler (compress : Compression) : QueryImpl World (StateT Cache ProbComp)
  | .inl coins => do
      let answer ← (liftM (unifSpec.query coins) : ProbComp (unifSpec.Range coins))
      pure answer
  | .inr (.inl input) => pure (compress input)
  | .inr (.inr (.inl input)) => fun cache => cache.forward input
  | .inr (.inr (.inr input)) => fun cache => cache.inverse input

def eagerHandler (compress : Compression) (p : BiPermutation Block) : QueryImpl World ProbComp
  | .inl coins => liftM (unifSpec.query coins)
  | .inr (.inl input) => pure (compress input)
  | .inr (.inr (.inl input)) => pure (p.forward input)
  | .inr (.inr (.inr input)) => pure (p.inverse input)

noncomputable def lazyRun (compress : Compression) {α : Type} (program : OracleComp World α)
    (cache : Cache) : ProbComp (α × Cache) := (simulateQ (lazyHandler compress) program).run cache

def eagerRun (compress : Compression) (p : BiPermutation Block) {α : Type} (program : OracleComp World α) :
    ProbComp α := simulateQ (eagerHandler compress p) program

private theorem lazy_query (compress : Compression) {α : Type} (query : World.Domain)
    (next : World.Range query → OracleComp World α) (cache : Cache) :
    lazyRun compress ((liftM (World.query query) : OracleComp World _) >>= next) cache =
      (lazyHandler compress query).run cache >>= fun result => lazyRun compress (next result.1) result.2 := by
  simp [lazyRun, simulateQ_bind, StateT.run_bind]

private theorem eager_query (compress : Compression) (p : BiPermutation Block) {α : Type}
    (query : World.Domain) (next : World.Range query → OracleComp World α) :
    eagerRun compress p ((liftM (World.query query) : OracleComp World _) >>= next) =
      eagerHandler compress p query >>= fun answer => eagerRun compress p (next answer) := by
  simp [eagerRun, simulateQ_bind]

private theorem independent_draws {α β γ : Type} (left : ProbComp α) (right : ProbComp β)
    (next : α → β → ProbComp γ) :
    (do let a ← left; let b ← right; next a b) =ᵈ (do let b ← right; let a ← left; next a b) := by
  letI : MeasurableSpace γ := ⊤
  exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_bind_swap_of_uniform left right next)

theorem adaptive_cache_equivalence (compress : Compression) {α : Type} (program : OracleComp World α)
    (cache : Cache) :
    (do let p ← cache.sample; eagerRun compress p.val program) =ᵈ (Prod.fst <$> lazyRun compress program cache) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp only [lazyRun, eagerRun, simulateQ_pure, StateT.run_pure, map_pure]
    letI : MeasurableSpace α := ⊤
    exact EvalDistEq.of_evalDist_eq (OracleComp.evalDist_bind_const cache.sample (pure value))
  | query_bind query next ih =>
    simp only [lazy_query, eager_query, map_bind]
    rcases query with coins | publicQuery
    · simp [lazyHandler, eagerHandler]
      exact (independent_draws cache.sample (liftM (unifSpec.query coins) : ProbComp _)
        (fun p answer => eagerRun compress p.val (next answer))).trans
        (EvalDistEq.bind_right _ (fun answer => ih answer cache))
    · rcases publicQuery with input | perm
      · simp only [lazyHandler, eagerHandler, StateT.run_pure, pure_bind]
        exact ih (compress input) cache
      · rcases perm with input | input
        · exact (cache.forward_step_eq input (fun answer p => eagerRun compress p (next answer))).trans
            (EvalDistEq.bind_right _ (fun result => ih result.1 result.2))
        · exact (cache.inverse_step_eq input (fun answer p => eagerRun compress p (next answer))).trans
            (EvalDistEq.bind_right _ (fun result => ih result.1 result.2))

def emptyTransport : Transport Perm (Completion (PermutationCache.empty Block).entries) where
  toFun p := ⟨BiPermutation.equiv Block p, by simp [PermutationCache.empty, Agrees]⟩
  invFun p := (BiPermutation.equiv Block).symm p.val
  leftInverse p := (BiPermutation.equiv Block).symm_apply_apply p
  rightInverse p := Subtype.ext ((BiPermutation.equiv Block).apply_symm_apply p.val)

private theorem eager_handler_world (compress : Compression) (p : Perm) :
    eagerHandler compress (BiPermutation.equiv Block p) = (Oracle.world ⟨compress, p⟩ : QueryImpl World ProbComp) := by
  funext query
  rcases query with coins | (input | (input | input)) <;> rfl

theorem adaptive_cache_from_empty (compress : Compression) {α : Type} (program : OracleComp World α) :
    (do let p ← $ᵗ Perm; simulateQ (Oracle.world ⟨compress, p⟩) program) =ᵈ
      (Prod.fst <$> lazyRun compress program (PermutationCache.empty Block)) := by
  letI := (PermutationCache.empty Block).completionSampler
  let next : Perm → ProbComp α := fun p => simulateQ (Oracle.world ⟨compress, p⟩) program
  have split := uniform_transport_bind emptyTransport next
  apply split.trans
  trans (do let p ← (PermutationCache.empty Block).sample; eagerRun compress p.val program)
  · apply EvalDistEq.bind_right
    intro completion
    unfold next eagerRun
    rw [← eager_handler_world]
    simp [emptyTransport]
  · exact adaptive_cache_equivalence compress program (PermutationCache.empty Block)

end TwoPermutationPrototype.Sampling
