import CommitGolfCandidate.TwoPermutationInverseEvent
import CommitGolfCandidate.Probability

/-! Return a uniform completion along with the adaptive prefix's output.
The continuation may inspect the same fully realized permutation. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp

private theorem query_in_lazy_run {α : Type} (compress : Compression) (query : World.Domain)
    (next : World.Range query → OracleComp World α) (cache : Cache) :
    lazyRun compress ((liftM (World.query query) : OracleComp World _) >>= next) cache =
      (lazyHandler compress query).run cache >>= fun result => lazyRun compress (next result.1) result.2 := by
  simp [lazyRun, simulateQ_bind, StateT.run_bind]

theorem adaptive_posterior_equivalence {α β : Type} (compress : Compression)
    (program : OracleComp World α) (cache : Cache) (next : α → BiPermutation Block → ProbComp β) :
    (do let p ← cache.sample
        let value ← eagerRun compress p.val program
        next value p.val) =ᵈ
      (do let (value, final) ← lazyRun compress program cache
          let p ← final.sample
          next value p.val) := by
  induction program using OracleComp.inductionOn generalizing cache with
  | pure value =>
    simp only [eagerRun, lazyRun, simulateQ_pure, StateT.run_pure, pure_bind]
    rfl
  | query_bind query continuation ih =>
    rw [query_in_lazy_run]
    simp only [eagerRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, bind_assoc]
    rcases query with coins | (input | (input | output))
    · simp only [eagerHandler, lazyHandler, StateT.run_monadLift, bind_assoc, pure_bind]
      have swapped := EvalDistEq.of_evalDist_eq
        (CommitGolfCandidate.distribution_bind_comm cache.sample (liftM (unifSpec.query coins) : ProbComp _)
          (fun p answer => eagerRun compress p.val (continuation answer) >>= fun value => next value p.val))
      apply swapped.trans
      apply EvalDistEq.bind_right
      intro answer
      exact ih answer cache
    · simp only [eagerHandler, lazyHandler, StateT.run_pure, pure_bind]
      exact ih (compress input) cache
    · simp only [eagerHandler, lazyHandler, pure_bind]
      apply (cache.forward_step_eq input
        (fun answer p => eagerRun compress p (continuation answer) >>= fun value => next value p)).trans
      apply EvalDistEq.bind_right
      intro result
      exact ih result.1 result.2
    · simp only [eagerHandler, lazyHandler, pure_bind]
      apply (cache.inverse_step_eq output
        (fun answer p => eagerRun compress p (continuation answer) >>= fun value => next value p)).trans
      apply EvalDistEq.bind_right
      intro result
      exact ih result.1 result.2

theorem lazy_cache_length {α : Type} (compress : Compression) (program : OracleComp World α)
    (cache : Cache) (budget : Nat) (bounded : QueryBounded program budget) (result : α × Cache)
    (present : result ∈ support (lazyRun compress program cache)) :
    result.2.entries.length ≤ cache.entries.length + budget := by
  induction program using OracleComp.inductionOn generalizing cache budget result with
  | pure value =>
    simp only [lazyRun, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at present
    subst result
    exact Nat.le_add_right _ _
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, QueryBounded (next answer) (budget - Oracle.callCost query)) at bounded
    rw [query_in_lazy_run] at present
    obtain ⟨⟨answer, middle⟩, reached, finished⟩ := (mem_support_bind_iff _ _ _).mp present
    have advances : middle.entries.length ≤ cache.entries.length + Oracle.callCost query := by
      rcases query with coins | (input | (input | output))
      · simp only [lazyHandler, StateT.run_monadLift, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at reached
        obtain ⟨coin, _, same⟩ := reached
        cases same
        rfl
      · simp only [lazyHandler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
        cases reached
        exact Nat.le_succ _
      · exact forward_cache_growth cache input (answer, middle) reached
      · exact inverse_cache_growth cache output (answer, middle) reached
    have remaining := ih answer middle _ (bounded.2 answer) result finished
    omega

end TwoPermutationPrototype.Sampling
