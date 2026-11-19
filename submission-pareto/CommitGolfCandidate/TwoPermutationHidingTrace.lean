import CommitGolfCandidate.TwoPermutationHidingAdaptive
import CommitGolfCandidate.TwoPermutationBindingEvents
import CommitGolfCandidate.HidingTrace

/-! Collect permutation query/reply pairs in input/output order. Both oracle
directions therefore use the same row list and the same mark predicate. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp CommitGolfCandidate

def permutationHead (query : World.Domain) (answer : World.Range query) : List Row :=
  match query with
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr (.inl input)) => [(input, answer)]
  | .inr (.inr (.inr output)) => [(answer, output)]

def tracePermutation {α : Type} (computation : OracleComp World α) :
    OracleComp World (α × List Row) :=
  OracleComp.recOn computation
    (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← (liftM (World.query query) : OracleComp World _)
      let (value, trace) ← next answer
      pure (value, permutationHead query answer ++ trace))

theorem trace_permutation_run_query {α : Type} (oracle : Oracle) (query : World.Domain)
    (next : World.Range query → OracleComp World α) :
    fixedOracleRun oracle (tracePermutation ((liftM (World.query query) : OracleComp World _) >>= next)) =
    (do let answer ← oracle.world query
        let result ← fixedOracleRun oracle (tracePermutation (next answer))
        pure (result.1, permutationHead query answer ++ result.2)) := by
  have expansion :
      tracePermutation ((liftM (World.query query) : OracleComp World _) >>= next) =
      (do let answer ← (liftM (World.query query) : OracleComp World _)
          let (value, trace) ← tracePermutation (next answer)
          pure (value, permutationHead query answer ++ trace)) := rfl
  rw [expansion]
  rw [fixed_run_query_bind]
  apply bind_congr
  intro answer
  rw [fixed_oracle_run_bind]
  apply bind_congr
  intro result
  cases result
  exact fixed_oracle_run_pure _ _

theorem trace_permutation_length {α : Type} (oracle : Oracle) (computation : OracleComp World α)
    (budget : Nat) (bounded : QueryBounded computation budget)
    (result : α × List Row)
    (reached : result ∈ support (fixedOracleRun oracle (tracePermutation computation))) :
    result.2.length ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
    change result ∈ support (fixedOracleRun oracle (pure (value, []))) at reached
    rw [fixed_oracle_run_pure] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact Nat.zero_le _
  | query_bind query next ih =>
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, QueryBounded (next answer) (budget-Oracle.callCost query)) at bounded
    rw [trace_permutation_run_query] at reached
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reached
    obtain ⟨answer, _, tail, tailReached, rfl⟩ := reached
    have rest := ih answer (budget - Oracle.callCost query) (bounded.2 answer) tail tailReached
    have head : (permutationHead query answer).length ≤ Oracle.callCost query := by
      rcases query with _ | (_ | (_ | _)) <;> simp [permutationHead, Oracle.callCost]
    simp only [List.length_append]
    omega

def rowHits (rows : List Row) (query : Row) : Bool :=
  rows.any fun row => decide (query.1 = row.1 ∨ query.2 = row.2)

theorem flagged_reference_trace {α : Type} (compress : Compression) (p : BiPermutation Block)
    (rows : List Row) (computation : OracleComp World α) (flag : Bool) :
    flaggedRun (fixedOracle compress p) (marksReferencePair p rows) computation flag =
      ((fun result : α × List Row => (result.1, (), flag || result.2.any (rowHits rows))) <$>
        fixedOracleRun (fixedOracle compress p) (tracePermutation computation)) := by
  induction computation using OracleComp.inductionOn generalizing flag with
  | pure value =>
    change (pure (value, (), flag) : ProbComp _) =
      (fun result : α × List Row => (result.1, (), flag || result.2.any (rowHits rows))) <$>
        fixedOracleRun (fixedOracle compress p) (pure (value, []))
    simp [fixed_oracle_run_pure]
  | query_bind query next ih =>
    rw [flagged_run_query_bind, trace_permutation_run_query, map_bind]
    rcases query with coins | (input | (input | output))
    · simp only [ih, permutationHead, List.nil_append, marksReferencePair, Bool.or_false, bind_pure_comp, Functor.map_map]
    · simp only [ih, permutationHead, List.nil_append, marksReferencePair, Bool.or_false, bind_pure_comp, Functor.map_map]
    · change (pure (p.forward input) >>= _) = (pure (p.forward input) >>= _)
      simp only [pure_bind, ih, permutationHead, marksReferencePair, List.singleton_append, List.any_cons,
        rowHits, Bool.or_assoc, bind_pure_comp, Functor.map_map]
    · change (pure (p.inverse output) >>= _) = (pure (p.inverse output) >>= _)
      simp only [pure_bind, ih, permutationHead, marksReferencePair, List.singleton_append, List.any_cons,
        rowHits, Bool.or_assoc, bind_pure_comp, Functor.map_map]

end TwoPermutationPrototype.Sampling
