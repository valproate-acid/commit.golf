import CommitGolfCandidate.TwoPermutationBindingLeaf
import CommitGolfCandidate.TwoPermutationPosterior
import CommitGolfCandidate.CompressionSampling

/-! Record the actual queries made by checker replay and transfer every recorded
row to the terminal oracle cache. The trace records replies in either direction. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp OracleSpec CommitGolfCandidate
set_option maxRecDepth 8192

inductive PublicRow where
  | compression (input : BitVec 512) (reply : BitVec 256)
  | permutation (input reply : Block)

def queryRows (query : World.Domain) (answer : World.Range query) : List PublicRow :=
  match query with
  | .inl _ => []
  | .inr (.inl input) => [.compression input answer]
  | .inr (.inr (.inl input)) => [.permutation input answer]
  | .inr (.inr (.inr output)) => [.permutation answer output]

def recordRows {α : Type} (program : OracleComp World α) : OracleComp World (α × List PublicRow) :=
  OracleComp.recOn program (fun value => pure (value, []))
    (fun query _ next => do
      let answer ← (liftM (World.query query) : OracleComp World _)
      (fun result => (result.1, queryRows query answer ++ result.2)) <$> next answer)

theorem record_rows_query {α : Type} (query : World.Domain) (next : World.Range query → OracleComp World α) :
    recordRows ((liftM (World.query query) : OracleComp World _) >>= next) =
      (do let answer ← (liftM (World.query query) : OracleComp World _)
          (fun result => (result.1, queryRows query answer ++ result.2)) <$> recordRows (next answer)) := rfl

theorem record_rows_bound {α : Type} (program : OracleComp World α) (budget : Nat)
    (bounded : PublicQueryBound program budget) : PublicQueryBound (recordRows program) budget := by
  induction program using OracleComp.inductionOn generalizing budget with
  | pure _ => trivial
  | query_bind query next ih =>
    rw [record_rows_query]
    change Oracle.callCost query ≤ budget ∧
      (∀ answer, PublicQueryBound (next answer) (budget - Oracle.callCost query)) at bounded
    refine ⟨bounded.1, fun answer => ?_⟩
    exact (isQueryBound_map_iff _ _ _ _ _).mpr (ih answer _ (bounded.2 answer))

theorem record_rows_pure {α : Type} (value : α) :
    recordRows (pure value : OracleComp World α) = pure (value, []) := rfl

theorem record_rows_bind {α β : Type} (program : OracleComp World α) (next : α → OracleComp World β) :
    recordRows (program >>= next) = (do
      let earlier ← recordRows program
      let later ← recordRows (next earlier.1)
      pure (later.1, earlier.2 ++ later.2)) := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [record_rows_pure]
  | query_bind query tail ih =>
    rw [bind_assoc, record_rows_query, record_rows_query]
    simp only [bind_assoc]
    apply bind_congr
    intro answer
    rw [ih]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def, List.append_assoc]

theorem record_rows_erase {α : Type} (program : OracleComp World α) :
    Prod.fst <$> recordRows program = program := by
  induction program using OracleComp.inductionOn with
  | pure value => simp [record_rows_pure]
  | query_bind query next ih =>
    rw [record_rows_query, map_bind]
    apply bind_congr
    intro answer
    simpa only [Functor.map_map, Function.comp_def] using ih answer

theorem run_recorded_rows_support {α σ : Type}
    (handler : QueryImpl World (StateT σ ProbComp)) (stored : σ → PublicRow → Prop)
    (step : ∀ query state result, result ∈ support ((handler query).run state) →
      (∀ row, stored state row → stored result.2 row) ∧
      ∀ row ∈ queryRows query result.1, stored result.2 row)
    (program : OracleComp World α) (state : σ) (result : (α × List PublicRow) × σ)
    (reached : result ∈ support ((simulateQ handler (recordRows program)).run state)) :
    (∀ row, stored state row → stored result.2 row) ∧
    ∀ row ∈ result.1.2, stored result.2 row := by
  induction program using OracleComp.inductionOn generalizing state result with
  | pure value =>
    change result ∈ support ((simulateQ handler (pure (value, []))).run state) at reached
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact ⟨fun _ before => before, by simp⟩
  | query_bind query next ih =>
    rw [record_rows_query] at reached
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, simulateQ_map, StateT.run_map, mem_support_bind_iff, support_map, Set.mem_image] at reached
    obtain ⟨⟨answer, middle⟩, called, tail, continued, rfl⟩ := reached
    obtain ⟨preserved, head⟩ := step query state (answer, middle) called
    obtain ⟨kept, recorded⟩ := ih answer middle tail continued
    refine ⟨fun row before => kept row (preserved row before), fun row present => ?_⟩
    rcases List.mem_append.mp present with first | later
    · exact kept row (head row first)
    · exact recorded row later

def permutationStored (cache : Cache) : PublicRow → Prop
  | .permutation input output => (input, output) ∈ cache.entries
  | .compression _ _ => True

def compressionStored (cache : CompressionCache) : PublicRow → Prop
  | .compression input output => cache input = some output
  | .permutation _ _ => True

private theorem forward_rows (cache : Cache) (input : Block) (result : Block × Cache)
    (reached : result ∈ support (cache.forward input)) :
    (∀ row ∈ cache.entries, row ∈ result.2.entries) ∧ (input, result.1) ∈ result.2.entries := by
  classical
  unfold PermutationCache.forward at reached
  split at reached
  · obtain ⟨answer, _, same⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    constructor
    · intro row present
      exact List.mem_cons_of_mem _ present
    · exact List.mem_cons_self
  · rename_i known
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    constructor
    · exact fun _ => id
    · simp only [UnusedInput, not_forall, not_not] at known
      obtain ⟨⟨previous, answer⟩, present, equal⟩ := known
      change previous = input at equal
      subst previous
      have reply := cache.example.property (input, answer) present
      change cache.example.val.forward input = answer at reply
      rw [reply]
      exact present

private theorem inverse_rows (cache : Cache) (output : Block) (result : Block × Cache)
    (reached : result ∈ support (cache.inverse output)) :
    (∀ row ∈ cache.entries, row ∈ result.2.entries) ∧ (result.1, output) ∈ result.2.entries := by
  classical
  unfold PermutationCache.inverse at reached
  split at reached
  · obtain ⟨answer, _, same⟩ := (mem_support_bind_iff _ _ _).mp reached
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    constructor
    · intro row present
      exact List.mem_cons_of_mem _ present
    · exact List.mem_cons_self
  · rename_i known
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    constructor
    · exact fun _ => id
    · simp only [UnusedOutput, not_forall, not_not] at known
      obtain ⟨⟨answer, previous⟩, present, equal⟩ := known
      change previous = output at equal
      subst previous
      have reply := cache.example.property (answer, output) present
      change cache.example.val.forward answer = output at reply
      have inverse : cache.example.val.inverse output = answer := by
        rw [← reply, cache.example.val.leftInverse]
      rw [inverse]
      exact present

theorem permutation_replay_stored {α : Type} (compress : Compression) (program : OracleComp World α)
    (cache : Cache) (result : (α × List PublicRow) × Cache)
    (reached : result ∈ support (lazyRun compress (recordRows program) cache)) :
    ∀ row ∈ result.1.2, permutationStored result.2 row := by
  apply (run_recorded_rows_support (lazyHandler compress) permutationStored ?_ program cache result reached).2
  intro query state result possible
  rcases query with coins | (input | (input | output))
  · simp only [lazyHandler, StateT.run_monadLift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at possible
    obtain ⟨answer, _, same⟩ := possible
    subst result
    exact ⟨fun _ before => before, by simp [queryRows]⟩
  · simp only [lazyHandler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨fun _ before => before, by simp [queryRows, permutationStored]⟩
  · obtain ⟨kept, new⟩ := forward_rows state input result possible
    refine ⟨fun row before => ?_, fun row inHead => ?_⟩
    · cases row with
      | permutation x y => exact kept (x, y) before
      | compression _ _ => trivial
    · simp only [queryRows, List.mem_singleton] at inHead
      subst row
      exact new
  · obtain ⟨kept, new⟩ := inverse_rows state output result possible
    refine ⟨fun row before => ?_, fun row inHead => ?_⟩
    · cases row with
      | permutation x y => exact kept (x, y) before
      | compression _ _ => trivial
    · simp only [queryRows, List.mem_singleton] at inHead
      subst row
      exact new

theorem compression_replay_stored {α : Type} (p : Perm) (program : OracleComp World α)
    (cache : CompressionCache) (result : (α × List PublicRow) × CompressionCache)
    (reached : result ∈ support (compressionRun p (recordRows program) cache)) :
    ∀ row ∈ result.1.2, compressionStored result.2 row := by
  apply (run_recorded_rows_support (compressionHandler p) compressionStored ?_ program cache result reached).2
  intro query state result possible
  rcases query with coins | (input | (input | output))
  · simp only [compressionHandler, StateT.run_monadLift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at possible
    obtain ⟨answer, _, same⟩ := possible
    subst result
    exact ⟨fun _ before => before, by simp [queryRows]⟩
  · change result ∈ support ((randomOracle input).run state) at possible
    rw [randomOracle.run_eq] at possible
    cases cached : state input with
    | some answer =>
      simp only [cached, support_pure, Set.mem_singleton_iff] at possible
      subst result
      refine ⟨fun _ before => before, fun row inHead => ?_⟩
      simp only [queryRows, List.mem_singleton] at inHead
      subst row
      exact cached
    | none =>
      simp only [cached, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at possible
      obtain ⟨answer, _, same⟩ := possible
      subst result
      refine ⟨fun row before => ?_, fun row inHead => ?_⟩
      · cases row with
        | permutation _ _ => trivial
        | compression key value =>
          change state key = some value at before
          by_cases atInput : key = input
          · subst key
            rw [cached] at before
            contradiction
          · exact (QueryCache.cacheQuery_of_ne state answer atInput).trans before
      · simp only [queryRows, List.mem_singleton] at inHead
        subst row
        exact QueryCache.cacheQuery_self state input answer
  · simp only [compressionHandler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨fun _ before => before, by simp [queryRows, compressionStored]⟩
  · simp only [compressionHandler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨fun _ before => before, by simp [queryRows, compressionStored]⟩

end TwoPermutationPrototype.Sampling
