import CommitGolfCandidate.TwoPermutationCheckerPaths
import CommitGolfCandidate.CheckEvaluation

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp OracleSpec RiscvZkvm.Rv64
open TwoPermutationPrototype.Sampling

/-- A computation with no private coin query. Both trusted interpreters then
choose the same public replies, including after replay instrumentation. -/
inductive PublicOnly {α : Type} : OracleComp World α → Prop where
  | pure (value : α) : PublicOnly (pure value)
  | query (query : PublicSpec.Domain) (next : PublicSpec.Range query → OracleComp World α)
      (coinFree : ∀ reply, PublicOnly (next reply)) :
      PublicOnly ((liftM (World.query (.inr query)) : OracleComp World _) >>= next)

theorem PublicOnly.map {α β : Type} {program : OracleComp World α}
    (coinFree : PublicOnly program) (f : α → β) : PublicOnly (f <$> program) := by
  induction coinFree with
  | pure value => simpa using PublicOnly.pure (f value)
  | query query next _ ih =>
    rw [map_bind]
    exact .query query _ ih

theorem PublicOnly.record {α : Type} {program : OracleComp World α}
    (coinFree : PublicOnly program) : PublicOnly (recordRows program) := by
  induction coinFree with
  | pure value =>
    rw [record_rows_pure]
    exact .pure _
  | query query next _ ih =>
    rw [record_rows_query]
    exact .query query _ fun reply => (ih reply).map _

theorem PublicOnly.limit {α : Type} {program : OracleComp World α}
    (coinFree : PublicOnly program) (budget : Nat) : PublicOnly (limitPublicQueries program budget) := by
  induction coinFree generalizing budget with
  | pure value =>
    rw [limit_public_pure]
    exact .pure _
  | query query next _ ih =>
    rw [limit_public_query_bind]
    split
    · exact .query query _ fun reply => ih reply _
    · exact .pure _

theorem PublicOnly.fixed {α : Type} (oracle : Oracle) {program : OracleComp World α}
    (coinFree : PublicOnly program) :
    fixedOracleRun oracle program = (Pure.pure (checkEvaluation oracle program).1 : ProbComp α) := by
  induction coinFree with
  | pure value => rw [fixed_oracle_run_pure, check_evaluation_pure]
  | query query next _ ih =>
    rw [fixed_oracle_run_public, check_evaluation_public_bind, ih]

theorem execute_public_only (image : Image) (fuel : Nat) (state : MachineState) :
    PublicOnly (execute image fuel state false) := by
  induction fuel generalizing state with
  | zero => exact .pure _
  | succ fuel ih =>
    simp only [execute, Bool.false_and, Bool.false_eq_true, ite_false]
    split
    · exact .pure _
    · split
      · split
        · exact .pure _
        · simp only [bind_pure_comp]
          exact .query _ _ (fun reply => (ih _).map _)
      · split <;> exact .pure _
    · split
      · exact .pure _
      · simp only [bind_pure_comp]
        exact (ih _).map _

theorem check_public_only (s : Submission) (input : CheckInput) :
    PublicOnly (s.run .check input) := by
  by_cases size : input.proof.length ≤ s.sizes.proof
  · simp only [Submission.run, size, decide_true, ite_true]
    change PublicOnly (execute (s.image .check) (s.steps .check) (s.initialState .check input) false)
    exact execute_public_only _ _ _
  · simp only [Submission.run, size, decide_false]
    exact .pure _

/-- Recording neither changes the check output nor its counted calls. -/
theorem check_record_erase {α : Type} (oracle : Oracle) (program : OracleComp World α) :
    let recorded := checkEvaluation oracle (recordRows program)
    (recorded.1.1, recorded.2) = checkEvaluation oracle program := by
  calc
    _ = checkEvaluation oracle (Prod.fst <$> recordRows program) :=
      (check_evaluation_map oracle Prod.fst (recordRows program)).symm
    _ = _ := by rw [record_rows_erase]

/-- The limiter retains the full trace whenever the deterministic check fits
the allotted budget. The 2^31 replay overhead can therefore be enforced
independently of the machine's larger instruction limit. -/
theorem PublicOnly.limit_recorded {α : Type} (oracle : Oracle) {program : OracleComp World α}
    (coinFree : PublicOnly program) (budget : Nat)
    (fits : (checkEvaluation oracle (recordRows program)).2 ≤ budget) :
    let result := checkEvaluation oracle (recordRows program)
    checkEvaluation oracle (recordRows (limitPublicQueries program budget)) =
      ((some result.1.1, result.1.2), result.2) := by
  induction coinFree generalizing budget with
  | pure value =>
    simp [limit_public_pure, record_rows_pure, check_evaluation_pure]
  | query query next _ ih =>
    let answer := oracle.answer (m := Id) query
    have before : (checkEvaluation oracle (recordRows
        ((liftM (World.query (.inr query)) : OracleComp World _) >>= next))).2 =
        1 + (checkEvaluation oracle (recordRows (next answer))).2 := by
      rw [record_rows_query, check_evaluation_public_bind, check_evaluation_map]
    have one : Oracle.callCost (.inr query) ≤ budget := by
      change 1 ≤ budget
      omega
    rw [limit_public_query_bind, ite_eq_left one, record_rows_query, check_evaluation_public_bind,
      check_evaluation_map]
    have tail : (checkEvaluation oracle (recordRows (next answer))).2 ≤ budget - Oracle.callCost (.inr query) := by
      change _ ≤ budget - 1
      omega
    simp only [record_rows_query, check_evaluation_public_bind, check_evaluation_map]
    rw [ih answer _ tail]

end TwoPermutationPrototype.Checker
