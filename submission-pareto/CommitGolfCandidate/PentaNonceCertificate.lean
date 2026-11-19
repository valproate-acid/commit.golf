import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.TwoPermutationTranscript
import CommitGolf.Statements
import CommitGolfCandidate.TwoPermutationCheckerReplay
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.Machine
import CommitGolfCandidate.QuadNonceSpec
import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.QuadCertificate

/-! Penta copy of `QuadNonceCertificate` (itself a copy of `QuadCertificate` for quad + NonceChain), with the opening
cycles and proof bytes as parameters and the quad2 transcript builder: the opening facts carry
`QuadNonceTranscriptRefines`, completeness ranges over seeds (the lead's `CheckerFacts` are reused
unchanged), and the commit call count is only
bounded by `COMMIT_BUDGET` (quad 41,943,039 + chain 1,525,248 = 43,468,287 calls). -/

namespace TwoPermutationPrototype.PentaNonceCertificate
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
open TwoPermutationPrototype.QuadCertificate (CheckerFacts honestCheckInput)
open CommitGolf CommitGolf.Riscv CommitGolfCandidate OracleComp TwoPermutationPrototype.Sampling

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

local instance {α : Type} : MeasurableSpace α := ⊤

structure OpeningFacts (s : Submission) (openingCycles proofBytes : Nat) : Prop where
  runs : ∀ (trapdoor : s.scheme.Trapdoor) (positions : Positions), ∃ result : Execution,
    s.run .opening (trapdoor, positions) = pure result ∧ result.exit = .success ∧
    s.openingSucceeded result = true ∧
    (positions.card = BATCH → result.cycles ≤ openingCycles ∧ (s.readProof result).length ≤ proofBytes)
  refines : PentaNonceTranscriptRefines s.scheme pentaTranscriptBuilder

variable {s : Submission} {commitCycles openingCycles proofBytes : Nat}
variable (commit : ∀ (message : Message) (result : Execution), result ∈ support (s.run .commit message) →
  result.exit = .success ∧ result.cycles = commitCycles ∧ result.oracleCalls ≤ COMMIT_BUDGET)

private theorem scheme_check_observation (oracle : Oracle) (input : CheckInput) :
    oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof) =
      let observed := Checker.checkObservation s oracle input
      (observed.1.1.exit == .success, observed.2) := by
  rw [scheme_check_evaluation]
  have erase := Checker.check_record_erase oracle (s.run .check input)
  rw [← erase]
  rfl

private theorem counted_check_observation (oracle : Oracle) (input : CheckInput) :
    oracle.run (s.run .check input) =
      let observed := Checker.checkObservation s oracle input
      pure (observed.1.1, observed.2) := by
  have erase := Checker.check_record_erase oracle (s.run .check input)
  dsimp only [Checker.checkObservation] at ⊢
  erw [erase]
  by_cases valid : input.proof.length ≤ s.sizes.proof
  · have run : s.run .check input = execute (s.image .check) (s.steps .check)
        (s.initialState .check input) false := by
      simp only [Submission.run, valid, decide_true, ite_true]
      rfl
    erw [run, execute_check_evaluation]
  · have run : s.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
      simp only [Submission.run, valid, decide_false, Bool.false_eq_true, ite_false]
    erw [run, oracle_run_pure, check_evaluation_pure]

include commit in
private theorem scheme_commit_budget (oracle : Oracle) (message : Message)
    (result : (Commitment × s.scheme.Trapdoor) × Nat)
    (reached : result ∈ support (oracle.run (s.scheme.commit message))) :
    result.2 ≤ COMMIT_BUDGET := by
  change result ∈ support (oracle.run (s.readCommit <$> s.run .commit message)) at reached
  rw [oracle_run_map oracle s.readCommit, support_map] at reached
  obtain ⟨execution,execReached,same⟩ := reached
  have actual := commit message execution.1 (writer_support (oracle.world.withAddCost Oracle.callCost) _ execution execReached)
  have calls := execute_counted_with_coins oracle (s.image .commit) (s.steps .commit)
    (s.initialState .commit message) true execution execReached
  have equal : execution.2 = result.2 := congrArg Prod.snd same
  rw [← equal, ← calls]
  exact actual.2.2

private theorem opening_run (opens : OpeningFacts s openingCycles proofBytes) (trapdoor : s.scheme.Trapdoor) (positions : Positions)
    (opened : Execution) (reached : opened ∈ support (s.run .opening (trapdoor,positions))) :
    opened.exit = .success ∧ s.openingSucceeded opened = true ∧
    (positions.card = BATCH → opened.cycles ≤ openingCycles ∧ (s.readProof opened).length ≤ proofBytes) := by
  obtain ⟨result, exactRun, facts⟩ := opens.runs trapdoor positions
  rw [exactRun,support_pure,Set.mem_singleton_iff] at reached
  rwa [reached]

include commit in
private theorem honest_machine_resources (opens : OpeningFacts s openingCycles proofBytes) (message : Message) (positions : Positions)
    (result : MachineResult) (reached : result ∈ support (s.honestMachine message positions)) :
    result.success = true ∧
      (positions.card = BATCH → result.commitCycles ≤ commitCycles ∧ result.openingCycles ≤ openingCycles) := by
  change result ∈ support (do
    let committed ← s.run .commit message
    let opened ← s.run .opening ((s.readCommit committed).2,positions)
    pure ⟨committed.exit == Exit.success && s.openingSucceeded opened,
      committed.cycles,opened.cycles,(s.readProof opened).length⟩) at reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨committed,commitReached,opened,openReached,rfl⟩ := reached
  have finished := commit message committed commitReached
  have physical := opening_run opens (s.readCommit committed).2 positions opened openReached
  constructor
  · simp only [finished.1,beq_self_eq_true,physical.2.1,Bool.and_true]
  · intro batch
    exact ⟨finished.2.1.le,(physical.2.2 batch).1⟩

include commit in
theorem machine_success (opens : OpeningFacts s openingCycles proofBytes) : s.MachineSuccess := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources commit opens message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).1

include commit in
theorem prover_cycles (opens : OpeningFacts s openingCycles proofBytes) : s.ProverCycles commitCycles openingCycles := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  exact (honest_machine_resources commit opens message positions result.1
    (writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached)).2 batch

include commit in
theorem termination (opens : OpeningFacts s openingCycles proofBytes) (checks : CheckerFacts s) : s.Termination := by
  intro oracle program input
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  have execution := writer_support (oracle.world.withAddCost Oracle.callCost) _ result reached
  cases program with
  | commit =>
    rw [(commit input result.1 execution).1]
    decide
  | opening =>
    rw [(opening_run opens input.1 input.2 result.1 execution).1]
    decide
  | check =>
    erw [counted_check_observation oracle input] at reached
    simp only [support_pure, Set.mem_singleton_iff] at reached
    subst result
    exact checks.terminates oracle input

private theorem scheme_open_run (trapdoor : s.scheme.Trapdoor) (positions : Positions)
    (result : Execution) (exactRun : s.run .opening (trapdoor,positions) = pure result) :
    s.scheme.opening trapdoor positions = pure (s.readProof result) := by
  change s.readProof <$> s.run .opening (trapdoor,positions) = _
  rw [exactRun,map_pure]

include commit in
theorem honest_budgets (opens : OpeningFacts s openingCycles proofBytes) (checks : CheckerFacts s) : s.scheme.HonestBudgets := by
  intro oracle message positions
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,calls⟩,committed,opened,opening,remainder⟩ := reached
  obtain ⟨openedMachine,exec,_⟩ := opens.runs trapdoor positions
  erw [scheme_open_run trapdoor positions openedMachine exec,oracle_run_pure] at opening
  simp only [support_pure,Set.mem_singleton_iff] at opening remainder
  subst opened
  subst result
  let input : CheckInput := ⟨root,positions,message.restrict positions,s.readProof openedMachine⟩
  have checked : (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).2 ≤
      100*positions.card := by
    rw [scheme_check_observation]
    exact checks.queryBudget oracle input
  exact ⟨scheme_commit_budget commit oracle message _ committed,Nat.zero_le _,checked⟩

theorem proof_size (opens : OpeningFacts s openingCycles proofBytes) : s.scheme.ProofSize proofBytes := by
  intro oracle message positions batch
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,trapdoor⟩,calls⟩,_,opened,opening,remainder⟩ := reached
  obtain ⟨openedMachine,exec,_,_,scored⟩ := opens.runs trapdoor positions
  erw [scheme_open_run trapdoor positions openedMachine exec,oracle_run_pure] at opening
  simp only [support_pure,Set.mem_singleton_iff] at opening remainder
  subst opened
  subst result
  exact (scored batch).2

private theorem honest_check_event (scheme : Scheme) (oracle : Oracle) (message : Message) (positions : Positions) :
    (fun result : Scheme.HonestResult => result.accepted = true) <$> scheme.honest oracle message positions =
      (fun view : Commitment × Proof =>
        (oracle.eval (scheme.check view.1 positions (message.restrict positions) view.2)).1 = true) <$>
        fixedOracleRun oracle (executableTranscript scheme message positions) := by
  simp only [Scheme.honest,executableTranscript,fixed_oracle_run_bind,
    fixed_oracle_run_pure,map_bind,map_pure]
  simp only [fixedOracleRun,bind_map_left]

set_option linter.constructorNameAsVariable false in
theorem completeness (opens : OpeningFacts s openingCycles proofBytes) (checks : CheckerFacts s) : s.scheme.Completeness := by
  intro oracle message positions
  rw [honest_check_event]
  rw [(opens.refines oracle message positions).prEvent_eq]
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro view reached
  simp only [mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨key,_,rfl⟩ := reached
  let salts := actualNonces oracle.permutation key
  let input := honestCheckInput oracle message positions salts
  change (oracle.eval (s.scheme.check input.commitment input.positions input.values input.proof)).1 = true
  rw [scheme_check_observation]
  dsimp only
  erw [checks.honestAccepted oracle message positions salts]
  rfl

include commit in
theorem certificate_of_facts (admitted : s.Admission) (opens : OpeningFacts s openingCycles proofBytes) (checks : CheckerFacts s)
    (privateView : s.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120))) :
    Certificate s proofBytes commitCycles openingCycles where
  admission := admitted
  machineSuccess := machine_success commit opens
  termination := termination commit opens checks
  completeness := completeness opens checks
  honestBudgets := honest_budgets commit opens checks
  proofSize := proof_size opens
  proverCycles := prover_cycles commit opens
  binding := checks.binding
  hidingProperty := privateView

end TwoPermutationPrototype.PentaNonceCertificate
