import CommitGolfCandidate.QuadCheckPentaBody
import CommitGolfCandidate.QuadHeaderAssembly
import CommitGolfCandidate.QuadBindingPaths
import CommitGolfCandidate.QuadCertificate

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (checkObservation check_recorded_map)

open TwoPermutationPrototype.Quad.Honest (honest_input_empty honest_input_records_fit honest_input_admitted)
set_option maxRecDepth 32768
set_option maxHeartbeats 1800000

attribute [local irreducible] execute checkEvaluation

private theorem observation_admitted (oracle : Oracle) (input : CheckInput)
    (admitted : input.proof.length ≤ loaderReference.sizes.proof) :
    checkObservation loaderReference oracle input =
      checkEvaluation oracle (recordRows
        (execute packedImage 34359803904 (loaderReference.initialState .check input) false)) := by
  unfold checkObservation
  erw [check_run_admitted input admitted]

private theorem observation_oversized (oracle : Oracle) (input : CheckInput)
    (oversized : loaderReference.sizes.proof < input.proof.length) :
    checkObservation loaderReference oracle input = ((⟨.failure,initialMachine,0,0⟩,[]),0) := by
  unfold checkObservation
  erw [check_run_oversized input oversized]
  rw [record_rows_pure,check_evaluation_pure]

private abbrev rawObserved (oracle : Oracle) (input : CheckInput) :=
  checkEvaluation oracle (recordRows
    (execute packedImage 34359803904 (loaderReference.initialState .check input) false))

private theorem raw_empty (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 23890755584) (empty : input.positions.card = 0) :
    CheckerObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨result, executed, terminal, succeeds⟩ := header_empty input fits empty
  unfold rawObserved
  rw [executed, record_rows_pure, check_evaluation_pure]
  refine ⟨terminal,Nat.zero_le _,?_,?_⟩
  · intro _ index
    have nonempty := Finset.card_pos.mpr ⟨index.val,index.property⟩
    omega
  · intro message salts canonical
    apply succeeds
    exact canonical.symm ▸ honest_input_empty oracle message input.positions salts empty

private theorem raw_short (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 23890755584) (short : input.proof.length < 1424*input.positions.card) :
    CheckerObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨result,executed,failed⟩ := header_short input fits short
  unfold rawObserved
  rw [executed, record_rows_pure, check_evaluation_pure]
  refine ⟨?_,Nat.zero_le _,?_,?_⟩
  · change result.exit ≠ .unfinished
    rw [failed]
    decide
  · intro impossible
    change result.exit = .success at impossible
    rw [failed] at impossible
    cases impossible
  · intro message salts canonical
    have required : 1424*input.positions.card ≤ input.proof.length :=
      canonical.symm ▸ honest_input_records_fit oracle message input.positions salts
    omega

private theorem observation_hop (oracle : Oracle) (input : CheckInput)
    (before after : MachineState) (steps cycles fuel : Nat) (hop : Hop before after steps cycles)
    (body : CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel after false)))) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage (steps+fuel) before false))) := by
  rw [hop fuel,bind_pure_comp,check_recorded_map]
  exact body.charge cycles

private theorem raw_positive (oracle : Oracle) (input : CheckInput) (fits : input.proof.length ≤ 23890755584)
    (nonempty : input.positions.card ≠ 0) (long : 1424*input.positions.card ≤ input.proof.length) :
    CheckerObservationFacts oracle input (rawObserved oracle input) := by
  obtain ⟨state,cursor,memory,executeHeader⟩ := header_positive input fits nonempty long
  have cardinal := checker_positions_bound input
  have enough : 2048*input.positions.card+5 ≤ 34359803882 := by omega
  have initialFrame : RecordInputFrame input 0 state := by
    intro word _ _
    exact congrFun memory (wordAddress word)
  have body := checker_body_facts oracle input state ⟨long,fits⟩ cursor initialFrame 34359803882 enough
  exact observation_hop oracle input (loaderReference.initialState .check input) state
    22 25 34359803882 executeHeader body

private theorem raw_checker_observation (oracle : Oracle) (input : CheckInput)
    (fits : input.proof.length ≤ 23890755584) :
    CheckerObservationFacts oracle input (rawObserved oracle input) := by
  by_cases empty : input.positions.card = 0
  · exact raw_empty oracle input fits empty
  by_cases short : input.proof.length < 1424*input.positions.card
  · exact raw_short oracle input fits short
  exact raw_positive oracle input fits empty (Nat.le_of_not_gt short)

theorem checker_complete_observation (oracle : Oracle) (input : CheckInput) :
    CheckerObservationFacts oracle input (checkObservation loaderReference oracle input) := by
  by_cases admitted : input.proof.length ≤ loaderReference.sizes.proof
  · rw [observation_admitted oracle input admitted]
    exact raw_checker_observation oracle input admitted
  · rw [observation_oversized oracle input (Nat.lt_of_not_ge admitted)]
    refine ⟨by decide,Nat.zero_le _,?_,?_⟩
    · intro impossible
      cases impossible
    · intro message salts canonical
      exact (admitted (canonical.symm ▸ honest_input_admitted oracle message input.positions salts)).elim

theorem checker_facts_of_observations (s : Submission)
    (checked : ∀ (oracle : Oracle) (input : CheckInput),
      CheckerObservationFacts oracle input (checkObservation s oracle input)) :
    QuadCertificate.CheckerFacts s := by
  refine ⟨fun oracle input => (checked oracle input).terminates,
    fun oracle input => (checked oracle input).queries.trans (by omega), ?_, ?_⟩
  · apply binding_of_penta_trace s ?_
    intro oracle input
    dsimp only
    intro accepted
    have count := (checked oracle input).queries
    have card := checker_positions_bound input
    exact ⟨by omega,(checked oracle input).paths accepted⟩
  · intro oracle message positions salts
    exact (checked oracle (honestCheckInput oracle message positions salts)).honest message salts rfl

end TwoPermutationPrototype.Quad.Checker
