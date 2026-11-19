import CommitGolfCandidate.QuadCheckPentaRecord
import CommitGolfCandidate.TwoPermutationHonestBytes

/-! All penta records in ascending order, then the final proof-length check
(word 273: the proof cursor must equal the proof end) and the accepting exit. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Quad (PentaOpening)
open TwoPermutationPrototype.Checker (honestIndex honestOrder honest_order_length check_recorded_map)
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

structure CheckerObservationFacts (oracle : Oracle) (input : CheckInput)
    (observed : (Execution × List PublicRow) × Nat) : Prop where
  terminates : observed.1.1.exit ≠ .unfinished
  queries : observed.2 ≤ 25*input.positions.card
  paths : observed.1.1.exit = .success → ∀ index : {i // i ∈ input.positions},
    PentaOpening oracle index.val (input.values index) input.commitment observed.1.2
  honest : ∀ message salts, input = honestCheckInput oracle message input.positions salts →
    observed.1.1.exit = .success

theorem CheckerObservationFacts.charge {oracle : Oracle} {input : CheckInput}
    {result : (Execution × List PublicRow) × Nat} (good : CheckerObservationFacts oracle input result)
    (cycles : Nat) :
    CheckerObservationFacts oracle input ((result.1.1.charge cycles 0, result.1.2), result.2) :=
  ⟨good.terminates, good.queries, good.paths, good.honest⟩

structure PentaCollection where
  state : MachineState
  steps : Nat
  cycles : Nat
  records : Nat
  rows : List PublicRow
  rejected : Bool

noncomputable def collectPenta (oracle : Oracle) (input : CheckInput) :
    Nat → Nat → MachineState → PentaCollection
  | 0, _, state => ⟨state,0,0,0,[],false⟩
  | left+1, ordinal, state => by
    classical
    exact if present : ordinal < input.positions.card then
      let out := recordOutcome oracle ordinal (honestIndex input.positions ordinal present).val state
      if out.accepted then
        let rest := collectPenta oracle input left (ordinal+1) out.state
        ⟨rest.state,out.steps+rest.steps,out.cycles+rest.cycles,rest.records+1,out.rows++rest.rows,rest.rejected⟩
      else ⟨out.state,out.steps,out.cycles,1,out.rows,true⟩
    else ⟨state,0,0,0,[],true⟩

structure CollectFacts (oracle : Oracle) (input : CheckInput) (ordinal left : Nat) (start : MachineState)
    (result : PentaCollection) : Prop where
  stepBound : result.steps ≤ 2048*left
  records : result.records ≤ left
  run : ∀ fuel,
    let tail := checkEvaluation oracle (recordRows (execute packedImage fuel result.state false))
    checkEvaluation oracle (recordRows (execute packedImage (result.steps+fuel) start false)) =
      ((tail.1.1.charge result.cycles (13*result.records),result.rows++tail.1.2),13*result.records+tail.2)
  rejected : result.rejected=true → result.state.pc=0x15b0
  live : result.rejected=false → RecordCursor input input.positions.card result.state ∧
    ∀ later (present : later < input.positions.card), ordinal≤later →
      let index := honestIndex input.positions later present
      PentaOpening oracle index.val (input.values index) input.commitment result.rows
  honest : ∀ message salts, input=honestCheckInput oracle message input.positions salts → result.rejected=false

attribute [local irreducible] execute checkEvaluation recordRows

theorem collect_penta_facts (oracle : Oracle) (input : CheckInput) (fits : ProofWithin input) :
    ∀ left ordinal state, ordinal+left=input.positions.card → RecordCursor input ordinal state →
      RecordInputFrame input ordinal state →
      CollectFacts oracle input ordinal left state (collectPenta oracle input left ordinal state) := by
  intro left
  induction left with
  | zero =>
    intro ordinal state count cursor _
    have done : ordinal=input.positions.card := by omega
    subst ordinal
    refine ⟨Nat.zero_le _,Nat.zero_le _,?_,(fun h => by cases h),?_,fun _ _ _ => rfl⟩
    · intro fuel
      simp [collectPenta,Execution.charge]
    · intro _
      exact ⟨cursor,fun later present low => absurd present (by omega)⟩
  | succ left ih =>
    intro ordinal state count cursor framed
    have present : ordinal < input.positions.card := by omega
    let out := recordOutcome oracle ordinal (honestIndex input.positions ordinal present).val state
    have facts : RecordFacts oracle input ordinal present state out :=
      record_facts oracle input ordinal present state fits cursor framed
    have unfold1 : collectPenta oracle input (left+1) ordinal state=
        if out.accepted then
          ⟨(collectPenta oracle input left (ordinal+1) out.state).state,
            out.steps+(collectPenta oracle input left (ordinal+1) out.state).steps,
            out.cycles+(collectPenta oracle input left (ordinal+1) out.state).cycles,
            (collectPenta oracle input left (ordinal+1) out.state).records+1,
            out.rows++(collectPenta oracle input left (ordinal+1) out.state).rows,
            (collectPenta oracle input left (ordinal+1) out.state).rejected⟩
        else ⟨out.state,out.steps,out.cycles,1,out.rows,true⟩ := by
      rw [collectPenta,dif_pos present]
    cases accepted : out.accepted with
    | true =>
      rw [unfold1,if_pos accepted]
      have tail := ih (ordinal+1) out.state (by omega) (facts.cursor accepted) (facts.frame accepted)
      generalize collectPenta oracle input left (ordinal+1) out.state = rest at tail ⊢
      refine ⟨?_,?_,?_,tail.rejected,?_,tail.honest⟩
      · have a := facts.steps; have b := tail.stepBound
        change out.steps+rest.steps≤2048*(left+1)
        omega
      · have b := tail.records
        change rest.records+1≤left+1
        omega
      · intro fuel
        dsimp only
        rw [show out.steps+rest.steps+fuel=out.steps+(rest.steps+fuel) by omega,facts.run,tail.run]
        simp only [Execution.charge,List.append_assoc]
        refine Prod.ext (Prod.ext ?_ rfl) ?_
        · dsimp only; congr 1 <;> omega
        · simp only; omega
      · intro live
        obtain ⟨finalCursor,openings⟩ := tail.live live
        refine ⟨finalCursor,?_⟩
        intro later laterPresent low
        by_cases same : later=ordinal
        · subst later
          exact (facts.opening accepted).mono (fun _ h => List.mem_append_left _ h)
        · exact (openings later laterPresent (by omega)).mono (fun _ h => List.mem_append_right _ h)
    | false =>
      rw [unfold1,if_neg (by rw [accepted]; decide)]
      refine ⟨?_,by simp,?_,fun _ => facts.rejected accepted,(fun h => by cases h),?_⟩
      · have a := facts.steps
        change out.steps≤2048*(left+1)
        omega
      · intro fuel
        simpa only [Nat.mul_one] using facts.run fuel
      · intro message salts canonical
        have := facts.honest message salts canonical
        rw [accepted] at this
        cases this

/-! ### Final length check and acceptance -/

def finalBranch (s : MachineState) : MachineState := execInstrBr s (.BNE .x21 .x22 364)

def acceptState (state : MachineState) : MachineState :=
  ((state.setReg .x5 1).setReg .x10 0).setPC 0x159c

theorem execute_accept (state : MachineState) (pc : state.pc = 0x1594) (fuel : Nat) :
    execute packedImage (3+fuel) state false = pure ⟨.success, acceptState state, 3, 0⟩ := by
  let first := (state.setReg .x5 1).setPC 0x1598
  have a := fetch_at state 357 (.ADDI .x5 .x0 1) (by decide) pc rfl
  have b := fetch_at first 358 (.ADDI .x10 .x0 0) (by decide) rfl rfl
  have c := fetch_at (acceptState state) 359 .ECALL (by decide) rfl rfl
  have r : ordinaryStep state (.base (.ADDI .x5 .x0 1)) = some first := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, first] <;> rfl
  have t : ordinaryStep first (.base (.ADDI .x10 .x0 0)) = some (acceptState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, first, acceptState] <;> rfl
  rw [Nat.add_comm 3 fuel]
  simp only [execute, a, b, c, r, t, instructionCycles, pure_bind]
  rfl

theorem execute_final (state : MachineState) (pc : state.pc=0x1444) (fuel : Nat) :
    ∃ result : Execution, execute packedImage (5+fuel) state false=pure result ∧
      result.exit≠.unfinished ∧ (result.exit=.success ↔ state.getReg .x21=state.getReg .x22) := by
  let b := finalBranch state
  have fb := fetch_at state 273 (.BNE .x21 .x22 364) (by decide) pc rfl
  have stepB : ordinaryStep state (.base (.BNE .x21 .x22 364))=some b := rfl
  by_cases same : state.getReg .x21=state.getReg .x22
  · have bpc : b.pc=BitVec.ofNat 64 (4096+4*274) := by
      simp only [b,finalBranch,execInstrBr,same,bne_self_eq_false,Bool.false_eq_true,ite_false,
        MachineState.setPC,pc]; rfl
    let j := execInstrBr b (.JAL .x0 332)
    have fj := fetch_at b 274 (.JAL .x0 332) (by decide) bpc rfl
    have stepJ : ordinaryStep b (.base (.JAL .x0 332))=some j := rfl
    have jpc : j.pc=0x1594 := by
      simp only [j,execInstrBr,MachineState.setPC,MachineState.setReg,bpc]; rfl
    refine ⟨⟨.success,acceptState j,5,0⟩,?_,(by intro h; cases h),(by simp [same])⟩
    rw [show 5+fuel=(3+fuel+1)+1 by omega,execute_ordinary_step _ _ _ _ _ _ fb stepB,
      execute_ordinary_step _ _ _ _ _ _ fj stepJ,execute_accept j jpc]
    simp [instructionCycles,Execution.charge]
  · have bpc : b.pc=0x15b0 := by
      have ne : (state.getReg .x21 != state.getReg .x22)=true := by simpa using same
      simp only [b,finalBranch,execInstrBr,ne,ite_true,MachineState.setPC,pc]; rfl
    refine ⟨⟨.failure,headerRejectState b,4,0⟩,?_,(by intro h; cases h),(by simp [same])⟩
    rw [show 5+fuel=(3+(fuel+1))+1 by omega,execute_ordinary_step _ _ _ _ _ _ fb stepB,
      execute_header_reject b bpc]
    simp [instructionCycles,Execution.charge]

theorem final_honest (input : CheckInput) (state : MachineState) (cursor : RecordCursor input input.positions.card state)
    (length : input.proof.length=1424*input.positions.card) : state.getReg .x21=state.getReg .x22 := by
  rw [cursor.proof,cursor.proofEnd,length]
  unfold checkProofByte
  rfl

/-- Every opened position appears at some ordinal of the ascending order. -/
theorem every_index_ordinal (input : CheckInput) (index : {i // i ∈ input.positions}) :
    ∃ ordinal, ∃ present : ordinal < input.positions.card, honestIndex input.positions ordinal present=index := by
  have appears : index ∈ honestOrder input.positions := by simp [honestOrder]
  obtain ⟨ordinal,within,selected⟩ := List.mem_iff_getElem.mp appears
  exact ⟨ordinal,by simpa only [honest_order_length] using within,selected⟩

theorem checker_body_facts (oracle : Oracle) (input : CheckInput) (beginning : MachineState)
    (fits : ProofWithin input) (cursor : RecordCursor input 0 beginning) (frame : RecordInputFrame input 0 beginning)
    (fuel : Nat) (fuelBound : 2048*input.positions.card+5 ≤ fuel) :
    CheckerObservationFacts oracle input
      (checkEvaluation oracle (recordRows (execute packedImage fuel beginning false))) := by
  let collected := collectPenta oracle input input.positions.card 0 beginning
  have facts := collect_penta_facts oracle input fits input.positions.card 0 beginning (by omega) cursor frame
  let rest := fuel-collected.steps
  have limit : collected.steps ≤ 2048*input.positions.card := facts.stepBound
  have enough : 5 ≤ rest := by dsimp only [rest]; omega
  have total : collected.steps+rest = fuel := by dsimp only [rest]; omega
  have run := facts.run rest
  rw [total] at run
  rw [run]
  have count : collected.records ≤ input.positions.card := by simpa using facts.records
  cases rejected : collected.rejected with
  | true =>
    have pc := facts.rejected rejected
    have finish : execute packedImage rest collected.state false = pure ⟨.failure,headerRejectState collected.state,3,0⟩ := by
      rw [show rest=3+(rest-3) by omega]
      exact execute_header_reject _ pc _
    rw [finish,record_rows_pure,check_evaluation_pure]
    refine ⟨?_,?_,?_,?_⟩
    · intro impossible
      cases impossible
    · change 13*collected.records+0 ≤ 25*input.positions.card
      omega
    · intro impossible
      cases impossible
    · intro message salts canonical
      have accepts := facts.honest message salts canonical
      rw [rejected] at accepts
      cases accepts
  | false =>
    obtain ⟨finalCursor,openings⟩ := facts.live rejected
    have pc : collected.state.pc=0x1444 := finalCursor.pc.trans (ite_eq_left rfl)
    obtain ⟨result,executed,ends,accepts⟩ := execute_final collected.state pc (rest-5)
    rw [show rest=5+(rest-5) by omega,executed,record_rows_pure,check_evaluation_pure]
    refine ⟨?_,?_,?_,?_⟩
    · exact ends
    · change 13*collected.records+0 ≤ 25*input.positions.card
      omega
    · intro success index
      obtain ⟨ordinal,present,selected⟩ := every_index_ordinal input index
      have opening := openings ordinal present (Nat.zero_le _)
      dsimp only at opening
      rw [selected] at opening
      exact opening.mono (fun _ h => List.mem_append_left _ h)
    · intro message salts canonical
      apply accepts.mpr
      apply final_honest input _ finalCursor
      rw [canonical]
      exact Honest.honest_proof_length oracle message input.positions salts

end TwoPermutationPrototype.Quad.Checker
