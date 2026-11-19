import CommitGolfCandidate.TwoPermutationPackedCapWalk
import CommitGolfCandidate.TwoPermutationPackedCapRootRun

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt cap_hash_count_tree cap_hash_count_root)

theorem cap_outside_digest {groups : List Nat} {node : Nat} {before after : MachineState}
    (frame : CapFrame groups node before after) (address : Nat)
    (above : 4096 ≤ address) (bounded : address+4 ≤ 2^61) :
    readBuffer after (8*address) 32 = readBuffer before (8*address) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro word inside
  simp only [← Nat.mul_add]
  exact frame (address+word) (by omega) (Or.inr (Or.inl (by omega)))

private theorem root_test_memory (state : MachineState) : (capRootTest state).mem = state.mem := by
  by_cases root : state.getReg .x6 = 1#64 <;>
    simp [capRootTest, blockPrefix, capRootTestCode, execInstrBr, signExtend12, MachineState.getReg_setPC,
      Opening.getReg_setReg, show state.getReg .x0 = 0#64 from rfl, root] <;> rfl

structure CapFinished (oracle : Oracle) (groups : List Nat) (before : MachineState) (pointer claim fuel : Nat) : Prop where
  calls : (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).2 ≤ 255
  honestCalls : (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).2 ≤ 8*groups.length
  paths : let observed := checkEvaluation oracle (recordRows (execute packedImage fuel before false))
    observed.1.1.exit = .success → ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 →
      ProjectedPath observed.1.2 leaf 8 (capRootAt before leaf) (readBuffer before (8*claim) 32)
  terminates : (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).1.1.exit ≠ .unfinished
  honest : ∀ heap, CapHeapCorrect oracle heap → CapContents groups before 1 8 pointer heap →
    readBuffer before (8*claim) 32 = heap 1 →
    before.getReg .x22 = BitVec.ofNat 64 (pointer+30*(capFrontierNodes groups 1 8).length) →
    (checkEvaluation oracle (recordRows (execute packedImage fuel before false))).1.1.exit = .success

theorem execute_prepared_cap_suffix (codec : FrontierKernel) (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (position : CapPosition groups before 1 pointer)
    (pc : before.pc = 0x147c) (claimReg : before.getReg .x9 = wordAddress claim)
    (claimAbove : 4096 ≤ claim) (claimBound : claim+4 ≤ 2^33)
    (room : pointer+30*(capFrontierNodes groups 1 8).length ≤ MEMORY_BYTES)
    (fuelBound : 22502 ≤ fuel) : CapFinished oracle groups before pointer claim fuel := by
  obtain ⟨walk⟩ := execute_cap_subtree codec oracle groups before 1 8 pointer position pc Opening.cap_span_root room
  have steps : walk.segment.steps ≤ 22484 := walk.steps
  have leftFuel : 18 ≤ fuel-walk.segment.steps := by omega
  have observed := walk.segment.checked (fuel-walk.segment.steps)
  rw [show walk.segment.steps+(fuel-walk.segment.steps) = fuel by omega] at observed
  have hashCount := walk.calls.trans (cap_hash_count_tree groups 1 8)
  have groupCount := walk.calls.trans (cap_hash_count_root groups)
  have loadedClaim := cap_outside_digest walk.frame claim claimAbove (by omega)
  by_cases done : walk.done = true
  · have actual := walk.position done
    have finishedPC : walk.state.pc = 0x1528 := by simpa [done] using walk.pc
    let tested := capRootTest walk.state
    have testedPC : tested.pc = 0x1560 := by
      rw [cap_root_post _ finishedPC, actual.heap]
      rfl
    have testedRoots : tested.getReg .x25 = wordAddress 2048 :=
      (root_test_register _ .x25 (by decide)).trans actual.context.controls.roots
    have testedClaim : tested.getReg .x9 = wordAddress claim :=
      (root_test_register _ .x9 (by decide)).trans ((walk.stable .x9 (by decide)).trans claimReg)
    obtain ⟨result, accepted, count, ended, checkRoot⟩ :=
      execute_root_check tested claim (fuel-walk.segment.steps-18) testedPC testedRoots testedClaim claimBound
    have finalRun : execute packedImage (fuel-walk.segment.steps) walk.state false = pure (result.charge 2 0) := by
      rw [show fuel-walk.segment.steps = 2+(16+(fuel-walk.segment.steps-18)) by omega,
        execute_cap_root_test _ finishedPC, checkRoot]
      simp
    rw [finalRun, record_rows_pure, check_evaluation_pure] at observed
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [observed]
      simpa using hashCount
    · rw [observed]
      simpa using groupCount
    · dsimp only
      rw [observed]
      intro success leaf active low high
      have good : result.exit = .success := success
      have verified := (accepted.mp good).2
      have root : capRootAt tested 1 = capRootAt walk.state 1 := by
        unfold capRootAt
        exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun (root_test_memory walk.state) _)
      have claimStayed : readBuffer tested (8*claim) 32 = readBuffer walk.state (8*claim) 32 :=
        read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun (root_test_memory walk.state) _)
      have final := root.symm.trans (verified.trans (claimStayed.trans loadedClaim))
      have path := walk.authentic done leaf active low high (by omega)
      rw [final] at path
      simpa using path
    · rw [observed]
      exact ended
    · intro heap canonical contents rootClaim finishProof
      have heapRoot := walk.realizes done heap canonical contents
      have testedRoot : capRootAt tested 1 = capRootAt walk.state 1 := by
        unfold capRootAt
        exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun (root_test_memory walk.state) _)
      have claimStayed : readBuffer tested (8*claim) 32 = readBuffer walk.state (8*claim) 32 :=
        read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun (root_test_memory walk.state) _)
      have lengthOK : tested.getReg .x21 = tested.getReg .x22 := by
        rw [root_test_register _ .x21 (by decide), root_test_register _ .x22 (by decide), actual.proof,
          walk.stable .x22 (by decide), finishProof, walk.readLength done]
      have good := accepted.mpr ⟨lengthOK, testedRoot.trans (heapRoot.trans
        ((claimStayed.trans (loadedClaim.trans rootClaim)).symm))⟩
      rw [observed]
      exact good
  · have falseDone : walk.done = false := Bool.eq_false_iff.mpr done
    have failed : walk.state.pc = 0x15b0 := by simpa [falseDone] using walk.pc
    have finalRun : execute packedImage (fuel-walk.segment.steps) walk.state false =
        pure ⟨.failure,rejectState walk.state,3,0⟩ := by
      rw [show fuel-walk.segment.steps = 3+(fuel-walk.segment.steps-3) by omega]
      exact execute_reject _ failed _
    rw [finalRun, record_rows_pure, check_evaluation_pure] at observed
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [observed]
      simpa using hashCount
    · rw [observed]
      simpa using groupCount
    · dsimp only
      rw [observed]
      intro impossible
      cases impossible
    · rw [observed]
      exact (show Exit.failure ≠ Exit.unfinished by decide)
    · intro _ _ _ _ finishProof
      have fit : MEMORY_BYTES < 2^64 := by decide
      have enough : pointer+30*(capFrontierNodes groups 1 8).length ≤ (before.getReg .x22).toNat := by
        rw [finishProof, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact False.elim (done (walk.available enough))

end TwoPermutationPrototype.Packed.Checker
