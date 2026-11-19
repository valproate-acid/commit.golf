import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedCommit
import CommitGolfCandidate.TwoPermutationPackedParentMeaning
import CommitGolfCandidate.TwoPermutationOpeningTranscript
import CommitGolfCandidate.TwoPermutationSubmission
import CommitGolfCandidate.TwoPermutationRootBytes

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_support check_evaluation_pure
  check_evaluation_bind fixedOracleRun fixed_oracle_run_map oracle_run_bind oracle_run_pure
  splitBlocks split_blocks_bijective)
abbrev packedSubmission : Submission := CommitGolfCandidate.PackedCommitArtifact.submission

def packedPublicTree (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  transcriptHeap true oracle.compression (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)

set_option maxRecDepth 16384
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation packed_wideCommitBody packed_wideCommitTrace packedParentGroups rootPrefix

structure PackedLeafMeaning (leaves : PackedLeafExecution) where
  counted : ∀ oracle state, RunPublic oracle (leaves.trace state) 33554432
  content : ∀ (oracle : Oracle) (message : Message) (packed : BitVec (128*LENGTH)),
    let salts := splitBlocks 128 LENGTH packed
    let state := packed_wideReadyState (packedSubmission.initialState .commit message) packed
    let out := (checkEvaluation oracle (leaves.trace state)).1
    ParentContent (parentSetup out 5) (packedPublicTree oracle message salts) salts (2^24-1)

private theorem packed_wide_entry (message : Message) :
    CommitEntry (packedSubmission.initialState .commit message) := ⟨rfl,rfl,rfl,rfl⟩

theorem packed_wide_counted_body (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    RunPublic oracle (packed_wideCommitBody leaves initial packed) 50331647 := by
  unfold packed_wideCommitBody
  apply run_bind_public _ _ _ 33554432 16777215 (meaning.counted ..)
  intro out
  exact run_bind_public _ _ _ (46995*357) 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

def packed_widePackedOutput (leaves : PackedLeafExecution) (oracle : Oracle) (initial : MachineState)
    {bits : Nat} (packed : BitVec bits) : Execution :=
  ⟨.success,(checkEvaluation oracle (packed_wideCommitBody leaves initial packed)).1,637936351,50331647⟩

theorem packed_wide_counted_trace (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (initial : MachineState) :
    oracle.run (packed_wideCommitTrace leaves initial) =
      (do let packed ← $ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)
          return (packed_widePackedOutput leaves oracle initial packed,50331647)) := by
  unfold packed_wideCommitTrace
  rw [CommitGolfCandidate.oracle_run_coins_bind]
  apply bind_congr_of_forall_mem_support
  intro packed _
  rw [oracle_run_bind,show oracle.run (packed_wideCommitBody leaves initial packed)=_ from
    packed_wide_counted_body leaves meaning oracle initial packed,pure_bind]
  simp only [oracle_run_pure,pure_bind,Nat.add_zero]
  rfl

private theorem packed_wide_output_eq (leaves : PackedLeafExecution) (oracle : Oracle)
    (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    packed_widePackedOutput leaves oracle initial packed =
      ⟨.success,(checkEvaluation oracle (packed_wideCommitBody leaves initial packed)).1,637936351,50331647⟩ := rfl

private theorem execution_state (state : MachineState) :
    (⟨.success,state,637936351,50331647⟩ : Execution).state = state := rfl

attribute [local irreducible] packed_widePackedOutput

private theorem evaluated_finish (oracle : Oracle) (p : OracleComp World MachineState)
    (f : MachineState → OracleComp World MachineState) (finish : MachineState → MachineState) :
    (checkEvaluation oracle (p >>= fun s => f s >>= fun t => pure (finish t))).1 =
      finish (checkEvaluation oracle (f (checkEvaluation oracle p).1)).1 := by
  simp only [check_evaluation_bind,check_evaluation_pure]

private theorem packed_wide_eval_body (oracle : Oracle) (p : OracleComp World MachineState) :
    (checkEvaluation oracle (do
        let out ← p
        let parents ← packedParentGroups 184804 46995 357 (parentSetup out 5)
        return rootPrefix parents 10)).1 =
      rootPrefix (checkEvaluation oracle (packedParentGroups 184804 46995 357
        (parentSetup (checkEvaluation oracle p).1 5))).1 10 :=
  evaluated_finish oracle p
    (fun out => packedParentGroups 184804 46995 357 (parentSetup out 5))
    (fun parents => rootPrefix parents 10)

private theorem packed_wide_packed_state (leaves : PackedLeafExecution) (oracle : Oracle)
    (initial : MachineState) {bits : Nat} (packed : BitVec bits) :
    let state := packed_wideReadyState initial packed
    let out := (checkEvaluation oracle (leaves.trace state)).1
    let parents := (checkEvaluation oracle (packedParentGroups 184804 46995 357 (parentSetup out 5))).1
    (packed_widePackedOutput leaves oracle initial packed).state = rootPrefix parents 10 := by
  have projection := congrArg Execution.state (packed_wide_output_eq leaves oracle initial packed)
  refine projection.trans ((execution_state _).trans ?_)
  unfold packed_wideCommitBody
  exact packed_wide_eval_body oracle (leaves.trace (packed_wideReadyState initial packed))

private def serializationModel := Assembly.checkerReference commitImage

private theorem codecABI : CommitABI serializationModel where
  code := rfl
  message := rfl
  output := rfl
  trapdoor := rfl
  size := rfl
  fuel := by decide

private theorem packed_wide_serialized (parents : MachineState) (heap : Nat → BitVec 256)
    (salts : Index → BitVec 128) (result : Execution)
    (state : result.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (outReg : parents.getReg .x8=4294971392) (content : ParentContent parents heap salts 0) :
    (packedSubmission.readCommit result).1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → (packedSubmission.readCommit result).2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, (packedSubmission.readCommit result).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  have equality : packedSubmission.readCommit result = serializationModel.readCommit result := by
    simp only [Submission.readCommit, packedSubmission, CommitGolfCandidate.PackedCommitArtifact.submission, serializationModel, Assembly.checkerReference]
  rw [equality]
  exact serialized_parent_results serializationModel codecABI parents heap salts result state heapReg outReg content

theorem packed_wide_physical_results (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (message : Message) (packed : BitVec (128*LENGTH)) :
    let result := packed_widePackedOutput leaves oracle (packedSubmission.initialState .commit message) packed
    let output := packedSubmission.readCommit result
    let salts := splitBlocks 128 LENGTH packed
    let heap := packedPublicTree oracle message salts
    output.1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → output.2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, output.2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  let initial := packedSubmission.initialState .commit message
  let ready := packed_wideReadyState initial packed
  let out := (checkEvaluation oracle (leaves.trace ready)).1
  let start := parentSetup out 5
  let parents := (checkEvaluation oracle (packedParentGroups 184804 46995 357 start)).1
  let salts := splitBlocks 128 LENGTH packed
  let heap := packedPublicTree oracle message salts
  have tree (n : Nat) (positive : 0<n) (inner : n<LENGTH) :
      heap n=projectReply (oracle.compression (heap (2*n+1) ++ heap (2*n))) :=
    transcript_heap_parent true _ _ n positive inner
  have initialContent := meaning.content oracle message packed
  have finished := leaves.finished initial (packed_wide_entry message) packed out
    (check_evaluation_support oracle (leaves.trace ready))
  obtain ⟨regs,pc,keep⟩ := packed_wide_parent_setup_ready out finished.pc finished.selector finished.heap finished.stride finished.stop
  have content : ParentContent parents heap salts 0 :=
    packed_parent_content oracle 184804 46995 357 start heap salts (by decide) tree initialContent regs
  obtain ⟨endRegs,_,resultReg⟩ := packed_parent_phase_post start regs pc
    (check_evaluation_support oracle (packedParentGroups 184804 46995 357 start))
  have x8 : parents.getReg .x8=4294971392 := resultReg.trans (keep.trans finished.output)
  exact packed_wide_serialized parents heap salts
    (packed_widePackedOutput leaves oracle initial packed) (packed_wide_packed_state leaves oracle initial packed)
    endRegs.heap x8 content

noncomputable def packed_widePackSaltTape : CompleteSaltTape → BitVec (128*LENGTH) :=
  (Equiv.ofBijective (splitBlocks 128 LENGTH) (split_blocks_bijective 128 LENGTH (by decide))).symm

private theorem packed_wide_split_pack (salts : CompleteSaltTape) :
    splitBlocks 128 LENGTH (packed_widePackSaltTape salts)=salts :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).apply_symm_apply salts

private theorem packed_wide_pack_split (packed : BitVec (128*LENGTH)) :
    packed_widePackSaltTape (splitBlocks 128 LENGTH packed)=packed :=
  (Equiv.ofBijective _ (split_blocks_bijective 128 LENGTH (by decide))).symm_apply_apply packed

noncomputable def packed_wideTrapdoor (leaves : PackedLeafExecution) (oracle : Oracle)
    (message : Message) (salts : CompleteSaltTape) :
    BitVec (8*packedSubmission.sizes.trapdoor) :=
  (packedSubmission.readCommit (packed_widePackedOutput leaves oracle
    (packedSubmission.initialState .commit message) (packed_widePackSaltTape salts))).2

private theorem packed_wide_normalize_draw {α : Type} (bits : Nat)
    (width : bits=128*LENGTH) (f : {n : Nat} → BitVec n → α) :
    (do let packed ← $ᵗ BitVec bits; pure (f packed) : ProbComp α) =
      (do let packed ← $ᵗ BitVec (128*LENGTH); pure (f packed)) := by subst bits; rfl

theorem packed_wide_commit_distribution (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves)
    (oracle : Oracle) (message : Message) :
    fixedOracleRun oracle (packedSubmission.scheme.commit message) =
      (do let packed ← $ᵗ BitVec (128*LENGTH)
          let salts := splitBlocks 128 LENGTH packed
          pure (packedPublicTree oracle message salts 1,packed_wideTrapdoor leaves oracle message salts)) := by
  let initial := packedSubmission.initialState .commit message
  have entry := packed_wide_entry message
  have width : 8*((initialPrefix initial 11).getReg .x11).toNat=128*LENGTH := by
    rw [(setup_registers initial entry).size]; rfl
  change fixedOracleRun oracle (packedSubmission.readCommit <$> packedSubmission.run .commit message)=_
  rw [packed_submission_wide_commit_run leaves packedSubmission packed_manifest_image.symm (by decide) message entry, fixed_oracle_run_map]
  unfold fixedOracleRun
  rw [packed_wide_counted_trace leaves meaning]
  simp only [map_bind,map_pure]
  change (do let packed ← $ᵗ BitVec (8*((initialPrefix initial 11).getReg .x11).toNat)
             pure (packedSubmission.readCommit (packed_widePackedOutput leaves oracle initial packed)))=_
  rw [packed_wide_normalize_draw _ width (fun {_} packed =>
    packedSubmission.readCommit (packed_widePackedOutput leaves oracle initial packed))]
  apply bind_congr_of_forall_mem_support
  intro packed _
  have physical := packed_wide_physical_results leaves meaning oracle message packed
  dsimp only [packed_wideTrapdoor]
  rw [packed_wide_pack_split]
  exact congrArg pure (Prod.ext physical.1 rfl)

structure PackedCommitTranscript where
  trapdoor : Oracle → Message → CompleteSaltTape → BitVec (8*packedSubmission.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (packedSubmission.scheme.commit message) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          pure (packedPublicTree oracle message salts 1,trapdoor oracle message salts))
  nonce : ∀ oracle message salts index,
    Opening.trapdoorSalt (s := packedSubmission) (trapdoor oracle message salts) index=salts index
  heap : ∀ oracle message salts node, 0<node → node<2*LENGTH →
    Opening.trapdoorHeap (s := packedSubmission) (trapdoor oracle message salts) node=
      packedPublicTree oracle message salts node

noncomputable def packedVerifiedTranscript (leaves : PackedLeafExecution) (meaning : PackedLeafMeaning leaves) :
    PackedCommitTranscript where
  trapdoor := packed_wideTrapdoor leaves
  distribution := by
    intro oracle message
    rw [packed_wide_commit_distribution leaves meaning]
    exact packed_salt_tape_uniform
      (fun salts => pure (packedPublicTree oracle message salts 1,packed_wideTrapdoor leaves oracle message salts))
  nonce := by
    intro oracle message salts i
    have eq := (packed_wide_physical_results leaves meaning oracle message (packed_widePackSaltTape salts)).2.2 i
    simpa only [Opening.trapdoorSalt,packed_wideTrapdoor,packed_wide_split_pack] using eq
  heap := by
    intro oracle message salts n positive bound
    have eq := (packed_wide_physical_results leaves meaning oracle message (packed_widePackSaltTape salts)).2.1 n positive bound
    simpa only [Opening.trapdoorHeap,packed_wideTrapdoor,packed_wide_split_pack] using eq

end TwoPermutationPrototype.RV64
