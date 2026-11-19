import CommitGolfCandidate.TwoPermutationPinnedTranscript
import CommitGolfCandidate.TwoPermutationPackedOpeningProofBytes
import CommitGolfCandidate.TwoPermutationPackedOpeningRecords
import CommitGolfCandidate.TwoPermutationPackedOpeningRecordRun

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open Opening (groupsBefore lower_swap_bound lowerNode trapdoorHeap trapdoorSalt openingNodes
  cap_frontier_nodes_small cap_span_root)

local instance openingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

theorem opening_physical (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    ∃ result : Execution, s.run .opening (trapdoor, positions) = pure result ∧ OpenPhysical s trapdoor positions result :=
  opening_physical_with (execute_records_from_step execute_record) s abi trapdoor positions

theorem scheme_open_bytes (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions) :
    s.scheme.opening trapdoor positions = pure (proofFromTrapdoor (s := s) trapdoor positions) :=
  scheme_open_bytes_with (execute_records_from_step execute_record) s abi trapdoor positions

theorem opening_proof_size (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) (positions : Positions)
    (result : Execution) (physical : OpenPhysical s trapdoor positions result) :
    (s.readProof result).length = (result.state.getReg .x11).toNat := by
  simp only [Submission.readProof, opening_success s abi trapdoor positions result physical,
    ite_true, List.length_map, List.length_range]

theorem opening_scored_attainment (s : Submission) (abi : OpeningABI s)
    (trapdoor : BitVec (8*s.sizes.trapdoor)) :
    ∃ (positions : Positions) (result : Execution), positions.card = BATCH ∧
      s.run .opening (trapdoor, positions) = pure result ∧
      result.cycles = 88311 ∧ (s.readProof result).length = 67584 := by
  obtain ⟨positions, count, cycleVal, byteVal⟩ := scheduled_scored_attainment
  obtain ⟨result, run, physical⟩ := opening_physical s abi trapdoor positions
  exact ⟨positions, result, count, run, physical.cycles.trans cycleVal,
    (opening_proof_size s abi trapdoor positions result physical).trans (physical.length.trans byteVal)⟩

/-- Compose the exact packed opener with the commit distribution supplied by the concrete heap proof. -/
theorem transcript_refines (s : Submission) (abi : OpeningABI s)
    (trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*s.sizes.trapdoor))
    (distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          let leaves := pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts
          pure (transcriptHeap true oracle.compression leaves 1, trapdoorOf oracle message salts)))
    (nonce : ∀ oracle message salts index,
      trapdoorSalt (s := s) (trapdoorOf oracle message salts) index = salts index)
    (heap : ∀ oracle message salts node, 0<node → node<2*LENGTH →
      trapdoorHeap (s := s) (trapdoorOf oracle message salts) node =
        transcriptHeap true oracle.compression
          (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) node) :
    PinnedTranscriptRefines s.scheme (transcriptBuilder true) := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((distribution oracle message).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro salts
  rw [scheme_open_bytes s abi, pure_bind, fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (trapdoorOf oracle message salts) positions
    oracle.compression (pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
    salts (heap oracle message salts) (nonce oracle message salts)
  rw [proof]
  rfl

end TwoPermutationPrototype.PackedOpening
