import CommitGolfCandidate.TwoPermutationOpeningProofBytes

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp

local instance openingDiscreteSpace {α : Type} : MeasurableSpace α := ⊤

private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

private theorem grouping_sorted (positions : Positions) :
    groupsBefore positions positions.card =
      (positions.attach.sort (fun i j => i.val ≤ j.val)).map (capGroup ∘ Subtype.val) := by
  unfold groupsBefore
  have size : (positions.sort (· ≤ ·)).length = positions.card := by simp
  rw [← size, List.take_length, ← sorted_value_indices positions, List.map_map]

private theorem grouping_empty (positions : Positions) :
    (groupsBefore positions positions.card).isEmpty = true ↔ positions.card = 0 := by
  have size : (groupsBefore positions positions.card).length = positions.card := by
    simp [groupsBefore]
  rw [List.isEmpty_iff]
  simpa only [size] using (List.length_eq_zero_iff (l := groupsBefore positions positions.card)).symm

private theorem lower_sibling_positive (index : Index) (level : Nat) (inside : level < 16) :
    0 < lowerNode index level ^^^ 1 := by
  have divisor : 0 < 2^level := by positivity
  have power : 2^level ≤ 65536 :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : level ≤ 16)
  have big : 2 ≤ lowerNode index level := by
    unfold lowerNode
    apply (Nat.le_div_iff_mul_le divisor).mpr
    change 2*2^level ≤ 16777216+index.val
    omega
  by_cases even : lowerNode index level % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

private theorem cap_frontier_positive (groups : List Nat) (node height : Nat)
    (span : CapSpan node height) :
    ∀ n ∈ capFrontierNodes groups node height, 0 < n := by
  induction height generalizing node with
  | zero =>
    have positive := (cap_span_node node 0 span).1
    cases mark : capIsMarked groups node 0 <;> simp [capFrontierNodes,mark,positive]
  | succ height ih =>
    have ⟨left,right⟩ := cap_span_children node height span
    have positive := (cap_span_node node (height+1) span).1
    cases mark : capIsMarked groups node (height+1)
    · simp [capFrontierNodes,mark,positive]
    · intro n member
      simp only [capFrontierNodes,mark,Bool.true_eq,ite_true,List.mem_append] at member
      exact member.elim (ih _ left n) (ih _ right n)

private theorem lower_record_matches (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (heap : Nat → BitVec 256) (salts : CompleteSaltTape) (index : Index)
    (digest : ∀ node, 0 < node → node < 2*LENGTH → trapdoorHeap (s := s) trapdoor node = heap node)
    (salt : ∀ i, trapdoorSalt (s := s) trapdoor i = salts i) :
    lowerRecord false (trapdoorHeap (s := s) trapdoor) index (trapdoorSalt (s := s) trapdoor index) =
      lowerRecord false heap index (salts index) := by
  unfold lowerRecord
  rw [salt]
  congr 1
  apply List.flatMap_congr
  intro level member
  have same := digest _ (lower_sibling_positive index level (List.mem_range.mp member))
    (lower_swap_bound index level)
  simp only [lowerNode] at same
  rw [same]

/-- The pure transcript reconstructed from the concrete trapdoor slices agrees
with the reference transcript for any heap and nonce tape stored by commit. -/
theorem proof_from_trapdoor_matches (s : Submission) (trapdoor : BitVec (8 * s.sizes.trapdoor))
    (positions : Positions) (compress : Compression) (leaves : DigestTape) (salts : CompleteSaltTape)
    (digest : ∀ node, 0 < node → node < 2 * LENGTH →
      trapdoorHeap (s := s) trapdoor node = transcriptHeap false compress leaves node)
    (salt : ∀ index, trapdoorSalt (s := s) trapdoor index = salts index) :
    proofFromTrapdoor (s := s) trapdoor positions =
      (transcriptBuilder false compress positions (fun i => salts i.val) leaves).2 := by
  let heap := transcriptHeap false compress leaves
  unfold proofFromTrapdoor transcriptBuilder
  dsimp only
  congr 1
  · rw [← sorted_value_indices positions, List.flatMap_map]
    apply List.flatMap_congr
    intro index _
    exact lower_record_matches s trapdoor heap salts index.val digest salt
  · unfold frontierProof
    rw [← grouping_sorted positions]
    by_cases empty : positions.card = 0
    · simp [openingNodes, empty, groupsBefore]
    · have someGroups : (groupsBefore positions positions.card).isEmpty = false := by
        cases h : (groupsBefore positions positions.card).isEmpty
        · rfl
        · exact False.elim (empty ((grouping_empty positions).mp h))
      simp only [openingNodes, empty, someGroups, Bool.false_eq_true, ite_false,
        proofDigestBytes]
      apply List.flatMap_congr
      intro node member
      have small := cap_frontier_nodes_small _ 1 8 cap_span_root node member
      have capacity : 512 < 2*LENGTH := by decide
      rw [digest _ (cap_frontier_positive _ 1 8 cap_span_root node member) (small.trans capacity)]

/-- The commit-side refinement needed to instantiate the verified opener. The
serialized trapdoor may contain any extra workspace outside these slices. -/
structure CommitTranscript (s : Submission) where
  trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*s.sizes.trapdoor)
  distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
    (do let salts ← sampleCompleteSaltTape
        let leaves := fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts
        pure (transcriptHeap false oracle.compression leaves 1, trapdoorOf oracle message salts))
  nonce : ∀ oracle message salts index,
    trapdoorSalt (s := s) (trapdoorOf oracle message salts) index = salts index
  heap : ∀ oracle message salts node, 0 < node → node < 2*LENGTH →
    trapdoorHeap (s := s) (trapdoorOf oracle message salts) node =
      transcriptHeap false oracle.compression
        (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) node

/-- Composition of the exact machine opener with the commit-side distribution
and trapdoor representation yields the challenge's executable transcript premise. -/
theorem transcript_refines (s : Submission) (abi : OpeningABI s)
    (committed : CommitTranscript s) : TranscriptRefines s.scheme (transcriptBuilder false) := by
  intro oracle message positions
  unfold executableTranscript
  rw [fixed_oracle_run_bind]
  apply ((committed.distribution oracle message).bind_left _).trans
  simp only [bind_assoc, pure_bind]
  apply EvalDistEq.bind_right
  intro salts
  rw [scheme_open_bytes s abi, pure_bind, fixed_oracle_run_pure]
  have proof := proof_from_trapdoor_matches s (committed.trapdoorOf oracle message salts) positions
    oracle.compression (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
    salts (committed.heap oracle message salts) (committed.nonce oracle message salts)
  rw [proof]
  rfl

/-- The real commitment RNG returns one packed tape. This constructor transports
that distribution once and leaves the executable commit proof in its native form. -/
noncomputable def CommitTranscript.ofPacked (s : Submission)
    (trapdoorOf : Oracle → Message → CompleteSaltTape → BitVec (8*s.sizes.trapdoor))
    (distribution : ∀ oracle message, fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let packed ← $ᵗ BitVec (128 * LENGTH)
          let salts := splitBlocks 128 LENGTH packed
          let leaves := fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts
          pure (transcriptHeap false oracle.compression leaves 1, trapdoorOf oracle message salts)))
    (nonce : ∀ oracle message salts index,
      trapdoorSalt (s := s) (trapdoorOf oracle message salts) index = salts index)
    (heap : ∀ oracle message salts node, 0 < node → node < 2*LENGTH →
      trapdoorHeap (s := s) (trapdoorOf oracle message salts) node =
        transcriptHeap false oracle.compression
          (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) node) :
    CommitTranscript s :=
  ⟨trapdoorOf, fun oracle message =>
    (distribution oracle message).trans
      (packed_salt_tape_uniform (fun salts => pure
        (transcriptHeap false oracle.compression
          (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) 1,
         trapdoorOf oracle message salts))), nonce, heap⟩

theorem scheme_hiding (s : Submission) (abi : OpeningABI s) (committed : CommitTranscript s) :
    s.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ) + 1) / 2 ^ 120)) :=
  scheme_hiding_of_transcript _ _ (transcript_refines s abi committed)

end TwoPermutationPrototype.Opening
