import CommitGolfCandidate.TwoPermutationHidingBridge

/-! Pure transcript for the two-permutation image. The reference heap stores
the exact leaf digests; only internal digests are projected in packed mode. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate

def projectInternal (packed : Bool) (compress : Compression) : Compression :=
  fun input =>
    if packed then (0#16) ++ (compress input).extractLsb' 0 240 else compress input

def transcriptHeap (packed : Bool) (compress : Compression) (leaves : DigestTape) : Nat → BitVec 256 :=
  referenceHeap (projectInternal packed compress) LENGTH
    (fun index => if inside : index < LENGTH then leaves ⟨index, inside⟩ else 0)

theorem transcript_heap_leaf (packed : Bool) (compress : Compression) (leaves : DigestTape) (index : Index) :
    transcriptHeap packed compress leaves (LENGTH + index.val) = leaves index := by
  unfold transcriptHeap
  rw [reference_heap_leaf _ _ _ _ index.isLt]
  exact dite_eq_left index.isLt

theorem transcript_heap_parent (packed : Bool) (compress : Compression) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (branch : node < LENGTH) :
    transcriptHeap packed compress leaves node =
      projectInternal packed compress
        (transcriptHeap packed compress leaves (2 * node + 1) ++ transcriptHeap packed compress leaves (2 * node)) := by
  unfold transcriptHeap
  exact reference_heap_parent _ _ _ _ positive branch

def saltBytes (salt : BitVec 128) : List Byte :=
  List.ofFn fun i : Fin 16 => salt.extractLsb' (8 * i.val) 8

def proofDigestBytes (packed : Bool) (digest : BitVec 256) : List Byte :=
  if packed then (digestBytes digest).take 30 else digestBytes digest

def lowerRecord (packed : Bool) (heap : Nat → BitVec 256) (index : Index)
    (salt : BitVec 128) : List Byte :=
  saltBytes salt ++ (List.range 16).flatMap fun level =>
    proofDigestBytes (packed && level != 0) (heap (((LENGTH + index.val) / 2 ^ level) ^^^ 1))

def capGroup (index : Index) : Nat := (LENGTH + index.val) / 2 ^ 16

def capIsMarked (groups : List Nat) (node height : Nat) : Bool :=
  groups.any (fun group => group / 2 ^ height == node)

def capFrontierNodes (groups : List Nat) (node : Nat) : Nat → List Nat
  | 0 => if capIsMarked groups node 0 then [] else [node]
  | height + 1 =>
    if capIsMarked groups node (height + 1) then
      capFrontierNodes groups (2 * node) height ++ capFrontierNodes groups (2 * node + 1) height
    else [node]

def frontierProof (packed : Bool) (heap : Nat → BitVec 256) (groups : List Nat) : Proof :=
  if groups.isEmpty then []
  else (capFrontierNodes groups 1 8).flatMap (fun node => proofDigestBytes packed (heap node))

def transcriptBuilder (packed : Bool) : TranscriptBuilder :=
  fun compress positions salts leaves =>
    let heap := transcriptHeap packed compress leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let path := ordered.flatMap (fun index => lowerRecord packed heap index.val (salts index))
    let footer := frontierProof packed heap (ordered.map (capGroup ∘ Subtype.val))
    (heap 1, path ++ footer)

theorem proof_digest_length (packed : Bool) (digest : BitVec 256) :
    (proofDigestBytes packed digest).length = if packed then 30 else 32 := by
  cases packed <;> simp [proofDigestBytes, digestBytes]

theorem lower_record_length (packed : Bool) (heap : Nat → BitVec 256) (index : Index) (salt : BitVec 128) :
    (lowerRecord packed heap index salt).length = if packed then 498 else 528 := by
  unfold lowerRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap]
  cases packed <;> simp [proof_digest_length, List.range_succ]


theorem cap_marked_children (groups : List Nat) (node height : Nat) :
    capIsMarked groups node (height + 1) =
      (capIsMarked groups (2 * node) height || capIsMarked groups (2 * node + 1) height) := by
  apply Bool.eq_iff_iff.mpr
  simp only [capIsMarked, List.any_eq_true, beq_iff_eq, Bool.or_eq_true]
  have parent (group : Nat) : group / 2 ^ (height + 1) = (group / 2 ^ height) / 2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  constructor
  · rintro ⟨group, belongs, mark⟩
    rw [parent] at mark
    have child : group / 2 ^ height = 2 * node ∨ group / 2 ^ height = 2 * node + 1 := by omega
    exact child.imp (fun both => ⟨group, belongs, both⟩) (fun both => ⟨group, belongs, both⟩)
  · rintro (⟨group, belongs, mark⟩ | ⟨group, belongs, mark⟩)
    · exact ⟨group, belongs, (parent group).trans (by omega)⟩
    · exact ⟨group, belongs, (parent group).trans (by omega)⟩

def capMarkTree (groups : List Nat) (node : Nat) : (height : Nat) → CapMarks height
  | 0 => .leaf (capIsMarked groups node 0)
  | height + 1 => .node (capMarkTree groups (2 * node) height) (capMarkTree groups (2 * node + 1) height)

theorem cap_tree_occupied (groups : List Nat) (node height : Nat) :
    (capMarkTree groups node height).occupied = capIsMarked groups node height := by
  induction height generalizing node with
  | zero => rfl
  | succ height ih =>
    simp only [capMarkTree, CapMarks.occupied, ih, ← cap_marked_children]

theorem cap_frontier_length (groups : List Nat) (node height : Nat) :
    (capFrontierNodes groups node height).length = (capMarkTree groups node height).boundary := by
  induction height generalizing node with
  | zero =>
    cases mark : capIsMarked groups node 0 <;> simp [capFrontierNodes, capMarkTree, CapMarks.boundary, CapMarks.occupied, mark]
  | succ height ih =>
    rw [capFrontierNodes, capMarkTree, CapMarks.boundary, ← capMarkTree, cap_tree_occupied]
    split <;> simp_all

theorem frontier_proof_bound (packed : Bool) (heap : Nat → BitVec 256) (groups : List Nat) :
    (frontierProof packed heap groups).length ≤ (if packed then 30 else 32) * 128 := by
  unfold frontierProof
  split
  · simp
  · have count := (cap_frontier_length groups 1 8).trans_le (production_boundary_bound (capMarkTree groups 1 8))
    simp only [List.length_flatMap]
    cases packed <;> simp [proof_digest_length] <;> omega

/-- The worst-case bound for the pure opening transcript at the scored size. -/
theorem transcript_128_size (packed : Bool) (compress : Compression) (positions : Positions)
    (salts : OpenedSalts positions) (leaves : DigestTape) (count : positions.card = 128) :
    (transcriptBuilder packed compress positions salts leaves).2.length ≤ if packed then 67584 else 71680 := by
  let sorted := positions.attach.sort (fun i j => i.val ≤ j.val)
  let heap := transcriptHeap packed compress leaves
  have countProof := frontier_proof_bound packed heap (sorted.map (capGroup ∘ Subtype.val))
  have ordered : sorted.length = 128 := by simp [sorted, count]
  change ((sorted.flatMap (fun index => lowerRecord packed heap index.val (salts index))) ++
    frontierProof packed heap (sorted.map (capGroup ∘ Subtype.val))).length ≤ _
  simp only [List.length_append, List.length_flatMap]
  cases packed <;> simp [Function.comp_def, lower_record_length, ordered] at countProof ⊢ <;> omega

end TwoPermutationPrototype.Sampling
