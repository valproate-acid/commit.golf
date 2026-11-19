import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationTranscript

/-! Shared interface for the 4-ary permutation bottom node ("quad" design, option A).

Tree: leaves `0 … LENGTH-1` are the unchanged 8d2a211 pinned (position-tagged) two-permutation leaf digests `pinnedFullLeafDigests` (256 bits).
Leaves `4g … 4g+3` feed one quad node: the permutation block is 72 zero bytes followed by the
four 32-byte leaf digests (bytes 72..199, little-endian, leaf `4g` first); the node value is the
low 256 bits (bytes 0..31) of the permutation reply, untruncated. Quad nodes sit at heap indices
`[LENGTH/4, LENGTH/2)` (index `LENGTH/4 + g`); heap indices `[1, LENGTH/4)` are the binary
compression nodes with 240-bit projection exactly as in 8d2a211; the frontier is unchanged.

Proof record per opened position (534 bytes): salt (16) ++ the three other leaf digests of the
quad group in ROTATION order: slots r+1, r+2, r+3 (mod 4) where r = index % 4 (3 × 32) ++ the sibling quad node (32, untruncated) ++ the
binary siblings at heights 3..15 (13 × 30). The 30-byte frontier footer is unchanged. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate

theorem length_value : LENGTH = 16777216 := rfl

/-- Permutation block of a quad node: low 576 bits zero, then child 0, 1, 2, 3. -/
def quadInput (c : Fin 4 → BitVec 256) : Block :=
  (((c 3 ++ c 2) ++ c 1) ++ c 0) ++ (0#576)

abbrev QuadFunction := (Fin 4 → BitVec 256) → BitVec 256

def quadFunction (perm : Block → Block) : QuadFunction :=
  fun c => (perm (quadInput c)).extractLsb' 0 256

/-- Leaf `4 * (index / 4) + k` of the quad group containing `index`. -/
def quadLeaf (leaves : DigestTape) (index : Index) (k : Fin 4) : BitVec 256 :=
  leaves ⟨4 * (index.val / 4) + k.val, by
    have h1 := index.isLt; have h2 := k.isLt; have h3 : LENGTH = 16777216 := rfl; omega⟩

def quadGroupLeaves (leaves : DigestTape) (g : Nat) : Fin 4 → BitVec 256 :=
  fun k => if inside : 4 * g + k.val < LENGTH then leaves ⟨4 * g + k.val, inside⟩ else 0

def quadHeap (compress : Compression) (quad : QuadFunction) (leaves : DigestTape) : Nat → BitVec 256 :=
  referenceHeap (projectInternal true compress) (LENGTH / 4) (fun g => quad (quadGroupLeaves leaves g))

/-- Slot of the `j`-th other leaf in the record: rotation order `r+1, r+2, r+3 (mod 4)`, `r = index % 4`. -/
def quadRotSlot (index : Index) (j : Nat) : Fin 4 := ⟨(index.val % 4 + j + 1) % 4, Nat.mod_lt _ (by decide)⟩

def quadLowerRecord (heap : Nat → BitVec 256) (leaves : DigestTape) (index : Index)
    (salt : BitVec 128) : List Byte :=
  saltBytes salt ++
  (List.range 3).flatMap (fun j => digestBytes (quadLeaf leaves index (quadRotSlot index j))) ++
  proofDigestBytes false (heap (((LENGTH + index.val) / 4) ^^^ 1)) ++
  (List.range 13).flatMap fun j =>
    proofDigestBytes true (heap (((LENGTH + index.val) / 2 ^ (j + 3)) ^^^ 1))

abbrev QuadTranscriptBuilder :=
  Compression → QuadFunction → (positions : Positions) → OpenedSalts positions → DigestTape →
    Commitment × Proof

def quadTranscriptBuilder : QuadTranscriptBuilder :=
  fun compress quad positions salts leaves =>
    let heap := quadHeap compress quad leaves
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    let path := ordered.flatMap (fun index => quadLowerRecord heap leaves index.val (salts index))
    let footer := frontierProof true heap (ordered.map (capGroup ∘ Subtype.val))
    (heap 1, path ++ footer)

/-- Honest view: same leaf digests as 8d2a211; the quad layer queries the same permutation. -/
def quadHonestView (build : QuadTranscriptBuilder) (compress : Compression) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build compress (quadFunction p.forward) positions (fun index => salts index.val)
    (pinnedFullLeafDigests p message salts)

def QuadTranscriptRefines (scheme : Scheme) (build : QuadTranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          pure (quadHonestView build oracle.compression (BiPermutation.equiv Block oracle.permutation)
            message positions salts))

theorem quad_lower_record_length (heap : Nat → BitVec 256) (leaves : DigestTape) (index : Index)
    (salt : BitVec 128) : (quadLowerRecord heap leaves index salt).length = 534 := by
  unfold quadLowerRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, proof_digest_length]
  simp [digestBytes, List.range_succ]

theorem quad_heap_node (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (g : Nat) (inside : g < LENGTH / 4) :
    quadHeap compress quad leaves (LENGTH / 4 + g) = quad (quadGroupLeaves leaves g) := by
  unfold quadHeap
  rw [referenceHeap]
  have notBranch : ¬ (0 < LENGTH / 4 + g ∧ LENGTH / 4 + g < LENGTH / 4) := by omega
  have leafRange : LENGTH / 4 ≤ LENGTH / 4 + g ∧ LENGTH / 4 + g < 2 * (LENGTH / 4) := by omega
  simp only [notBranch, leafRange, dite_false, if_true, and_self, Nat.add_sub_cancel_left]

theorem quad_heap_parent (compress : Compression) (quad : QuadFunction) (leaves : DigestTape)
    (node : Nat) (positive : 0 < node) (branch : node < LENGTH / 4) :
    quadHeap compress quad leaves node =
      projectInternal true compress
        (quadHeap compress quad leaves (2 * node + 1) ++ quadHeap compress quad leaves (2 * node)) := by
  unfold quadHeap
  exact reference_heap_parent _ _ _ _ positive branch

/-! ### Trapdoor layout (interface between the commit image and the opening image)
Byte offsets from the trapdoor base:
* `[0, 2^28)`: heap, node `k ∈ [1, LENGTH/2)` at `32 k` (quad nodes at `k ∈ [LENGTH/4, LENGTH/2)`);
  `[2^28, QUAD_GROUP_BASE)` absorbs the 168-byte overflow of the last (ascending) quad-node write.
* leaf groups from `QUAD_GROUP_BASE = 2^28 + 4096 - 72` (so `QUAD_GROUP_BASE + 72 = 0x10001000` is one `lui`): group `g` at `QUAD_GROUP_BASE + 368 g`, 72 zero
  bytes (never written) then leaf slots `k = 0..3` at `+72 + 32 k` (each leaf's second reply writes
  200 bytes from its slot; the last slot's write ends exactly at the next group).
* salts from `QUAD_SALT_BASE = 0x6C001000` (one `lui`; 72 bytes above the last group), 16 bytes per leaf (bulk RANDOM).
Layout: message 4096, commitment 4294971392, trapdoor 4294971424, indices = trapdoor + QUAD_TRAPDOOR_BYTES,
values = indices + 2^27 + 64, proof = values + 2^32 (same gaps after the trapdoor as 880e477/8d2a211). -/
def QUAD_GROUP_BASE : Nat := 2 ^ 28 + 4096 - 72
def quadSlotOffset (i : Nat) : Nat := QUAD_GROUP_BASE + 368 * (i / 4) + 72 + 32 * (i % 4)
def QUAD_SALT_BASE : Nat := 0x6C001000
def QUAD_TRAPDOOR_BYTES : Nat := QUAD_SALT_BASE + 16 * LENGTH

theorem quad_trapdoor_bytes_value : QUAD_TRAPDOOR_BYTES = 2080378880 := rfl

theorem quad_groups_below_salts : QUAD_GROUP_BASE + 368 * (LENGTH / 4) ≤ QUAD_SALT_BASE := by decide

def quadTrapdoorHeap {n : Nat} (trapdoor : BitVec n) (node : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (256 * node) 256
def quadTrapdoorLeaf {n : Nat} (trapdoor : BitVec n) (index : Index) : BitVec 256 :=
  trapdoor.extractLsb' (8 * quadSlotOffset index.val) 256
def quadTrapdoorSalt {n : Nat} (trapdoor : BitVec n) (index : Index) : BitVec 128 :=
  trapdoor.extractLsb' (8 * (QUAD_SALT_BASE + 16 * index.val)) 128

def quadPublicLeaves (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : DigestTape :=
  pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts

def quadPublicTree (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → BitVec 256 :=
  quadHeap oracle.compression (quadFunction oracle.permutation) (quadPublicLeaves oracle message salts)

/-- What the commit side (worker W3) delivers to the opening side (lead). -/
structure QuadCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → CompleteSaltTape → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let salts ← sampleCompleteSaltTape
          pure (quadPublicTree oracle message salts 1, trapdoor oracle message salts))
  nonce : ∀ oracle message salts index, quadTrapdoorSalt (trapdoor oracle message salts) index = salts index
  leaf : ∀ oracle message salts index,
    quadTrapdoorLeaf (trapdoor oracle message salts) index = quadPublicLeaves oracle message salts index
  heap : ∀ oracle message salts node, 0 < node → node < LENGTH / 2 →
    quadTrapdoorHeap (trapdoor oracle message salts) node = quadPublicTree oracle message salts node

end TwoPermutationPrototype.Sampling
