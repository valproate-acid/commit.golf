import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.QuadNonceSpec

/-! Shared interface for the full 5-ary permutation tree ("penta" design).

Leaves are the unchanged pinned two-permutation leaf digests (256 bits). Every internal node is one
permutation call on `pentaInput c = 0^320 || c0 || c1 || c2 || c3 || c4` (low bits first: 40 zero
bytes, then five 32-byte children); the node is the low 256 bits of the reply. Domain D5 = blocks
whose low 320 bits are zero. Level 0 has `LENGTH` nodes (the leaves); level `k+1` has
`pentaCount (k+1) = ⌈pentaCount k / 5⌉` nodes, node `j` over level-`k` nodes `5j … 5j+4`, where
nodes beyond `pentaCount k` count as 0 (ragged last groups). Level 11 has one node, the root
(= the commitment). No compression function and no binary tree are used.

Proof record per opened position `i` (1424 bytes): salt (16) ++ for each level `k = 0 … 10`, the four
other children of the level-`k+1` node above `i` in rotation order `r+1, r+2, r+3, r+4 (mod 5)`,
`r = (i / 5^k) % 5` (4 × 32 each). Records in ascending position order; no footer. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate OracleComp
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)

def PENTA_LEVELS : Nat := 11

/-- Nodes at level `k`: 16777216, 3355444, 671089, 134218, 26844, 5369, 1074, 215, 43, 9, 2, 1. -/
def pentaCount : Nat → Nat
  | 0 => LENGTH
  | k + 1 => (pentaCount k + 4) / 5

theorem penta_count_values :
    (List.range 12).map pentaCount =
      [16777216, 3355444, 671089, 134218, 26844, 5369, 1074, 215, 43, 9, 2, 1] := by decide

/-- Permutation block of a 5-ary node: low 320 bits zero, then child 0, 1, 2, 3, 4. -/
def pentaInput (c : Fin 5 → BitVec 256) : Block :=
  ((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) ++ (0#320)

abbrev PentaFunction := (Fin 5 → BitVec 256) → BitVec 256

def pentaFunction (perm : Block → Block) : PentaFunction :=
  fun c => (perm (pentaInput c)).extractLsb' 0 256

/-- Node `j` of level `k` (0 beyond `pentaCount k`). -/
def pentaNode (penta : PentaFunction) (leaves : DigestTape) : Nat → Nat → BitVec 256
  | 0, j => if h : j < LENGTH then leaves ⟨j, h⟩ else 0
  | k + 1, j => if j < pentaCount (k + 1) then penta (fun t => pentaNode penta leaves k (5 * j + t.val)) else 0

/-- Children of node `j` of level `k+1`: level-`k` nodes `5j … 5j+4`. -/
def pentaGroup (penta : PentaFunction) (leaves : DigestTape) (k j : Nat) : Fin 5 → BitVec 256 :=
  fun t => pentaNode penta leaves k (5 * j + t.val)

theorem penta_node_succ (penta : PentaFunction) (leaves : DigestTape) (k j : Nat)
    (inside : j < pentaCount (k + 1)) :
    pentaNode penta leaves (k + 1) j = penta (pentaGroup penta leaves k j) := by
  rw [pentaNode, if_pos inside]
  rfl

def pentaRoot (penta : PentaFunction) (leaves : DigestTape) : BitVec 256 :=
  pentaNode penta leaves PENTA_LEVELS 0

/-- Slot of the `j`-th (`j < 4`) other child at level `k` in the record. -/
def pentaRot (index : Index) (k j : Nat) : Fin 5 :=
  ⟨(index.val / 5 ^ k % 5 + j + 1) % 5, Nat.mod_lt _ (by decide)⟩

/-- Level-`k` node index of the `j`-th other child at level `k` for `index`. -/
def pentaNeighbour (index : Index) (k j : Nat) : Nat := 5 * (index.val / 5 ^ (k + 1)) + (pentaRot index k j).val

def pentaRecord (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) : List Byte :=
  saltBytes salt ++
  (List.range PENTA_LEVELS).flatMap fun k =>
    (List.range 4).flatMap fun j => digestBytes (pentaNode penta leaves k (pentaNeighbour index k j))

abbrev PentaTranscriptBuilder :=
  PentaFunction → (positions : Positions) → OpenedSalts positions → DigestTape → Commitment × Proof

def pentaTranscriptBuilder : PentaTranscriptBuilder :=
  fun penta positions salts leaves =>
    let ordered := positions.attach.sort (fun i j => i.val ≤ j.val)
    (pentaRoot penta leaves, ordered.flatMap (fun index => pentaRecord penta leaves index.val (salts index)))

theorem penta_record_length (penta : PentaFunction) (leaves : DigestTape) (index : Index) (salt : BitVec 128) :
    (pentaRecord penta leaves index salt).length = 1424 := by
  have inner : ∀ k, ((List.range 4).flatMap fun j =>
      digestBytes (pentaNode penta leaves k (pentaNeighbour index k j))).length = 128 := by
    intro k
    simp only [List.length_flatMap, digestBytes, List.length_ofFn, List.map_const', List.length_range,
      List.sum_replicate, smul_eq_mul]
  unfold pentaRecord saltBytes
  simp only [List.length_append, List.length_ofFn, List.length_flatMap, inner, List.map_const',
    List.length_range, List.sum_replicate, smul_eq_mul, PENTA_LEVELS]

/-- Honest view: same leaf digests as 8d2a211; every internal node queries the same permutation. -/
def pentaHonestView (build : PentaTranscriptBuilder) (p : BiPermutation Block)
    (message : Message) (positions : Positions) (salts : CompleteSaltTape) : Commitment × Proof :=
  build (pentaFunction p.forward) positions (fun index => salts index.val) (pinnedFullLeafDigests p message salts)

/-- Executable commit-and-open transcript = penta honest view with nonce-chain salts. -/
def PentaNonceTranscriptRefines (scheme : Scheme) (build : PentaTranscriptBuilder) : Prop :=
  ∀ (oracle : Oracle) (message : Message) (positions : Positions),
    fixedOracleRun oracle (executableTranscript scheme message positions) =ᵈ
      (do let k ← $ᵗ Key
          pure (pentaHonestView build (BiPermutation.equiv Block oracle.permutation)
            message positions (actualNonces oracle.permutation k)))

/-- The builder reads the node function only on the honest inputs of levels `1 … 11`. -/
def PentaBuildLocal (build : PentaTranscriptBuilder) : Prop :=
  ∀ (penta penta' : PentaFunction) (positions : Positions) (salts : OpenedSalts positions) (leaves : DigestTape),
    (∀ k j, k < PENTA_LEVELS → j < pentaCount (k + 1) →
      penta (pentaGroup penta leaves k j) = penta' (pentaGroup penta leaves k j)) →
      build penta positions salts leaves = build penta' positions salts leaves

theorem penta_node_congr (penta penta' : PentaFunction) (leaves : DigestTape)
    (same : ∀ k j, k < PENTA_LEVELS → j < pentaCount (k + 1) →
      penta (pentaGroup penta leaves k j) = penta' (pentaGroup penta leaves k j)) :
    ∀ k, k ≤ PENTA_LEVELS → ∀ j, pentaNode penta leaves k j = pentaNode penta' leaves k j := by
  intro k
  induction k with
  | zero => intro _ j; rfl
  | succ k ih =>
    intro le j
    rw [pentaNode, pentaNode]
    split_ifs with inside
    · have children : (fun t : Fin 5 => pentaNode penta leaves k (5 * j + t.val)) =
          (fun t : Fin 5 => pentaNode penta' leaves k (5 * j + t.val)) := by
        funext t; exact ih (by omega) _
      have h := same k j (by omega) inside
      unfold pentaGroup at h
      rw [h, children]
    · rfl

theorem penta_transcript_builder_local : PentaBuildLocal pentaTranscriptBuilder := by
  intro penta penta' positions salts leaves same
  have nodes := penta_node_congr penta penta' leaves same
  have root : pentaRoot penta leaves = pentaRoot penta' leaves := nodes _ le_rfl _
  have record : ∀ index salt, pentaRecord penta leaves index salt = pentaRecord penta' leaves index salt := by
    intro index salt
    unfold pentaRecord
    congr 1
    apply List.flatMap_congr
    intro k member
    apply List.flatMap_congr
    intro j _
    rw [nodes k (le_of_lt (List.mem_range.mp member))]
  simp only [pentaTranscriptBuilder, root, record]

/-! ### Trapdoor layout (interface between the commit image and the opening image)
Byte offsets from the trapdoor base (the trapdoor size, salts and buffer layout are exactly those
of the quad base: size `QUAD_TRAPDOOR_BYTES = 2080378880`, salts at `QUAD_SALT_BASE + 16 i`):
* level-`k` groups (`k = 0 … 11`) from `pentaGroupBase k` (each `+ 40` is 4096-aligned, one `lui`):
  group `g` at `pentaGroupBase k + 368 g`, 40 zero bytes, then slots `t = 0 … 4` at `+40 + 32 t`;
  level-`k` node `j` sits in slot `j % 5` of group `j / 5` (`pentaSlotOffset k j`). Level 0 holds
  the leaf digests (each leaf's 200-byte second reply is written from its slot), level 11 holds the
  root in slot 0 of its only group. Writes are ascending within a level, so each 200-byte reply only
  overwrites later slots of its own group or ends exactly at the next group.
* ragged slots (slots `j ≥ pentaCount k` of the last level-`k` group, `k ≤ 10`) are zero in the
  trapdoor: the commit clears them after the level is written.
* all groups end at offset 0x5C012148 < `QUAD_SALT_BASE - 176`.
Layout: message 4096, commitment 4294971392, trapdoor 4294971424, indices 6375350304,
values 6509568096, proof 10804535392 (as in the quad base); proof capacity `1424 · LENGTH`. -/
def pentaGroupBase : Nat → Nat
  | 0 => 4056 | 1 => 1234812888 | 2 => 1481781208 | 3 => 1531178968 | 4 => 1541062616
  | 5 => 1543045080 | 6 => 1543446488 | 7 => 1543532504 | 8 => 1543552984 | 9 => 1543561176
  | 10 => 1543569368 | _ => 1543577560

def pentaSlotOffset (k j : Nat) : Nat := pentaGroupBase k + 368 * (j / 5) + 40 + 32 * (j % 5)

def PENTA_PROOF_CAPACITY : Nat := 1424 * LENGTH

theorem penta_proof_capacity_value : PENTA_PROOF_CAPACITY = 23890755584 := rfl

/-- Consecutive level regions do not overlap, and all lie below the salt area. -/
theorem penta_levels_separate :
    (∀ k, k < 11 → pentaGroupBase k + 368 * pentaCount (k + 1) ≤ pentaGroupBase (k + 1)) ∧
    pentaGroupBase 11 + 368 ≤ QUAD_SALT_BASE - 176 := by
  refine ⟨?_, by decide⟩
  intro k lt
  interval_cases k <;> decide

def pentaTrapdoorNode {n : Nat} (trapdoor : BitVec n) (k j : Nat) : BitVec 256 :=
  trapdoor.extractLsb' (8 * pentaSlotOffset k j) 256

def pentaPublicNodes (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) : Nat → Nat → BitVec 256 :=
  pentaNode (pentaFunction oracle.permutation) (quadPublicLeaves oracle message salts)

/-- What the commit side delivers to the opening side (penta + NonceChain). -/
structure PentaNonceCommitTranscript (s : Submission) where
  trapdoor : Oracle → Message → Key → BitVec (8 * s.sizes.trapdoor)
  distribution : ∀ oracle message,
    fixedOracleRun oracle (s.scheme.commit message) =ᵈ
      (do let k ← $ᵗ Key
          pure (pentaPublicNodes oracle message (actualNonces oracle.permutation k) PENTA_LEVELS 0,
            trapdoor oracle message k))
  nonce : ∀ oracle message k index,
    quadTrapdoorSalt (trapdoor oracle message k) index = actualNonces oracle.permutation k index
  /-- Every slot of levels `0 … 10` that a record can name (in-range nodes and ragged zeros). -/
  node : ∀ oracle message k level j, level < PENTA_LEVELS → j < 5 * pentaCount (level + 1) →
    pentaTrapdoorNode (trapdoor oracle message k) level j =
      pentaPublicNodes oracle message (actualNonces oracle.permutation k) level j

end TwoPermutationPrototype.Sampling
