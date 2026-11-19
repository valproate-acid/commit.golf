import CommitGolfCandidate.InputMemory

namespace TwoPermutationPrototype.QOpening
set_option maxRecDepth 100000
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64

def markBase : Nat := 4096
def trapdoorBase : Nat := 4096 + 256 * LENGTH + 32
/-- Quad leaf groups: leaf `i`'s digest is at `groupBase + 368 (i / 4) + 32 (i % 4)` (QuadSpec `quadSlotOffset`). -/
def groupBase : Nat := trapdoorBase + 268439552
def trapdoorBytes : Nat := 2080378880
def nonceBase : Nat := trapdoorBase + 1811943424
def indicesBase : Nat := trapdoorBase + trapdoorBytes
def proofBase : Nat := indicesBase + 8 * LENGTH + 64 + 256 * LENGTH
def proofCapacity : Nat := 534 * LENGTH + 8192

structure OpeningLayout (s : Submission) : Prop where
  trapdoor : s.layout.trapdoor = trapdoorBase
  trapdoorSize : s.sizes.trapdoor = trapdoorBytes
  indices : s.layout.indices = indicesBase
  proof : s.layout.proof = proofBase

private theorem index_word (index : Index) :
    BitVec.ofNat 64 (∑ j ∈ Finset.range 8,
      (BitVec.ofNat 8 (index.val / 2 ^ (8 * j))).toNat * 2 ^ (8 * j)) =
      BitVec.ofNat 64 index.val := by
  congr 1
  have bounded : index.val < 16777216 := index.isLt
  norm_num [Finset.sum_range_succ, BitVec.toNat_ofNat]
  omega

/-- The ABI's ordinal is the offset in the sorted set. The nonce is subsequently
addressed by the position value, independently of that ordinal. -/
theorem input_index (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (ordinal : Nat) (bounded : ordinal < positions.card) :
    (s.initialState .opening (trapdoor, positions)).getMem
      (BitVec.ofNat 64 (indicesBase + 8 * ordinal)) =
      BitVec.ofNat 64 ((positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)).val := by
  have cardinal : positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ positions
  erw [initial_input_word s .opening (trapdoor, positions) _ (by
    norm_num [indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH] at cardinal ⊢
    omega)]
  have bytes (j : Nat) (hj : j < 8) :
      inputByte s .opening (trapdoor, positions) (indicesBase + 8 * ordinal + j) =
        BitVec.ofNat 8 (((positions.sort (· ≤ ·))[ordinal]'(by simpa using bounded)).val /
          2 ^ (8 * j)) := by
    have before : ¬ (trapdoorBase ≤ indicesBase + 8 * ordinal + j ∧
        indicesBase + 8 * ordinal + j < trapdoorBase + (8 * trapdoorBytes + 7) / 8) := by
      norm_num [indicesBase, trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH]
      omega
    have inside : indicesBase ≤ indicesBase + 8 * ordinal + j ∧
        indicesBase + 8 * ordinal + j <
          indicesBase + 8 * (positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]
      omega
    have quotient : (indicesBase + 8 * ordinal + j - indicesBase) / 8 = ordinal := by omega
    have remainder : (indicesBase + 8 * ordinal + j - indicesBase) % 8 = j := by omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      layout.trapdoor, layout.trapdoorSize, layout.indices, before, inside, decide_false,
      and_true, decide_true]
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using bounded)]
  refine (congrArg (BitVec.ofNat 64) (Finset.sum_congr rfl fun j hj => ?_)).trans (index_word _)
  rw [bytes j (Finset.mem_range.mp hj)]

/-- Any slice within the serialized private state can be read at its exact offset. -/
theorem input_trapdoor_slice (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (offset bytes : Nat) (inside : offset + bytes ≤ trapdoorBytes) :
    readBuffer (s.initialState .opening (trapdoor, positions)) (trapdoorBase + offset) bytes =
      trapdoor.extractLsb' (8 * offset) (8 * bytes) := by
  apply read_serialized_slice
  intro j hj
  have bound : trapdoorBase + offset + j < 2 ^ 64 := by
    norm_num [trapdoorBase, trapdoorBytes, LENGTH, LOG_LENGTH] at inside ⊢
    omega
  erw [initial_input_byte s .opening (trapdoor, positions) _ bound]
  have covered : trapdoorBase ≤ trapdoorBase + offset + j ∧
      trapdoorBase + offset + j < trapdoorBase + (8 * trapdoorBytes + 7) / 8 := by omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    layout.trapdoor, layout.trapdoorSize, covered, and_true, decide_true]
  rw [show trapdoorBase + offset + j - trapdoorBase = offset + j by omega]

/-- Sixteen bytes at a leaf's original vector index recover that leaf's nonce. -/
theorem input_nonce (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) (index : Index) :
    readBuffer (s.initialState .opening (trapdoor, positions)) (nonceBase + 16 * index.val) 16 =
      trapdoor.extractLsb' (8 * (0x6C001000 + 16 * index.val)) 128 := by
  have address : nonceBase + 16 * index.val = trapdoorBase + (0x6C001000 + 16 * index.val) := by
    unfold nonceBase; omega
  have slice := input_trapdoor_slice s layout trapdoor positions (0x6C001000 + 16 * index.val) 16 (by
    have bounded := index.isLt
    have size : LENGTH = 16777216 := rfl
    unfold trapdoorBytes
    omega)
  refine Eq.trans ?_ slice
  rw [address]

/-- The entire heap occupies 64N bytes, before the leaf groups and the nonce region. -/
theorem input_digest (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (node : Nat) (bounded : node < 2 * LENGTH) :
    readBuffer (s.initialState .opening (trapdoor, positions)) (trapdoorBase + 32 * node) 32 =
      trapdoor.extractLsb' (256 * node) 256 := by
  have offset : 8 * (32 * node) = 256 * node := by omega
  rw [← offset]
  exact input_trapdoor_slice s layout trapdoor positions _ _ (by
    have size : LENGTH = 16777216 := rfl
    unfold trapdoorBytes; omega)

/-- Leaf `4 (index / 4) + k`'s digest slot inside its quad group. -/
theorem input_leaf (s : Submission) (layout : OpeningLayout s)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions)
    (index : Index) (k : Nat) (slot : k < 4) :
    readBuffer (s.initialState .opening (trapdoor, positions))
        (groupBase + 368 * (index.val / 4) + 32 * k) 32 =
      trapdoor.extractLsb' (8 * (0x10001000 + (368 * (index.val / 4) + 32 * k))) 256 := by
  have address : groupBase + 368 * (index.val / 4) + 32 * k =
      trapdoorBase + (0x10001000 + (368 * (index.val / 4) + 32 * k)) := by
    unfold groupBase; omega
  have slice := input_trapdoor_slice s layout trapdoor positions
      (0x10001000 + (368 * (index.val / 4) + 32 * k)) 32 (by
    have bounded := index.isLt
    have size : LENGTH = 16777216 := rfl
    unfold trapdoorBytes
    omega)
  refine Eq.trans ?_ slice
  rw [address]

end TwoPermutationPrototype.QOpening
