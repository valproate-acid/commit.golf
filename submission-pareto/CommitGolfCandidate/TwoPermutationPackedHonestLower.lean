import CommitGolfCandidate.TwoPermutationPackedCheckRecordData

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate CommitGolfCandidate.ShortTree RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
open TwoPermutationPrototype.PackedHonest (honestHeap honest_projected_node)
set_option maxRecDepth 8192

def lowerWireSibling (state : MachineState) (ordinal level : Nat) : Digest :=
  if level = 0 then readBuffer state (checkProofByte ordinal+16) 32
  else 0#16 ++ readBuffer state (checkProofByte ordinal+48+30*(level-1)) 30

private theorem later_sibling_internal (index : Index) (level : Nat) (later : 0 < level) (within : level < 16) :
    0 < Opening.lowerNode index level ^^^ 1 ∧ Opening.lowerNode index level ^^^ 1 < LENGTH := by
  let node := Opening.lowerNode index level
  have bounded := index.isLt
  have scale : 2 ≤ (2:Nat)^level := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show 1 ≤ level by omega)
  have scaleBound : (2:Nat)^level ≤ 32768 :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show level ≤ 15 by omega)).trans (by decide)
  have lo : 2 ≤ node := by
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < (2:Nat)^level)).mpr
    change 2*2^level ≤ 16777216+index.val
    omega
  have hi : node < LENGTH := by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < (2:Nat)^level)).mpr
    have fit : (16777216:Nat)*2 ≤ 16777216*2^level := Nat.mul_le_mul_left _ scale
    change 16777216+index.val < 16777216*2^level
    change index.val < 16777216 at bounded
    omega
  change 0 < node ^^^ 1 ∧ node ^^^ 1 < 16777216
  change node < 16777216 at hi
  by_cases parity : node % 2 = 0
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr parity)]
    omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]
    omega

theorem canonical_lower_wire_sibling (oracle : Oracle) (message : Message)
    (positions : Positions) (salts : CompleteSaltTape) (ordinal : Nat) (present : ordinal < positions.card)
    (state : MachineState) (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state)
    (level : Nat) (within : level < 16) :
    lowerWireSibling state ordinal level =
      honestHeap oracle message salts (Opening.lowerNode (honestIndex positions ordinal present) level ^^^ 1) := by
  by_cases first : level = 0
  · subst level
    simpa only [lowerWireSibling, ite_true, Opening.lowerNode, Nat.pow_zero, Nat.div_one] using
      packed_record_first_sibling oracle message positions salts ordinal present state framed
  · rw [lowerWireSibling, ite_eq_right first]
    let slot := level-1
    have restored : slot+1=level := by unfold slot; omega
    have actual := packed_record_later_sibling oracle message positions salts ordinal present state framed slot (by
      unfold slot
      omega)
    rw [restored] at actual
    rw [actual]
    obtain ⟨lo,hi⟩ := later_sibling_internal (honestIndex positions ordinal present) level (by omega) within
    exact honest_projected_node _ _ _ lo hi

/-- A fold over the sixteen siblings and the two-permutation leaf digest. -/
def lowerDigestFold (oracle : Oracle) (index : Index) (leaf : Digest) (sibling : Nat → Digest) : Nat → Digest
  | 0 => leaf
  | count+1 => padLow (oracle.compression
      (pathPair (Opening.lowerNode index count) (lowerDigestFold oracle index leaf sibling count) (sibling count)))

private theorem lower_node_above_two (index : Index) (level : Nat) (within : level < 16) :
    2 ≤ Opening.lowerNode index level := by
  have scaleBound : (2:Nat)^level ≤ 32768 :=
    (Nat.pow_le_pow_right (by decide : 0 < (2:Nat)) (show level ≤ 15 by omega)).trans (by decide)
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < (2:Nat)^level)).mpr
  change 2*2^level ≤ 16777216+index.val
  omega

theorem lower_fold_canonical (oracle : Oracle) (leaves : DigestTape) (index : Index)
    (leaf : Digest) (leafCorrect : leaf = leaves index) (sibling : Nat → Digest)
    (levels : Nat) (within : levels ≤ 16)
    (siblings : ∀ j < levels, sibling j =
      transcriptHeap true oracle.compression leaves (Opening.lowerNode index j ^^^ 1)) :
    lowerDigestFold oracle index leaf sibling levels =
      transcriptHeap true oracle.compression leaves (Opening.lowerNode index levels) := by
  induction levels with
  | zero =>
    simpa only [lowerDigestFold, Opening.lowerNode, Nat.pow_zero, Nat.div_one,
      transcript_heap_leaf] using leafCorrect
  | succ level ih =>
    rw [lowerDigestFold, ih (by omega) (fun j inside => siblings j (by omega)), siblings level (by omega),
      Opening.lower_node_next]
    exact packed_honest_heap_climb oracle leaves _ (lower_node_above_two index level (by omega))
      (Opening.lower_node_bound index level)

end TwoPermutationPrototype.Packed.Checker
