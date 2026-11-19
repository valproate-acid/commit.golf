import CommitGolfCandidate.TwoPermutationOpeningMemory

namespace TwoPermutationPrototype.Opening
open CommitGolf CommitGolf.Riscv

def lowerNode (index : Index) (level : Nat) : Nat :=
  (LENGTH + index.val) / 2 ^ level

def recordBase (ordinal : Nat) : Nat :=
  proofBase + 528 * ordinal

def siblingDest (ordinal level : Nat) : Nat :=
  recordBase ordinal + 16 + 32 * level

theorem lower_node_next (index : Index) (level : Nat) :
    lowerNode index (level + 1) = lowerNode index level / 2 := by
  simp only [lowerNode, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem lower_node_bound (index : Index) (level : Nat) :
    lowerNode index level < 2 * LENGTH := by
  have bound := index.isLt
  exact (Nat.div_le_self _ _).trans_lt (by omega)

theorem lower_swap_bound (index : Index) (level : Nat) :
    lowerNode index level ^^^ 1 < 2 * LENGTH :=
  Nat.xor_lt_two_pow (lower_node_bound index level) (show (1 : Nat) < 2 ^ 25 by decide)

theorem lower_cap_range (index : Index) : 256 ≤ lowerNode index 16 ∧ lowerNode index 16 < 512 := by
  have bound := index.isLt
  simp only [lowerNode]
  norm_num [LENGTH, LOG_LENGTH] at bound ⊢
  omega

theorem ordinal_nonce_geometry (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH) :
    (nonceBase + 16 * index.val) % 8 = 0 ∧
    (recordBase ordinal) % 8 = 0 ∧
    nonceBase + 16 * index.val + 16 ≤ recordBase ordinal ∧
    recordBase ordinal + 16 ≤ MEMORY_BYTES := by
  have indexBound := index.isLt
  norm_num [recordBase, proofBase, indicesBase, nonceBase, trapdoorBase, trapdoorBytes,
    LENGTH, LOG_LENGTH, MEMORY_BYTES] at bounded indexBound ⊢
  omega

theorem ordinal_sibling_geometry (index : Index) (ordinal level : Nat)
    (ordinalBound : ordinal < LENGTH) (levelBound : level < 16) :
    (trapdoorBase + 32 * (lowerNode index level ^^^ 1)) % 8 = 0 ∧
    siblingDest ordinal level % 8 = 0 ∧
    trapdoorBase + 32 * (lowerNode index level ^^^ 1) + 32 ≤ siblingDest ordinal level ∧
    siblingDest ordinal level + 32 ≤ MEMORY_BYTES := by
  have nodeBound := lower_swap_bound index level
  norm_num [siblingDest, recordBase, proofBase, indicesBase, trapdoorBase, trapdoorBytes,
    LENGTH, LOG_LENGTH, MEMORY_BYTES] at ordinalBound nodeBound ⊢
  omega

theorem ordinal_sibling_end (ordinal : Nat) :
    siblingDest ordinal 16 = recordBase (ordinal + 1) := by
  unfold siblingDest recordBase
  omega

/-- Cap scratch is disjoint from every input and from each lower record. -/
theorem marks_before_trapdoor : markBase + 8 * 512 ≤ trapdoorBase := by
  decide

theorem heap_before_nonces : trapdoorBase + 32 * (2 * LENGTH) ≤ nonceBase := by
  decide

theorem nonces_end_at_indices : nonceBase + 16 * LENGTH = indicesBase := by
  decide

theorem indices_before_records : indicesBase + 8 * LENGTH ≤ proofBase := by
  decide

/-- Every lower record and the entire worst-case cap footer fit the declared capacity. -/
theorem proof_fits_memory : proofBase + proofCapacity ≤ MEMORY_BYTES := by
  decide

end TwoPermutationPrototype.Opening
