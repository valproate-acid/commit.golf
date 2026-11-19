import CommitGolfCandidate.CapConsistency
import CommitGolfCandidate.CapWitness

/-! Build the cap's known-leaf shape from the duplicate-checked root map.
This file links occupancy to supplied group records, without assuming a machine
has populated those records. -/
namespace CommitGolfCandidate
open CommitGolf

def capKnownView (roots : CapRootMap) : (height offset : Nat) → CapView height
  | 0, offset => .leaf (roots offset)
  | height + 1, offset =>
      .node (capKnownView roots height offset)
        (capKnownView roots height (offset + 2^height))

def capPathIndex : {height : Nat} → Path height → Nat
  | _, .here => 0
  | _, .left path => capPathIndex path
  | height + 1, .right path => 2^height + capPathIndex path

theorem cap_path_index_bound {height : Nat} (path : Path height) :
    capPathIndex path < 2^height := by
  induction path with
  | here => decide
  | left path ih => simp only [capPathIndex, pow_succ]; omega
  | right path ih => simp only [capPathIndex, pow_succ]; omega

theorem cap_known_view_leaf (roots : CapRootMap) {height : Nat} (path : Path height)
    (offset : Nat) :
    capLeafValue (capKnownView roots height offset) path =
      roots (offset + capPathIndex path) := by
  induction path generalizing offset with
  | here => simp [capLeafValue, capKnownView, capPathIndex]
  | left path ih => simpa [capLeafValue, capKnownView, capPathIndex] using ih offset
  | @right height path ih =>
      simpa [capLeafValue, capKnownView, capPathIndex, Nat.add_assoc] using ih (offset + 2^height)

theorem cap_known_view_count (roots : CapRootMap) (height offset : Nat) :
    capMarkedCount (capKnownView roots height offset) =
      ∑ index ∈ Finset.range (2^height), if (roots (offset + index)).isSome then 1 else 0 := by
  induction height generalizing offset with
  | zero => simp only [capKnownView, capMarkedCount, pow_zero, Finset.sum_range_one, Nat.add_zero]
  | succ height ih =>
      simp only [capKnownView, capMarkedCount, ih]
      rw [pow_succ]
      have twice : 2^height * 2 = 2^height + 2^height := by omega
      rw [twice, Finset.sum_range_add]
      simp [Nat.add_assoc]

/-- The number of known cap leaves is exactly the distinct occupied group count. -/
theorem cap_known_view_card (roots : CapRootMap) :
    capMarkedCount (capKnownView roots 8 0) =
      ((Finset.range 256).filter (fun group => (roots group).isSome = true)).card := by
  rw [cap_known_view_count]
  norm_num

/-- Every supplied lower root occupies its requested cap leaf after a successful
duplicate-consistency check. -/
theorem cap_collected_view_leaf (records : List (Nat × Digest)) (roots : CapRootMap)
    (accepted : capCollect records = some roots) (path : Path 8) (value : Digest)
    (member : (capPathIndex path, value) ∈ records) :
    capLeafValue (capKnownView roots 8 0) path = some value := by
  rw [cap_known_view_leaf]
  simpa using cap_collect_member records roots accepted (capPathIndex path) value member
end CommitGolfCandidate
