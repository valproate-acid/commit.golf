import CommitGolfCandidate.CapMultiproof

/-! Position grouping and arithmetic for the height-eight cap. These facts do not
assume that an image has populated or checked the corresponding root records. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Each cap leaf is a height-sixteen subtree of the original commitment. -/
def capGroup (index : Index) : Fin 256 :=
  ⟨index.val / 2^16, by
    have bound := index.isLt
    change index.val < 16777216 at bound
    change index.val / 65536 < 256
    omega⟩

/-- Group occupancy is determined by the requested positions, not the supplied proof. -/
def capGroups (positions : Positions) : Finset (Fin 256) := positions.image capGroup

theorem cap_groups_member (positions : Positions) (group : Fin 256) :
    group ∈ capGroups positions ↔ ∃ index ∈ positions, capGroup index = group := by
  simp [capGroups]

theorem cap_groups_card (positions : Positions) :
    (capGroups positions).card ≤ positions.card := Finset.card_image_le

theorem cap_groups_empty (positions : Positions) :
    capGroups positions = ∅ ↔ positions = ∅ := by simp [capGroups]

/-- 128 salt/lower-path records and at most 128 cap boundary digests, with no header. -/
theorem cap_batch_byte_bound (boundary : Nat) (bound : boundary ≤ 128) :
    BATCH * (32 + 16*32) + boundary*32 ≤ 73728 := by
  change 128 * (32 + 16*32) + boundary*32 ≤ 73728
  omega

/-- Eight leaf calls and sixteen lower-path calls, plus cap reconstruction. -/
theorem cap_honest_query_budget (positions : Positions) (capQueries : Nat)
    (bounded : capQueries ≤ 8 * (capGroups positions).card) :
    24*positions.card + capQueries ≤ CHECK_BUDGET positions.card := by
  have groups := cap_groups_card positions
  unfold CHECK_BUDGET
  omega

/-- A conservative replay can recompute all supplied lower records for two claims.
Reply recording is charged separately, so the eventual detector overhead is doubled. -/
def capReplayCeiling : Nat := 2 * (24*LENGTH + 255)

theorem cap_detector_arithmetic (q : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) :
    (q + 2*capReplayCeiling)^2 ≤ q*2^136 := by
  have square := Nat.mul_le_mul_left q small
  norm_num [capReplayCeiling, LENGTH, LOG_LENGTH] at *
  nlinarith
end CommitGolfCandidate
