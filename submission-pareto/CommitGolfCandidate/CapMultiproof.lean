import CommitGolfCandidate.CapFrontier
import CommitGolfCandidate.Model

/-! Semantic cap proof codec using the salted commitment tree and its compression
function. This supporting module does not establish machine refinement or security. -/
namespace CommitGolfCandidate
open CommitGolf
inductive CapView : Nat → Type
  | leaf (known : Option Digest) : CapView 0
  | node {height : Nat} (left right : CapView height) : CapView (height+1)
def capOccupied : {height : Nat} → CapView height → Bool
  | _, .leaf known => known.isSome
  | _, .node left right => capOccupied left || capOccupied right
def capView : {height : Nat} → Tree height → (Nat → Bool) → CapView height
  | _, .leaf value, marked => .leaf (if marked 0 then some value else none)
  | h+1, .node left right, marked =>
      .node (capView left marked) (capView right (fun i => marked (2^h+i)))
def capProof (compress : Compression) : {height : Nat} → Tree height → CapView height → List Digest
  | _, tree, view =>
      if capOccupied view then
        match tree, view with
        | .leaf _, .leaf _ => []
        | .node left right, .node lview rview => capProof compress left lview ++ capProof compress right rview
      else [Tree.root compress tree]
def capDecode (compress : Compression) : {height : Nat} → CapView height → List Digest → Option (Digest × List Digest)
  | _, view, proof =>
      if capOccupied view then
        match view with
        | .leaf known => known.map (fun value => (value, proof))
        | .node left right => do
            let (lroot, rest) ← capDecode compress left proof
            let (rroot, rest') ← capDecode compress right rest
            return (combine compress lroot rroot, rest')
      else match proof with
        | [] => none
        | value :: rest => some (value, rest)

/-- The codec consumes exactly its proof and preserves an arbitrary trailing suffix. -/
theorem cap_codec (compress : Compression) {height : Nat} (tree : Tree height)
    (marked : Nat → Bool) (rest : List Digest) :
    capDecode compress (capView tree marked) (capProof compress tree (capView tree marked) ++ rest) =
      some (Tree.root compress tree, rest) := by
  induction tree generalizing marked rest with
  | leaf value =>
      by_cases h : marked 0 = true <;> simp [capView, capProof, capDecode, capOccupied, Tree.root, h]
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (capView (.node left right) marked) = true
      · simp only [capView] at h ⊢
        simp only [capProof, h, ↓reduceIte]
        simp only [capDecode, h, ↓reduceIte, List.append_assoc]
        rw [ihLeft]
        change (do
          let result ← capDecode compress (capView right (fun i => marked (2^_+i)))
            (capProof compress right (capView right (fun i => marked (2^_+i))) ++ rest)
          return (combine compress (Tree.root compress left) result.1, result.2)) = _
        rw [ihRight]
        rfl
      · simp only [capView] at h ⊢
        simp [capProof, capDecode, h]
end CommitGolfCandidate

namespace CommitGolfCandidate
open CommitGolf

def capMarks : {height : Nat} → CapView height → MarkTree height
  | _, .leaf known => .leaf known.isSome
  | _, .node left right => .node (capMarks left) (capMarks right)

theorem cap_marks_occupied {height : Nat} (view : CapView height) :
    occupied (capMarks view) = capOccupied view := by
  induction view with
  | leaf known => rfl
  | node left right ihLeft ihRight => simp [capMarks, occupied, capOccupied, ihLeft, ihRight]

/-- No serialization headers are included: one digest per unknown boundary subtree. -/
theorem cap_proof_length (compress : Compression) {height : Nat} (tree : Tree height)
    (view : CapView height) :
    (capProof compress tree view).length = if capOccupied view then frontier (capMarks view) else 1 := by
  induction tree with
  | leaf value => cases view with
    | leaf known => cases known <;> simp [capProof, capOccupied, capMarks, frontier]
  | node left right ihLeft ihRight =>
      cases view with
      | node lview rview =>
          cases hl : capOccupied lview <;> cases hr : capOccupied rview <;>
            simp [capProof, capOccupied, capMarks, frontier, cap_marks_occupied, hl, hr,
              ihLeft, ihRight, Nat.add_comm]

theorem cap_occupied_proof_bound (compress : Compression) (tree : Tree 8)
    (view : CapView 8) (nonempty : capOccupied view = true) :
    (capProof compress tree view).length ≤ 128 := by
  rw [cap_proof_length, nonempty]
  exact height_eight_frontier (capMarks view)
end CommitGolfCandidate

namespace CommitGolfCandidate
open CommitGolf

def capMarkedCount : {height : Nat} → CapView height → Nat
  | _, .leaf known => if known.isSome then 1 else 0
  | _, .node left right => capMarkedCount left + capMarkedCount right

theorem cap_occupied_count {height : Nat} (view : CapView height) :
    capOccupied view = true ↔ 0 < capMarkedCount view := by
  induction view with
  | leaf known => cases known <;> simp [capOccupied, capMarkedCount]
  | node left right ihLeft ihRight =>
      simp only [capOccupied, Bool.or_eq_true, ihLeft, ihRight, capMarkedCount]
      omega

/-- Counts conceptual compression calls, not machine cycles. -/
def capCalls : {height : Nat} → CapView height → Nat
  | _, .leaf _ => 0
  | _, .node left right =>
      if capOccupied (.node left right) then capCalls left + capCalls right + 1 else 0

/-- A height-h cap requires at most h calls per occupied leaf, including sparse caps. -/
theorem cap_calls_bound {height : Nat} (view : CapView height) :
    capCalls view ≤ height * capMarkedCount view := by
  induction view with
  | leaf known => simp [capCalls]
  | node left right ihLeft ihRight =>
      by_cases h : capOccupied (.node left right) = true
      · have positive := (cap_occupied_count (.node left right)).mp h
        simp only [capMarkedCount] at positive
        simp only [capCalls, h, ↓reduceIte, capMarkedCount]
        nlinarith
      · simp [capCalls, h]
end CommitGolfCandidate

namespace CommitGolfCandidate
open CommitGolf
/-- Full-cap ceiling used for conservative binding replay overhead. -/
theorem cap_calls_full_bound {height : Nat} (view : CapView height) :
    capCalls view ≤ 2^height - 1 := by
  induction view with
  | leaf known => simp [capCalls]
  | node left right ihLeft ihRight =>
      rename_i depth
      by_cases h : capOccupied (.node left right) = true
      · simp only [capCalls, h, ↓reduceIte]
        rw [Nat.pow_succ]
        have positive : 1 ≤ 2^depth := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
        omega
      · simp [capCalls, h]

/-- Enlarging replay overhead to 304 still leaves ample 120-bit binding margin.
This arithmetic alone is not an extractor or a security theorem. -/
theorem cap_replay_arithmetic (q : Nat) (positive : 1 ≤ q) (small : q ≤ 2^120) :
    (q+304)^2 ≤ q * 2^136 := by
  have square := Nat.mul_le_mul_left q small
  nlinarith
end CommitGolfCandidate
