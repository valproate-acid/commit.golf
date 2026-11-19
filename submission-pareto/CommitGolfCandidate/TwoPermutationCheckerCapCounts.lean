import CommitGolfCandidate.TwoPermutationOpeningCapStructure

namespace TwoPermutationPrototype.Checker
open TwoPermutationPrototype.Sampling

def capHashCount (groups : List Nat) (node : Nat) : Nat → Nat
  | 0 => 0
  | height+1 => if capIsMarked groups node (height+1) then
      1 + capHashCount groups (2*node) height + capHashCount groups (2*node+1) height else 0

def scopeSize (groups : List Nat) (node height : Nat) : Nat :=
  (groups.filter fun group => group / 2^height == node).length

theorem scope_size_split (groups : List Nat) (node height : Nat) :
    scopeSize groups node (height+1) =
      scopeSize groups (2*node) height + scopeSize groups (2*node+1) height := by
  induction groups with
  | nil => rfl
  | cons group tail ih =>
    have parent : group / 2^(height+1) = (group / 2^height)/2 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    simp only [scopeSize] at ih ⊢
    simp only [List.filter_cons, beq_iff_eq, parent]
    split <;> split <;> split <;> (try simp only [List.length_cons]) <;> omega

theorem nonempty_cap_scope (groups : List Nat) (node height : Nat)
    (marked : capIsMarked groups node height = true) :
    1 ≤ scopeSize groups node height := by
  simp only [capIsMarked, List.any_eq_true, beq_iff_eq] at marked
  obtain ⟨group, listed, equal⟩ := marked
  have present : group ∈ groups.filter (fun g => g/2^height == node) :=
    List.mem_filter.mpr ⟨listed, beq_iff_eq.mpr equal⟩
  exact Nat.succ_le_iff.mpr (List.length_pos_of_mem present)

theorem cap_hash_count_by_groups (groups : List Nat) (node height : Nat) :
    capHashCount groups node height ≤ height*scopeSize groups node height := by
  induction height generalizing node with
  | zero => simp [capHashCount]
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    cases mark : capIsMarked groups node (height+1) with
    | false => simp [capHashCount, mark]
    | true =>
      have nonempty := nonempty_cap_scope groups node (height+1) mark
      rw [capHashCount, mark, ite_eq_left rfl, scope_size_split]
      rw [scope_size_split] at nonempty
      let l := scopeSize groups (2*node) height
      let r := scopeSize groups (2*node+1) height
      rw [show (height+1)*(l+r) = height*l+height*r+l+r by ring]
      have lbound : capHashCount groups (2*node) height ≤ height*l := left
      have rbound : capHashCount groups (2*node+1) height ≤ height*r := right
      have positive : 1 ≤ l+r := nonempty
      omega

theorem cap_hash_count_tree (groups : List Nat) (node height : Nat) :
    capHashCount groups node height ≤ 2^height-1 := by
  induction height generalizing node with
  | zero => rfl
  | succ height ih =>
    have left := ih (2*node)
    have right := ih (2*node+1)
    have positive : 0 < 2^height := by positivity
    rw [capHashCount, Nat.pow_succ]
    split <;> omega

theorem cap_hash_count_root (groups : List Nat) : capHashCount groups 1 8 ≤ 8*groups.length :=
  (cap_hash_count_by_groups groups 1 8).trans
    (Nat.mul_le_mul_left _ (List.length_filter_le ..))

end TwoPermutationPrototype.Checker
