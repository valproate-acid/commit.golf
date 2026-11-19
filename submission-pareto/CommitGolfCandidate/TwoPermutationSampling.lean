import Std.Tactic

/-! Swapping unused endpoints permutes completions of a partial table. This gives
the counting bijections required for forward and inverse lazy-sampling steps. -/
namespace TwoPermutationPrototype.Sampling

universe u

structure BiPermutation (α : Type u) where
  forward : α → α
  inverse : α → α
  leftInverse (x : α) : inverse (forward x) = x
  rightInverse (y : α) : forward (inverse y) = y

def swap {α : Type u} [DecidableEq α] (x y z : α) : α :=
  if z = x then y else if z = y then x else z

@[simp] theorem swap_first {α : Type u} [DecidableEq α] (x y : α) : swap x y x = y := by
  simp [swap]

@[simp] theorem swap_second {α : Type u} [DecidableEq α] (x y : α) : swap x y y = x := by
  by_cases equal : y = x
  · subst y; simp
  · simp [swap, equal]

theorem swap_other {α : Type u} [DecidableEq α] {x y z : α} (hx : z ≠ x) (hy : z ≠ y) :
    swap x y z = z := by simp [swap, hx, hy]

@[simp] theorem swap_involution {α : Type u} [DecidableEq α] (x y z : α) :
    swap x y (swap x y z) = z := by
  by_cases hx : z = x
  · subst z; simp
  by_cases hy : z = y
  · subst z; simp
  · simp [swap_other hx hy]

theorem BiPermutation.ext {α : Type u} {p q : BiPermutation α}
    (forward : p.forward = q.forward) (inverse : p.inverse = q.inverse) : p = q := by
  cases p
  cases q
  simp_all

def BiPermutation.flip {α : Type u} (p : BiPermutation α) : BiPermutation α where
  forward := p.inverse
  inverse := p.forward
  leftInverse := p.rightInverse
  rightInverse := p.leftInverse

def BiPermutation.swapOutputs {α : Type u} [DecidableEq α] (p : BiPermutation α) (x y : α) :
    BiPermutation α where
  forward a := swap x y (p.forward a)
  inverse b := p.inverse (swap x y b)
  leftInverse a := by simp [p.leftInverse]
  rightInverse b := by simp [p.rightInverse]

@[simp] theorem BiPermutation.swapOutputs_twice {α : Type u} [DecidableEq α]
    (p : BiPermutation α) (x y : α) : (p.swapOutputs x y).swapOutputs x y = p := by
  apply BiPermutation.ext <;> funext a <;> simp [swapOutputs]

def Agrees {α : Type u} (table : List (α × α)) (p : BiPermutation α) : Prop :=
  ∀ row ∈ table, p.forward row.1 = row.2

def UnusedOutput {α : Type u} (table : List (α × α)) (answer : α) : Prop :=
  ∀ row ∈ table, row.2 ≠ answer

def UnusedInput {α : Type u} (table : List (α × α)) (answer : α) : Prop :=
  ∀ row ∈ table, row.1 ≠ answer

theorem fresh_forward_answer_unused {α : Type u} {table : List (α × α)} {p : BiPermutation α}
    {x : α} (agrees : Agrees table p) (fresh : UnusedInput table x) :
    UnusedOutput table (p.forward x) := by
  intro row present same
  apply fresh row present
  have both := congrArg p.inverse ((agrees row present).trans same)
  simpa [p.leftInverse] using both

theorem fresh_inverse_answer_unused {α : Type u} {table : List (α × α)} {p : BiPermutation α}
    {y : α} (agrees : Agrees table p) (fresh : UnusedOutput table y) :
    UnusedInput table (p.inverse y) := by
  intro row present same
  apply fresh row present
  have both := congrArg p.forward same
  simpa [agrees row present, p.rightInverse] using both

theorem swap_agrees {α : Type u} [DecidableEq α] {table : List (α × α)} {p : BiPermutation α}
    {x y : α} (old : Agrees table p) (hx : UnusedOutput table x) (hy : UnusedOutput table y) :
    Agrees table (p.swapOutputs x y) := by
  intro row present
  change swap x y (p.forward row.1) = row.2
  rw [old row present, swap_other (hx row present) (hy row present)]

structure Transport (α β : Type u) where
  toFun : α → β
  invFun : β → α
  leftInverse (a : α) : invFun (toFun a) = a
  rightInverse (b : β) : toFun (invFun b) = b

def Transport.trans {α β γ : Type u} (first : Transport α β) (second : Transport β γ) : Transport α γ where
  toFun x := second.toFun (first.toFun x)
  invFun x := first.invFun (second.invFun x)
  leftInverse x := by rw [second.leftInverse, first.leftInverse]
  rightInverse x := by rw [first.rightInverse, second.rightInverse]

def Transport.symm {α β : Type u} (transport : Transport α β) : Transport β α where
  toFun := transport.invFun
  invFun := transport.toFun
  leftInverse := transport.rightInverse
  rightInverse := transport.leftInverse

abbrev ForwardCompletion {α : Type u} (table : List (α × α)) (input answer : α) :=
  {p : BiPermutation α // Agrees table p ∧ p.forward input = answer}

def forward_transport {α : Type u} [DecidableEq α] (table : List (α × α)) (input x y : α)
    (hx : UnusedOutput table x) (hy : UnusedOutput table y) :
    Transport (ForwardCompletion table input x) (ForwardCompletion table input y) where
  toFun p := ⟨p.val.swapOutputs x y, swap_agrees p.property.1 hx hy, by
    change swap x y (p.val.forward input) = y
    rw [p.property.2, swap_first]⟩
  invFun p := ⟨p.val.swapOutputs x y, swap_agrees p.property.1 hx hy, by
    change swap x y (p.val.forward input) = x
    rw [p.property.2, swap_second]⟩
  leftInverse p := Subtype.ext (p.val.swapOutputs_twice x y)
  rightInverse p := Subtype.ext (p.val.swapOutputs_twice x y)

abbrev InverseCompletion {α : Type u} (table : List (α × α)) (input answer : α) :=
  {p : BiPermutation α // Agrees table p ∧ p.inverse input = answer}

def flipTable {α : Type u} (table : List (α × α)) : List (α × α) := table.map Prod.swap

theorem flip_agrees {α : Type u} {table : List (α × α)} {p : BiPermutation α} :
    Agrees (flipTable table) p.flip ↔ Agrees table p := by
  constructor
  · intro h row present
    have value := h row.swap (List.mem_map_of_mem present)
    change p.inverse row.2 = row.1 at value
    rw [← value, p.rightInverse]
  · intro h row present
    obtain ⟨original, inTable, rfl⟩ := List.mem_map.mp present
    change p.inverse original.2 = original.1
    rw [← h original inTable, p.leftInverse]

private def flip_transport {α : Type u} (table : List (α × α)) (input answer : α) :
    Transport (InverseCompletion table input answer) (ForwardCompletion (flipTable table) input answer) where
  toFun p := ⟨p.val.flip, flip_agrees.mpr p.property.1, p.property.2⟩
  invFun p := ⟨p.val.flip, flip_agrees.mp p.property.1, p.property.2⟩
  leftInverse _ := rfl
  rightInverse _ := rfl

theorem flipped_output_unused {α : Type u} {table : List (α × α)} {x : α}
    (unused : UnusedInput table x) : UnusedOutput (flipTable table) x := by
  intro row present
  obtain ⟨original, inTable, rfl⟩ := List.mem_map.mp present
  exact unused original inTable

def inverse_transport {α : Type u} [DecidableEq α] (table : List (α × α)) (input x y : α)
    (hx : UnusedInput table x) (hy : UnusedInput table y) :
    Transport (InverseCompletion table input x) (InverseCompletion table input y) :=
  let replies := forward_transport (flipTable table) input x y (flipped_output_unused hx) (flipped_output_unused hy)
  (flip_transport table input x).trans (replies.trans (flip_transport table input y).symm)

abbrev Fiber {α β : Type u} (read : α → β) (answer : β) := {value : α // read value = answer}

private theorem move_fiber_value {α β : Type u} (read : α → β) (anchor : β)
    (move : ∀ answer, Transport (Fiber read answer) (Fiber read anchor))
    (value : α) (answer : β) (equal : read value = answer) :
    (move (read value)).toFun ⟨value, rfl⟩ = (move answer).toFun ⟨value, equal⟩ := by
  subst answer
  rfl

/-- Split an observation into its reply and the residual state in one fixed fiber. -/
def split_fibers {α β : Type u} (read : α → β) (anchor : β)
    (move : ∀ answer, Transport (Fiber read answer) (Fiber read anchor)) :
    Transport α (β × Fiber read anchor) where
  toFun value := (read value, (move (read value)).toFun ⟨value, rfl⟩)
  invFun pair := ((move pair.1).invFun pair.2).val
  leftInverse value := congrArg Subtype.val ((move (read value)).leftInverse ⟨value, rfl⟩)
  rightInverse pair := by
    let selected := (move pair.1).invFun pair.2
    change (read selected.val, (move (read selected.val)).toFun ⟨selected.val, rfl⟩) = pair
    apply Prod.ext
    · exact selected.property
    · change (move (read selected.val)).toFun ⟨selected.val, rfl⟩ = pair.2
      rw [move_fiber_value read anchor move selected.val pair.1 selected.property]
      exact (move pair.1).rightInverse pair.2

abbrev Completion {α : Type u} (table : List (α × α)) := {p : BiPermutation α // Agrees table p}
abbrev RemainingOutputs {α : Type u} (table : List (α × α)) := {y : α // UnusedOutput table y}
abbrev RemainingInputs {α : Type u} (table : List (α × α)) := {x : α // UnusedInput table x}

def readForward {α : Type u} (table : List (α × α)) (input : α) (fresh : UnusedInput table input)
    (p : Completion table) : RemainingOutputs table :=
  ⟨p.val.forward input, fresh_forward_answer_unused p.property fresh⟩

def readInverse {α : Type u} (table : List (α × α)) (input : α) (fresh : UnusedOutput table input)
    (p : Completion table) : RemainingInputs table :=
  ⟨p.val.inverse input, fresh_inverse_answer_unused p.property fresh⟩

private def forward_fiber {α : Type u} (table : List (α × α)) (input : α)
    (fresh : UnusedInput table input) (answer : RemainingOutputs table) :
    Transport (Fiber (readForward table input fresh) answer) (ForwardCompletion table input answer.val) where
  toFun p := ⟨p.val.val, p.val.property, congrArg Subtype.val p.property⟩
  invFun p := ⟨⟨p.val, p.property.1⟩, Subtype.ext p.property.2⟩
  leftInverse _ := rfl
  rightInverse _ := rfl

private def inverse_fiber {α : Type u} (table : List (α × α)) (input : α)
    (fresh : UnusedOutput table input) (answer : RemainingInputs table) :
    Transport (Fiber (readInverse table input fresh) answer) (InverseCompletion table input answer.val) where
  toFun p := ⟨p.val.val, p.val.property, congrArg Subtype.val p.property⟩
  invFun p := ⟨⟨p.val, p.property.1⟩, Subtype.ext p.property.2⟩
  leftInverse _ := rfl
  rightInverse _ := rfl

def forward_fiber_move {α : Type u} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedInput table input) (anchor answer : RemainingOutputs table) :
    Transport (Fiber (readForward table input fresh) answer) (Fiber (readForward table input fresh) anchor) :=
  let selection := forward_transport table input answer.val anchor.val answer.property anchor.property
  (forward_fiber table input fresh answer).trans (selection.trans (forward_fiber table input fresh anchor).symm)

def inverse_fiber_move {α : Type u} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedOutput table input) (anchor answer : RemainingInputs table) :
    Transport (Fiber (readInverse table input fresh) answer) (Fiber (readInverse table input fresh) anchor) :=
  let selection := inverse_transport table input answer.val anchor.val answer.property anchor.property
  (inverse_fiber table input fresh answer).trans (selection.trans (inverse_fiber table input fresh anchor).symm)

def forward_split {α : Type u} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedInput table input) (anchor : RemainingOutputs table) :
    Transport (Completion table) (RemainingOutputs table × Fiber (readForward table input fresh) anchor) :=
  split_fibers (readForward table input fresh) anchor (forward_fiber_move table input fresh anchor)

def inverse_split {α : Type u} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedOutput table input) (anchor : RemainingInputs table) :
    Transport (Completion table) (RemainingInputs table × Fiber (readInverse table input fresh) anchor) :=
  split_fibers (readInverse table input fresh) anchor (inverse_fiber_move table input fresh anchor)

theorem forward_split_reply {α : Type u} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedInput table input) (anchor : RemainingOutputs table) (p : Completion table) :
    ((forward_split table input fresh anchor).toFun p).1 = readForward table input fresh p := rfl

theorem inverse_split_reply {α : Type u} [DecidableEq α] (table : List (α × α)) (input : α)
    (fresh : UnusedOutput table input) (anchor : RemainingInputs table) (p : Completion table) :
    ((inverse_split table input fresh anchor).toFun p).1 = readInverse table input fresh p := rfl

theorem agrees_cons {α : Type u} (table : List (α × α)) (pair : α × α) (p : BiPermutation α) :
    Agrees (pair :: table) p ↔ p.forward pair.1 = pair.2 ∧ Agrees table p := by
  unfold Agrees
  constructor
  · intro all
    exact ⟨all pair (by simp), fun row present => all row (by simp [present])⟩
  · intro ⟨first, rest⟩ row present
    rcases List.mem_cons.mp present with rfl | present
    · exact first
    · exact rest row present

def forward_cons_transport {α : Type u} (table : List (α × α)) (input : α)
    (fresh : UnusedInput table input) (answer : RemainingOutputs table) :
    Transport (Fiber (readForward table input fresh) answer) (Completion ((input, answer.val) :: table)) where
  toFun p := ⟨p.val.val, (agrees_cons table _ _).mpr ⟨congrArg Subtype.val p.property, p.val.property⟩⟩
  invFun p := by
    have after := (agrees_cons table _ _).mp p.property
    exact ⟨⟨p.val, after.2⟩, Subtype.ext after.1⟩
  leftInverse _ := rfl
  rightInverse _ := rfl

def inverse_cons_transport {α : Type u} (table : List (α × α)) (input : α)
    (fresh : UnusedOutput table input) (answer : RemainingInputs table) :
    Transport (Fiber (readInverse table input fresh) answer) (Completion ((answer.val, input) :: table)) where
  toFun p := by
    have backward : p.val.val.inverse input = answer.val := congrArg Subtype.val p.property
    have forward : p.val.val.forward answer.val = input := by rw [← backward, p.val.val.rightInverse]
    exact ⟨p.val.val, (agrees_cons table _ _).mpr ⟨forward, p.val.property⟩⟩
  invFun p := by
    have after := (agrees_cons table _ _).mp p.property
    have forward : p.val.forward answer.val = input := after.1
    have backward : p.val.inverse input = answer.val :=
      (congrArg p.val.inverse forward.symm).trans (p.val.leftInverse answer.val)
    exact ⟨⟨p.val, after.2⟩, Subtype.ext backward⟩
  leftInverse _ := rfl
  rightInverse _ := rfl

theorem replay_budget_arithmetic {q calls : Nat} (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) :
    calls ≤ 2 ^ 32 * q ∧ calls * calls ≤ 2 ^ 121 * q ∧ calls ≤ 2 ^ 121 := by
  have square : q * q ≤ 2 ^ 120 * q := Nat.mul_le_mul_right q small
  have replayExpansion : (q + 2 ^ 31) * (q + 2 ^ 31) =
      q * q + 2 ^ 32 * q + 2 ^ 62 := by
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have replaySquare := Nat.mul_le_mul withReplay withReplay
  rw [replayExpansion] at replaySquare
  exact ⟨by omega, by omega, by omega⟩

/-- The inverse-domain, 256-bit digest, and 768-bit join terms fit comfortably
inside one quarter of the target. The factor two allows sampling without replacement. -/
theorem permutation_binding_margin {q calls : Nat} (positive : 1 ≤ q) (small : q ≤ 2 ^ 120)
    (withReplay : calls ≤ q + 2 ^ 31) :
    2 * calls * 2 ^ (768 - 168) + (calls * calls) * 2 ^ (768 - 256) +
      4 * (calls * calls) ≤ q * 2 ^ (768 - 122) := by
  obtain ⟨linear, square, _⟩ := replay_budget_arithmetic positive small withReplay
  omega

end TwoPermutationPrototype.Sampling
