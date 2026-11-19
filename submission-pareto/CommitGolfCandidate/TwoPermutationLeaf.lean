import Std.Tactic

/-! Word-level geometry and resource arithmetic for the experimental RV64 leaf.
This file does not refine the trusted decoder, syscall semantics, or security games. -/
namespace TwoPermutationPrototype

abbrev Word := BitVec 64
abbrev Words (count : Nat) := Fin count → Word
abbrev Memory := Nat → Word
abbrev Permutation := Words 25 → Words 25

def window {count : Nat} (mem : Memory) (start : Nat) : Words count :=
  fun i => mem (start + i.val)

def writeWindow {count : Nat} (mem : Memory) (start : Nat) (words : Words count) : Memory :=
  fun i => if h : start ≤ i ∧ i < start + count then words ⟨i - start, by omega⟩ else mem i

def writeWord (mem : Memory) (address : Nat) (word : Word) : Memory :=
  fun i => if i = address then word else mem i

def firstTag (index : Nat) : Word := BitVec.ofNat 64 (4056 + 256 * index)
def secondTag (index : Nat) : Word := firstTag index + 96

def header (index : Nat) (nonce : Words 2) : Words 5 := fun i =>
  if i.val = 0 then firstTag index else if i.val < 3 then 0 else nonce ⟨i.val - 3, by omega⟩

def firstInput (index : Nat) (nonce : Words 2) (message : Words 32) : Words 25 := fun i =>
  if h : i.val < 5 then header index nonce ⟨i.val, h⟩ else message ⟨i.val - 5, by omega⟩

def secondInput (index : Nat) (firstReply : Words 25) (message : Words 32) : Words 25 := fun i =>
  if i.val = 0 then secondTag index
  else if h : i.val < 13 then firstReply ⟨i.val + 12, by omega⟩
  else message ⟨i.val + 7, by omega⟩

def digest (perm : Permutation) (index : Nat) (nonce : Words 2) (message : Words 32) : Words 4 :=
  fun i => (perm (secondInput index (perm (firstInput index nonce message)) message)) ⟨i.val, by omega⟩

def retained (reply : Words 25) : Words 12 := fun i => reply ⟨i.val + 13, by omega⟩
def lowDigest (reply : Words 25) : Words 4 := fun i => reply ⟨i.val, by omega⟩

theorem commit_tag_address (index : Nat) :
    firstTag index = BitVec.ofNat 64 ((507 + 32 * index) * 8) := by
  unfold firstTag
  congr 1
  omega

theorem second_tag_address (index : Nat) :
    secondTag index = BitVec.ofNat 64 ((507 + 32 * index + 12) * 8) := by
  rw [secondTag, commit_tag_address]
  change BitVec.ofNat 64 ((507 + 32 * index) * 8) + BitVec.ofNat 64 96 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem tags_disjoint {left right : Nat} (hl : left < 2 ^ 24) (hr : right < 2 ^ 24) :
    firstTag left ≠ secondTag right := by
  intro equal
  have lvalue : (firstTag left).toNat = 4056 + 256 * left := by
    rw [firstTag, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have rvalue : (secondTag right).toNat = 4152 + 256 * right := by
    rw [second_tag_address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt] <;> omega
  have values := congrArg BitVec.toNat equal
  rw [lvalue, rvalue] at values
  omega

theorem first_tag_injective {left right : Nat} (hl : left < 2 ^ 24) (hr : right < 2 ^ 24)
    (same : firstTag left = firstTag right) : left = right := by
  have equal := congrArg BitVec.toNat same
  simp only [firstTag, BitVec.toNat_ofNat] at equal
  rw [Nat.mod_eq_of_lt (by omega : 4056 + 256 * left < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4056 + 256 * right < 2 ^ 64)] at equal
  omega

theorem second_tag_injective {left right : Nat} (hl : left < 2 ^ 24) (hr : right < 2 ^ 24)
    (same : secondTag left = secondTag right) : left = right := by
  apply first_tag_injective hl hr
  unfold secondTag at same
  have equal := congrArg (fun word : Word => word - 96) same
  simpa using equal

theorem distinct_message_equal_digest (perm : Permutation) (index : Nat)
    (nonce₀ nonce₁ : Words 2) (message₀ message₁ : Words 32)
    (different : message₀ ≠ message₁) (same : digest perm index nonce₀ message₀ = digest perm index nonce₁ message₁) :
    let a₀ := firstInput index nonce₀ message₀
    let a₁ := firstInput index nonce₁ message₁
    let b₀ := secondInput index (perm a₀) message₀
    let b₁ := secondInput index (perm a₁) message₁
    (a₀ ≠ a₁ ∧ retained (perm a₀) = retained (perm a₁)) ∨
      (b₀ ≠ b₁ ∧ lowDigest (perm b₀) = lowDigest (perm b₁)) := by
  dsimp only
  by_cases bEqual : secondInput index (perm (firstInput index nonce₀ message₀)) message₀ =
      secondInput index (perm (firstInput index nonce₁ message₁)) message₁
  · apply Or.inl
    constructor
    · intro aEqual
      apply different
      funext i
      by_cases head : i.val < 20
      · have exactInput := congrFun aEqual (⟨i.val + 5, by omega⟩ : Fin 25)
        have bound : ¬ i.val + 5 < 5 := by omega
        simpa [firstInput, bound] using exactInput
      · have j : i.val - 7 < 25 := by omega
        have exactInput := congrFun bEqual (⟨i.val - 7, j⟩ : Fin 25)
        have notTag : i.val - 7 ≠ 0 := by omega
        have notRetained : ¬ i.val - 7 < 13 := by omega
        have offset : i.val - 7 + 7 = i.val := by omega
        simpa [secondInput, notTag, notRetained, offset] using exactInput
    · funext i
      have exactInput := congrFun bEqual (⟨i.val + 1, by omega⟩ : Fin 25)
      have inRetained : i.val + 1 < 13 := by omega
      simpa [secondInput, retained, inRetained, Nat.add_assoc] using exactInput
  · exact Or.inr ⟨bEqual, same⟩

theorem first_window (mem : Memory) (start index : Nat) (nonce : Words 2) :
    window (writeWindow mem start (header index nonce)) start =
      firstInput index nonce (window mem (start + 5)) := by
  funext i
  by_cases inHeader : i.val < 5
  · have inside : start ≤ start + i.val ∧ start + i.val < start + 5 := by omega
    simp [window, writeWindow, firstInput, inside, inHeader]
  · have offset : start + i.val = start + 5 + (i.val - 5) := by omega
    simp [window, writeWindow, firstInput, inHeader, ← offset]

theorem second_window (mem : Memory) (start index : Nat) (nonce : Words 2) (reply : Words 25) :
    window (writeWord (writeWindow (writeWindow mem start (header index nonce)) start reply)
      (start + 12) (secondTag index)) (start + 12) =
      secondInput index reply (window mem (start + 5)) := by
  funext i
  by_cases tag : i.val = 0
  · simp [window, writeWord, secondInput, tag]
  · by_cases inReply : i.val < 13
    · have inside : start ≤ start + 12 + i.val ∧ start + 12 + i.val < start + 25 := by omega
      have offset : start + 12 + i.val - start = i.val + 12 := by omega
      simp [window, writeWord, writeWindow, secondInput, tag, inReply, inside, offset]
    · have outsideReply : ¬ (start ≤ start + 12 + i.val ∧ start + 12 + i.val < start + 25) := by omega
      have outsideHeader : ¬ (start ≤ start + 12 + i.val ∧ start + 12 + i.val < start + 5) := by omega
      have offset : start + 12 + i.val = start + 5 + (i.val + 7) := by omega
      simp [window, writeWord, writeWindow, secondInput, tag, inReply, outsideReply,
        outsideHeader, ← offset]

theorem direct_digest (mem : Memory) (perm : Permutation) (start index out : Nat) (nonce : Words 2) :
    let written := writeWindow mem start (header index nonce)
    let firstReply := perm (window written start)
    let prepared := writeWord (writeWindow written start firstReply) (start + 12) (secondTag index)
    let finished := writeWindow prepared out (perm (window prepared (start + 12)))
    (window finished out : Words 4) = digest perm index nonce (window mem (start + 5)) := by
  dsimp only
  rw [first_window, second_window]
  funext i
  have inside : out ≤ out + i.val ∧ out + i.val < out + 25 := by omega
  simp [window, writeWindow, digest, inside]

theorem future_input_untouched (mem : Memory) (perm : Permutation) (start index : Nat)
    (nonce : Words 2) {future : Nat} (after : start + 25 ≤ future) :
    let written := writeWindow mem start (header index nonce)
    let firstReply := perm (window written start)
    let prepared := writeWord (writeWindow written start firstReply) (start + 12) (secondTag index)
    prepared future = mem future := by
  dsimp only
  have noTag : future ≠ start + 12 := by omega
  have noReply : ¬ (start ≤ future ∧ future < start + 25) := by omega
  have noHeader : ¬ (start ≤ future ∧ future < start + 5) := by omega
  simp [writeWord, writeWindow, noTag, noReply, noHeader]

-- In the actual image leaf outputs are 32 bytes apart and salts start at offset 80N.
theorem leaf_output_before_salts {n i : Nat} (enough : 16 ≤ n) (leaf : i < n) :
    32 * n + 32 * i + 200 ≤ 80 * n := by omega

theorem second_window_ends_at_message_end (base : Nat) (room : 40 ≤ base) :
    base - 40 + 96 + 200 = base + 256 := by omega

theorem initial_check_prefix_after_indices (endOfIndices : Nat) :
    endOfIndices ≤ endOfIndices + 64 - 40 := by omega

def leafCycles : Nat := 11 + 1 + 2 * 8

def commitCycles (n : Nat) : Nat :=
  leafCycles * n + 3 * (n / 16) + (1 + 2 * n) + 10 * (n - 1) + (n - 1) / 128 + 31

def openingCycles (records capInternal occupied frontier : Nat) : Nat :=
  13 + 256 * records + 2551 + (19 * capInternal + 5 * occupied + 15 * frontier + 3) + 4

def packedOpeningCycles (records capInternal occupied frontier : Nat) : Nat :=
  13 + (590 * records - 1) + 2551 + (19 * capInternal + 5 * occupied + 37 * frontier + 3) + 4

def proofBytes (records frontier : Nat) : Nat := 528 * records + 32 * frontier

theorem production_commit_cycles : commitCycles (2 ^ 24) = 674365461 := by decide

theorem scalar_production_commit_cycles :
    45 * 2 ^ 24 + (2 ^ 24 - 1) / 128 + 23 = 755105814 := by decide

theorem packed_production_commit_cycles : commitCycles (2 ^ 24) + (2 ^ 24 - 1) = 691142676 := by decide

theorem production_opening_bound {internal occupied frontier : Nat}
    (hi : internal ≤ 255) (ho : occupied ≤ 128) (hf : frontier ≤ 128) :
    openingCycles 128 internal occupied frontier ≤ 42744 := by
  unfold openingCycles
  omega

theorem production_proof_bound {frontier : Nat} (bound : frontier ≤ 128) :
    proofBytes 128 frontier ≤ 71680 := by
  unfold proofBytes
  omega

theorem packed_production_bounds {internal occupied frontier : Nat}
    (hi : internal ≤ 255) (ho : occupied ≤ 128) (hf : frontier ≤ 128) :
    packedOpeningCycles 128 internal occupied frontier ≤ 88311 ∧
      498 * 128 + 30 * frontier ≤ 67584 := by
  unfold packedOpeningCycles
  omega

inductive CapMarks : Nat → Type where
  | leaf : Bool → CapMarks 0
  | node {height : Nat} : CapMarks height → CapMarks height → CapMarks (height + 1)

def CapMarks.occupied {height : Nat} : CapMarks height → Bool
  | .leaf marked => marked
  | .node left right => left.occupied || right.occupied

def CapMarks.boundary {height : Nat} (marks : CapMarks height) : Nat :=
  if marks.occupied then
    match marks with
    | .leaf _ => 0
    | .node left right => left.boundary + right.boundary
  else 1

theorem CapMarks.boundary_bound {height : Nat} (marks : CapMarks (height + 1)) :
    marks.boundary ≤ 2 ^ height := by
  induction height with
  | zero =>
    cases marks with
    | node left right =>
      cases left with
      | leaf l =>
        cases right with
        | leaf r => cases l <;> cases r <;> decide
  | succ height ih =>
    cases marks with
    | node left right =>
      have leftBound := ih left
      have rightBound := ih right
      rw [CapMarks.boundary, CapMarks.occupied, Nat.pow_succ]
      split
      · omega
      · have positive : 0 < 2 ^ height := Nat.pow_pos (by decide)
        omega

theorem production_boundary_bound (marks : CapMarks 8) : marks.boundary ≤ 128 :=
  CapMarks.boundary_bound (height := 7) marks

theorem check_call_bound {count capCalls : Nat} (capLimit : capCalls ≤ 8 * count) :
    18 * count + capCalls ≤ 26 * count := by omega

end TwoPermutationPrototype
