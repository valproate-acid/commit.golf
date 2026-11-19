import CommitGolfCandidate.TwoPermutationLeaf
import CommitGolfCandidate.TwoPermutationRV64

/-! Relate the pinned RV64 ordinary instruction semantics to the logical 25-word
oracle windows. The separate syscall refinement still has to show that the
challenge's byte-serialized reads and writes implement these aligned windows. -/
namespace TwoPermutationPrototype.RV64
open RiscvZkvm.Rv64

def wordAddress (index : Nat) : Word := BitVec.ofNat 64 (8 * index)

def memoryView (state : MachineState) : Memory :=
  fun index => state.getMem (wordAddress index)

theorem wordAddress_add (a b : Nat) : wordAddress (a + b) = wordAddress a + wordAddress b := by
  unfold wordAddress
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem wordAddress_injective_of_bound {a b : Nat} (ha : a < 2 ^ 61) (hb : b < 2 ^ 61)
    (same : wordAddress a = wordAddress b) : a = b := by
  have equal := congrArg BitVec.toNat same
  simp only [wordAddress, BitVec.toNat_ofNat] at equal
  rw [Nat.mod_eq_of_lt (by omega : 8 * a < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * b < 2 ^ 64)] at equal
  omega

theorem memory_at_store {state : MachineState} {address index : Nat} {value : Word}
    (addressBound : address < 2 ^ 61) (indexBound : index < 2 ^ 61) :
    memoryView (state.setMem (wordAddress address) value) index =
      writeWord (memoryView state) address value index := by
  by_cases equal : index = address
  · subst index
    simp [memoryView, writeWord]
  · have disjoint : wordAddress index ≠ wordAddress address :=
      fun alias => equal (wordAddress_injective_of_bound indexBound addressBound alias)
    simp [memoryView, writeWord, equal, MachineState.getMem_setMem_ne disjoint]

def nonceWords (state : MachineState) (slot : Fin 16) : Words 2 := fun i =>
  if i.val = 0 then state.getMem (state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val))
  else state.getMem (state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val + 8))

theorem header_as_stores (mem : Memory) (start index atWord : Nat) (nonce : Words 2) :
    writeWindow mem start (header index nonce) atWord =
      writeWord (writeWord (writeWord (writeWord (writeWord mem start (firstTag index))
        (start + 1) 0) (start + 2) 0) (start + 3) (nonce 0)) (start + 4) (nonce 1) atWord := by
  by_cases is0 : atWord = start
  · subst atWord
    simp [writeWord, writeWindow, header]
  by_cases is1 : atWord = start + 1
  · subst atWord
    simp [writeWord, writeWindow, header]
  by_cases is2 : atWord = start + 2
  · subst atWord
    simp [writeWord, writeWindow, header]
  by_cases is3 : atWord = start + 3
  · subst atWord
    simp [writeWord, writeWindow, header]
  by_cases is4 : atWord = start + 4
  · subst atWord
    simp [writeWord, writeWindow, header]
  have outside : ¬ (start ≤ atWord ∧ atWord < start + 5) := by omega
  simp [writeWord, writeWindow, is0, is1, is2, is3, is4, outside]

private theorem address_one (start : Nat) : wordAddress start + 8 = wordAddress (start + 1) := by
  rw [wordAddress_add]; rfl

private theorem address_two (start : Nat) : wordAddress start + 16 = wordAddress (start + 2) := by
  rw [wordAddress_add]; rfl

private theorem address_three (start : Nat) : wordAddress start + 24 = wordAddress (start + 3) := by
  rw [wordAddress_add]; rfl

private theorem address_four (start : Nat) : wordAddress start + 32 = wordAddress (start + 4) := by
  rw [wordAddress_add]; rfl

private theorem address_twelve (start : Nat) : wordAddress start + 96 = wordAddress (start + 12) := by
  rw [wordAddress_add]; rfl

theorem first_header_memory (state : MachineState) (slot : Fin 16) (start index atWord : Nat)
    (startBound : start + 24 < 2 ^ 61) (wordBound : atWord < 2 ^ 61)
    (source : state.getReg .x10 = wordAddress start) (tag : firstTag index = wordAddress start) :
    memoryView (firstMemory state slot) atWord = writeWindow (memoryView state) start
      (header index (nonceWords state slot)) atWord := by
  have b0 : start < 2 ^ 61 := by omega
  have b1 : start + 1 < 2 ^ 61 := by omega
  have b2 : start + 2 < 2 ^ 61 := by omega
  have b3 : start + 3 < 2 ^ 61 := by omega
  have b4 : start + 4 < 2 ^ 61 := by omega
  unfold firstMemory
  simp only [source, address_one, address_two, address_three, address_four]
  rw [header_as_stores, tag]
  simp only [memory_at_store b4 wordBound, memory_at_store b3 wordBound, memory_at_store b2 wordBound,
    memory_at_store b1 wordBound, memory_at_store b0 wordBound, writeWord]
  simp [nonceWords]

theorem first_call_input (state : MachineState) (slot : Fin 16) (start index : Nat)
    (startBound : start + 24 < 2 ^ 61)
    (source : state.getReg .x10 = wordAddress start) (tag : firstTag index = wordAddress start)
    (firstDisjoint : ∀ offset ∈ ([0, 8, 16] : List Word),
      state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val) ≠ state.getReg .x10 + offset)
    (secondDisjoint : ∀ offset ∈ ([0, 8, 16, 24] : List Word),
      state.getReg .x22 + BitVec.ofNat 64 (16 * slot.val + 8) ≠ state.getReg .x10 + offset) :
    let before := (firstInstructions slot).foldl execInstrBr state
    window (memoryView before) start = firstInput index (nonceWords state slot) (window (memoryView state) (start + 5)) := by
  rw [← first_window]
  funext i
  have execution := (first_execution state slot firstDisjoint secondDisjoint).1
  change ((firstInstructions slot).foldl execInstrBr state).getMem (wordAddress (start + i.val)) = _
  rw [MachineState.getMem, execution]
  change memoryView (firstMemory state slot) (start + i.val) = _
  exact first_header_memory state slot start index (start + i.val) startBound (by omega) source tag

theorem second_call_input (original afterFirst : MachineState) (slot : Fin 16) (start index : Nat)
    (startBound : start + 36 < 2 ^ 61) (nonce : Words 2) (reply : Words 25)
    (source : afterFirst.getReg .x10 = wordAddress start) (tag : firstTag index = wordAddress start)
    (afterMemory : ∀ i < 25, memoryView afterFirst (start + 12 + i) =
      writeWindow (writeWindow (memoryView original) start (header index nonce)) start reply (start + 12 + i)) :
    let before := (secondInstructions slot).foldl execInstrBr afterFirst
    window (memoryView before) (start + 12) = secondInput index reply (window (memoryView original) (start + 5)) := by
  rw [← second_window (memoryView original) start index nonce reply]
  funext i
  have execution := (second_execution afterFirst slot).1
  change ((secondInstructions slot).foldl execInstrBr afterFirst).getMem (wordAddress (start + 12 + i.val)) = _
  rw [MachineState.getMem, execution, source, address_twelve]
  change memoryView (afterFirst.setMem (wordAddress (start + 12)) (wordAddress (start + 12) + 0))
      (start + 12 + i.val) = _
  rw [memory_at_store (by omega) (by omega)]
  have tagAddress : wordAddress (start + 12) + 0 = secondTag index := by
    rw [← address_twelve, ← tag, secondTag, BitVec.add_assoc]
    rfl
  rw [tagAddress]
  simp [window, writeWord, afterMemory i.val i.isLt]

end TwoPermutationPrototype.RV64
