import CommitGolfCandidate.TwoPermutationLeafFetch

/-! A leaf makes its first call in the source buffer and writes its second
200-byte answer to the destination. Only its first four heap words persist
as a digest. The frame states exactly which other words survive both writes. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

structure LeafReady (s : MachineState) (slot : Fin 16) (start index dst salts : Nat) : Prop where
  source : s.getReg .x10 = wordAddress start
  destination : s.getReg .x20 + BitVec.ofNat 64 (32 * slot.val) = wordAddress dst
  nonces : s.getReg .x22 = wordAddress salts
  tag : firstTag index = wordAddress start
  sourceBound : start + 37 ≤ 2 ^ 33
  heapBound : dst + 25 ≤ 2 ^ 33
  nonceBound : salts + 32 ≤ 2 ^ 33
  separate : start + 37 ≤ salts
  selector : s.getReg .x5 = 0
  size : s.getReg .x11 = 200
  primitive : s.getReg .x13 = 1

def preparedA (s : MachineState) (slot : Fin 16) := (firstInstructions slot).foldl execInstrBr s
def repliedA (s : MachineState) (slot : Fin 16) (start : Nat) (answer : BitVec 1600) :=
  writeBits (preparedA s slot) (wordAddress start) answer
def preparedB (s : MachineState) (slot : Fin 16) (start : Nat) (a : BitVec 1600) :=
  (secondInstructions slot).foldl execInstrBr (repliedA s slot start a)
def repliedB (s : MachineState) (slot : Fin 16) (start dst : Nat) (a b : BitVec 1600) :=
  writeBits (preparedB s slot start a) (wordAddress dst) b
def finishedLeaf (s : MachineState) (slot : Fin 16) (start dst : Nat) (a b : BitVec 1600) :=
  execInstrBr (repliedB s slot start dst a b) (.ADDI .x10 .x10 160)

theorem leaf_nonce_separate (s : MachineState) (slot : Fin 16) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) :
    (∀ offset ∈ ([0,8,16] : List Word), s.getReg .x22 + BitVec.ofNat 64 (16*slot.val) ≠ s.getReg .x10 + offset) ∧
    (∀ offset ∈ ([0,8,16,24] : List Word), s.getReg .x22 + BitVec.ofNat 64 (16*slot.val+8) ≠ s.getReg .x10 + offset) := by
  have small := slot.isLt
  have src := ready.sourceBound
  have bound := ready.nonceBound
  have sep := ready.separate
  have distinct (a b : Nat) (ha : a ≤ 16*slot.val+8) (hb : b ≤ 24) :
      wordAddress salts + BitVec.ofNat 64 a ≠ wordAddress start + BitVec.ofNat 64 b := by
    unfold wordAddress
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add]
    intro equal
    have num := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at num
    rw [Nat.mod_eq_of_lt (by omega : 8*salts+a < 2^64),
      Nat.mod_eq_of_lt (by omega : 8*start+b < 2^64)] at num
    omega
  rw [ready.nonces,ready.source]
  constructor <;> intro offset present <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  · rcases present with rfl | rfl | rfl <;> apply distinct _ _ (by omega) (by decide)
  · rcases present with rfl | rfl | rfl | rfl <;> apply distinct _ _ (by omega) (by decide)

theorem after_a_memory (s : MachineState) (slot : Fin 16) (start index dst salts word : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (bounded : word < 2^33) :
    memoryView (repliedA s slot start a) word =
      writeWindow (writeWindow (memoryView s) start (header index (nonceWords s slot)))
        start (replyWords a) word := by
  obtain ⟨d0,d1⟩ := leaf_nonce_separate _ _ _ _ _ _ ready
  have memory := (first_execution s slot d0 d1).1
  have sourceBound := ready.sourceBound
  unfold repliedA
  rw [permutation_write_memory _ _ _ _ (by omega) bounded]
  by_cases covered : start ≤ word ∧ word < start + 25
  · simp only [writeWindow,dite_eq_left covered]
  · simp only [writeWindow,dite_eq_right covered]
    change (preparedA s slot).mem (wordAddress word) = _
    rw [show (preparedA s slot).mem = (firstMemory s slot).mem from memory]
    exact first_header_memory s slot start index word (by omega) (by omega) ready.source ready.tag

theorem after_a_input_cursor (s : MachineState) (slot : Fin 16) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    (repliedA s slot start a).getReg .x10 = wordAddress start := by
  obtain ⟨d0,d1⟩ := leaf_nonce_separate _ _ _ _ _ _ ready
  rw [repliedA,CommitGolfCandidate.writeBits_register]
  exact (first_execution s slot d0 d1).2.1.trans ready.source

theorem after_b_input (s : MachineState) (slot : Fin 16) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) :
    window (memoryView (preparedB s slot start a)) (start+12) =
      secondInput index (replyWords a) (window (memoryView s) (start+5)) := by
  have bound := ready.sourceBound
  exact second_call_input s (repliedA s slot start a) slot start index (by omega) (nonceWords s slot)
    (replyWords a) (after_a_input_cursor _ _ _ _ _ _ ready _) ready.tag
    (fun i hi => after_a_memory s slot start index dst salts _ ready a (by omega))

def leafWrites (mem : Memory) (slotNonce : Words 2) (start index dst : Nat)
    (a b : BitVec 1600) : Memory :=
  writeWindow (writeWord (writeWindow (writeWindow mem start (header index slotNonce)) start (replyWords a))
    (start+12) (secondTag index)) dst (replyWords b)

theorem finished_leaf_memory (s : MachineState) (slot : Fin 16) (start index dst salts word : Nat)
    (ready : LeafReady s slot start index dst salts) (a b : BitVec 1600) (bounded : word < 2^33) :
    memoryView (finishedLeaf s slot start dst a b) word =
      leafWrites (memoryView s) (nonceWords s slot) start index dst a b word := by
  have sb := ready.sourceBound
  have x10 := after_a_input_cursor _ _ _ _ _ _ ready a
  change memoryView (writeBits (preparedB s slot start a) (wordAddress dst) b) word = _
  rw [permutation_write_memory _ _ _ _ ready.heapBound bounded]
  by_cases inside : dst ≤ word ∧ word < dst+25
  · simp only [leafWrites,writeWindow,dite_eq_left inside]
  · simp only [leafWrites,writeWindow,dite_eq_right inside]
    have pre := (second_execution (repliedA s slot start a) slot).1
    change (preparedB s slot start a).mem (wordAddress word) = _
    rw [show (preparedB s slot start a).mem = _ from pre, x10,
      show wordAddress start + 96 = wordAddress (start+12) by rw [wordAddress_add];rfl]
    change memoryView ((repliedA s slot start a).setMem (wordAddress (start+12)) (wordAddress (start+12)+0)) word = _
    rw [memory_at_store (by omega) (by omega)]
    have tag : wordAddress (start+12)+0 = secondTag index := by
      rw [wordAddress_add,secondTag,ready.tag,BitVec.add_assoc]
      rfl
    simp only [writeWord,tag,after_a_memory _ _ _ _ _ _ _ ready a bounded]

theorem leaf_digest_words (mem : Memory) (n : Words 2) (start index dst : Nat) (a b : BitVec 1600) :
    window (leafWrites mem n start index dst a b) dst = lowDigest (replyWords b) := by
  funext i
  have inside : dst ≤ dst + i.val ∧ dst+i.val < dst+25 := by have := i.isLt;omega
  simp [leafWrites,window,writeWindow,lowDigest,inside]

theorem leaf_word_outside (mem : Memory) (n : Words 2) (start index dst word : Nat) (a b : BitVec 1600)
    (sourceOut : word < start ∨ start+25 ≤ word) (heapOut : word < dst ∨ dst+25 ≤ word) :
    leafWrites mem n start index dst a b word = mem word := by
  have d : ¬ (dst ≤ word ∧ word < dst+25) := by omega
  have m : ¬ (start ≤ word ∧ word < start+25) := by omega
  have h : ¬ (start ≤ word ∧ word < start+5) := by omega
  have t : word ≠ start+12 := by omega
  simp [leafWrites,writeWindow,writeWord,d,m,h,t]

end TwoPermutationPrototype.RV64
