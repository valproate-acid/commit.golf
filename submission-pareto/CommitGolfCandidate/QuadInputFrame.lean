import CommitGolfCandidate.QuadCheckLoader
import CommitGolfCandidate.TwoPermutationCollectInput

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

open TwoPermutationPrototype.Checker (honestIndex aligned_buffer_frame aligned_digest_frame)

/-- Penta records: 1424 bytes per opened position (salt and 11 × 4 siblings). -/
def checkProofByte (ordinal : Nat) : Nat := 10804535392+1424*ordinal

def checkIndexWord (ordinal : Nat) : Nat := 796918788+ordinal
def checkSourceWord (ordinal : Nat) : Nat := 813696007+32*ordinal

theorem checker_positions_bound (input : CheckInput) : input.positions.card ≤ 16777216 := by
  have card : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  exact card

theorem checker_cap_group (index : Index) : 256 ≤ Sampling.capGroup index ∧ Sampling.capGroup index < 512 := by
  have bound : index.val < 16777216 := index.isLt
  change 256 ≤ (16777216+index.val)/65536 ∧ (16777216+index.val)/65536 < 512
  omega

/-- Regions the remaining records or cap traversal can still read. -/
def RecordInputAddress (input : CheckInput) (ordinal word : Nat) : Prop :=
  (536871424 ≤ word ∧ word < 536871428) ∨
    (checkIndexWord 0 ≤ word ∧ word < checkIndexWord input.positions.card) ∨
    checkSourceWord ordinal ≤ word

def RecordInputFrame (input : CheckInput) (ordinal : Nat) (state : MachineState) : Prop :=
  ∀ word < 2^33, RecordInputAddress input ordinal word →
    memoryView state word = memoryView (loaderReference.initialState .check input) word

theorem record_input_frame_initial (input : CheckInput) :
    RecordInputFrame input 0 (loaderReference.initialState .check input) :=
  fun _ _ _ => rfl

theorem record_input_address_mono (input : CheckInput) (first last word : Nat) (advanced : first ≤ last)
    (used : RecordInputAddress input last word) : RecordInputAddress input first word := by
  rcases used with commitment | indices | source
  · exact Or.inl commitment
  · exact Or.inr (Or.inl indices)
  · exact Or.inr (Or.inr (by unfold checkSourceWord at *; omega))

theorem record_input_address_after (input : CheckInput) (ordinal word : Nat)
    (used : RecordInputAddress input (ordinal+1) word) :
    (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) ∧
      1625 ≤ word := by
  have card := checker_positions_bound input
  rcases used with ⟨first, last⟩ | ⟨first, last⟩ | source
  · unfold checkSourceWord
    omega
  · unfold checkIndexWord at first last
    unfold checkSourceWord
    omega
  · unfold checkSourceWord at *
    omega

theorem record_input_frame_step (input : CheckInput) (ordinal : Nat) (before after : MachineState)
    (previous : RecordInputFrame input ordinal before)
    (words : ∀ word < 2^33, RecordInputAddress input (ordinal+1) word →
      memoryView after word = memoryView before word) :
    RecordInputFrame input (ordinal+1) after := by
  intro word bounded used
  exact (words word bounded used).trans
    (previous word bounded (record_input_address_mono input ordinal (ordinal+1) word (by omega) used))

theorem record_input_index (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state : MachineState) (framed : RecordInputFrame input ordinal state) :
    memoryView state (checkIndexWord ordinal) = BitVec.ofNat 64 (honestIndex input.positions ordinal present).val.val := by
  have card := checker_positions_bound input
  rw [framed _ (by unfold checkIndexWord; omega) (Or.inr (Or.inl (by
    unfold checkIndexWord
    omega)))]
  have addr : 8*checkIndexWord ordinal = loaderReference.layout.indices+8*ordinal := by
    change 8*(796918788+ordinal)=6375350304+8*ordinal
    omega
  change (loaderReference.initialState .check input).getMem (BitVec.ofNat 64 (8*checkIndexWord ordinal)) = _
  rw [addr]
  exact (check_input_position input ordinal present).trans (congrArg
    (fun index : Index => BitVec.ofNat 64 index.val) (check_input_value_index input ordinal present).symm)

theorem record_input_value (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state : MachineState) (framed : RecordInputFrame input ordinal state) :
    readBuffer state (8*(checkSourceWord ordinal+5)) 256 = input.values (honestIndex input.positions ordinal present) := by
  have card := checker_positions_bound input
  have frame := aligned_buffer_frame (loaderReference.initialState .check input) state
    (checkSourceWord ordinal+5) 32 (fun j inside => framed _ (by unfold checkSourceWord; omega)
      (Or.inr (Or.inr (by omega))))
  refine frame.trans ?_
  have addr : 8*(checkSourceWord ordinal+5) = loaderReference.layout.values+256*ordinal := by
    change 8*(813696007+32*ordinal+5)=6509568096+256*ordinal
    omega
  rw [addr]
  exact check_input_value input ordinal present

theorem record_input_root (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (framed : RecordInputFrame input ordinal state) :
    readBuffer state loaderReference.layout.commitment 32 = input.commitment := by
  refine (aligned_digest_frame (loaderReference.initialState .check input) state 536871424 ?_).trans
    (check_input_commitment input)
  intro j inside
  exact framed _ (by omega) (Or.inl (by omega))

/-- The quad checker cursor points to 8-aligned 1424-byte records. -/
structure RecordCursor (input : CheckInput) (ordinal : Nat) (state : MachineState) : Prop where
  pc : state.pc = if ordinal = input.positions.card then 0x1444 else 0x1058
  index : state.getReg .x8 = wordAddress (checkIndexWord ordinal)
  value : state.getReg .x19 = wordAddress (checkSourceWord ordinal)
  proof : state.getReg .x21 = BitVec.ofNat 64 (checkProofByte ordinal)
  remaining : state.getReg .x18 = BitVec.ofNat 64 (input.positions.card-ordinal)
  tag : state.getReg .x3 = 4056
  commitment : state.getReg .x9 = 4294971392
  challengeLength : state.getReg .x20 = BitVec.ofNat 64 LENGTH
  proofEnd : state.getReg .x22 = BitVec.ofNat 64 (10804535392+input.proof.length)
  digest : state.getReg .x23 = wordAddress 1536
  pair : state.getReg .x24 = wordAddress 1568
  capRoots : state.getReg .x25 = wordAddress 2048
  marks : state.getReg .x26 = wordAddress 512
  capCount : state.getReg .x27 = 256
  selector : state.getReg .x5 = 0
  nonceScratch : state.getReg .x4 = 12272

/-- Packed records and their footer may begin between two consecutive aligned words. -/
theorem byte_frame (before after : MachineState) (address : Nat)
    (unchanged : memoryView after (address/8) = memoryView before (address/8)) :
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address) := by
  have addr : 8*(address/8)+address%8=address := by omega
  have fit : address%8<64 := by omega
  have a := aligned_byte after (address/8) (address%8) fit
  have b := aligned_byte before (address/8) (address%8) fit
  rw [addr, Nat.div_eq_of_lt (show address%8<8 from by omega), Nat.mul_zero, Nat.add_zero] at a b
  rw [a,b]
  exact congrArg (fun word : Word => extractByte word (address%8%8)) unchanged

theorem buffer_byte_frame (before after : MachineState) (address count : Nat)
    (unchanged : ∀ j < count, memoryView after ((address+j)/8) = memoryView before ((address+j)/8)) :
    readBuffer after address count = readBuffer before address count := by
  unfold readBuffer
  congr 1
  apply Finset.sum_congr rfl
  intro j inside
  rw [byte_frame before after _ (unchanged j (Finset.mem_range.mp inside))]

theorem packed_input_address_after (input : CheckInput) (ordinal word : Nat)
    (used : RecordInputAddress input (ordinal+1) word) :
    (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+26 ≤ word) ∧
      1625 ≤ word := by
  have card := checker_positions_bound input
  rcases used with ⟨first, last⟩ | ⟨first, last⟩ | source
  · unfold checkSourceWord
    omega
  · unfold checkIndexWord at first last
    unfold checkSourceWord
    omega
  · unfold checkSourceWord at *
    omega

theorem record_proof_frame (input : CheckInput) (ordinal offset count : Nat) (state : MachineState)
    (frame : RecordInputFrame input ordinal state) (before : ordinal ≤ input.positions.card)
    (bounded : checkProofByte ordinal+offset+count ≤ 2^36) :
    readBuffer state (checkProofByte ordinal+offset) count =
      readBuffer (loaderReference.initialState .check input) (checkProofByte ordinal+offset) count := by
  apply buffer_byte_frame
  intro j inside
  have card := checker_positions_bound input
  apply frame _ (by omega)
  exact Or.inr (Or.inr (by unfold checkSourceWord checkProofByte; omega))


end TwoPermutationPrototype.Quad.Checker
