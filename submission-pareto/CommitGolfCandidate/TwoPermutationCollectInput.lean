import CommitGolfCandidate.TwoPermutationCheckRecord
import CommitGolfCandidate.TwoPermutationHonestBytes

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

def checkIndexWord (ordinal : Nat) : Nat := 738198020+ordinal
def checkSourceWord (ordinal : Nat) : Nat := 754975239+32*ordinal
def checkNonceWord (ordinal : Nat) : Nat := 1291846156+66*ordinal

theorem checker_positions_bound (input : CheckInput) : input.positions.card ≤ 16777216 := by
  have card : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  exact card

theorem checker_cap_group (index : Index) : 256 ≤ capGroup index ∧ capGroup index < 512 := by
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
    memoryView state word = memoryView (Assembly.submission.initialState .check input) word

theorem record_input_frame_initial (input : CheckInput) :
    RecordInputFrame input 0 (Assembly.submission.initialState .check input) :=
  fun _ _ _ => rfl

theorem record_input_address_mono (input : CheckInput) (first last word : Nat) (advanced : first ≤ last)
    (used : RecordInputAddress input last word) : RecordInputAddress input first word := by
  rcases used with commitment | indices | source
  · exact Or.inl commitment
  · exact Or.inr (Or.inl indices)
  · exact Or.inr (Or.inr (by unfold checkSourceWord at *; omega))

theorem record_input_address_after (input : CheckInput) (ordinal word : Nat)
    (used : RecordInputAddress input (ordinal+1) word) :
    (word < checkSourceWord ordinal ∨ checkSourceWord ordinal+25 ≤ word) ∧
      (word < 1536 ∨ 1576 ≤ word) := by
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
  have addr : 8*checkIndexWord ordinal = Assembly.submission.layout.indices+8*ordinal := by
    change 8*(738198020+ordinal)=5905584160+8*ordinal
    omega
  change (Assembly.submission.initialState .check input).getMem (BitVec.ofNat 64 (8*checkIndexWord ordinal)) = _
  rw [addr]
  exact (check_input_position input ordinal present).trans (congrArg
    (fun index : Index => BitVec.ofNat 64 index.val) (check_input_value_index input ordinal present).symm)

theorem record_input_value (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (state : MachineState) (framed : RecordInputFrame input ordinal state) :
    readBuffer state (8*(checkSourceWord ordinal+5)) 256 = input.values (honestIndex input.positions ordinal present) := by
  have card := checker_positions_bound input
  have frame := aligned_buffer_frame (Assembly.submission.initialState .check input) state
    (checkSourceWord ordinal+5) 32 (fun j inside => framed _ (by unfold checkSourceWord; omega)
      (Or.inr (Or.inr (by omega))))
  refine frame.trans ?_
  have addr : 8*(checkSourceWord ordinal+5) = Assembly.submission.layout.values+256*ordinal := by
    change 8*(754975239+32*ordinal+5)=6039801952+256*ordinal
    omega
  rw [addr]
  exact check_input_value input ordinal present

theorem record_input_root (input : CheckInput) (ordinal : Nat)
    (state : MachineState) (framed : RecordInputFrame input ordinal state) :
    readBuffer state Assembly.submission.layout.commitment 32 = input.commitment := by
  refine (aligned_digest_frame (Assembly.submission.initialState .check input) state 536871424 ?_).trans
    (check_input_commitment input)
  intro j inside
  exact framed _ (by omega) (Or.inl (by omega))

/-- Registers at the current record or at entry to cap processing. -/
structure RecordCursor (input : CheckInput) (ordinal : Nat) (state : MachineState) : Prop where
  pc : state.pc = if ordinal = input.positions.card then 0x125c else 0x10cc
  index : state.getReg .x8 = wordAddress (checkIndexWord ordinal)
  value : state.getReg .x19 = wordAddress (checkSourceWord ordinal)
  proof : state.getReg .x21 = wordAddress (checkNonceWord ordinal)
  remaining : state.getReg .x18 = BitVec.ofNat 64 (input.positions.card-ordinal)
  tag : state.getReg .x3 = 4056
  commitment : state.getReg .x9 = 4294971392
  challengeLength : state.getReg .x20 = BitVec.ofNat 64 LENGTH
  proofEnd : state.getReg .x22 = BitVec.ofNat 64 (10334769248+input.proof.length)
  digest : state.getReg .x23 = wordAddress 1536
  pair : state.getReg .x24 = wordAddress 1568
  capRoots : state.getReg .x25 = wordAddress 2048
  marks : state.getReg .x26 = wordAddress 512
  capCount : state.getReg .x27 = 256
  selector : state.getReg .x5 = 0

theorem record_cursor_ready (input : CheckInput) (ordinal : Nat) (state : MachineState)
    (current : RecordCursor input ordinal state) (framed : RecordInputFrame input ordinal state)
    (present : ordinal < input.positions.card) :
    CheckRecordReady state (checkSourceWord ordinal) (checkNonceWord ordinal)
      (honestIndex input.positions ordinal present).val := by
  have card := checker_positions_bound input
  refine ⟨?_, ?_, ?_, current.tag, current.value, current.proof, current.digest, current.pair,
    current.challengeLength, current.selector, ?_, ?_, ?_⟩
  · rw [current.pc, ite_eq_right (by omega)]
  · rw [current.index]
    exact aligned_access _ (by unfold checkIndexWord; omega)
  · rw [current.index]
    exact record_input_index input ordinal present state framed
  · unfold checkNonceWord
    omega
  · unfold checkSourceWord checkNonceWord
    omega
  · unfold checkNonceWord
    omega

theorem record_honest_inputs (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (ordinal : Nat) (present : ordinal < positions.card) (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) ordinal state) :
    let index := (honestIndex positions ordinal present).val
    readBuffer state (8*checkNonceWord ordinal) 16 = salts index ∧
      readBuffer state (8*(checkSourceWord ordinal+5)) 256 = message index ∧
      ∀ offset < 16, readBuffer state (8*(checkNonceWord ordinal+2+4*offset)) 32 =
        honestHeap oracle message salts (((LENGTH+index.val)/2^offset) ^^^ 1) := by
  let input := honestCheckInput oracle message positions salts
  let initial := Assembly.submission.initialState .check input
  have cardinal : positions.card ≤ 16777216 := checker_positions_bound input
  have words (offset : Nat) (inside : offset < 66) :
      memoryView state (checkNonceWord ordinal+offset) =
        memoryView initial (checkNonceWord ordinal+offset) := by
    apply framed _ (by unfold checkNonceWord; omega)
    exact Or.inr (Or.inr (by unfold checkSourceWord checkNonceWord; omega))
  refine ⟨?_, record_input_value input ordinal present state framed, ?_⟩
  · refine (aligned_buffer_frame initial state (checkNonceWord ordinal) 2
      (fun k hk => words k (by omega))).trans ?_
    have addr : 8*checkNonceWord ordinal = Assembly.submission.layout.proof+528*ordinal := by
      change 8*(1291846156+66*ordinal)=10334769248+528*ordinal
      omega
    rw [addr]
    exact honest_input_nonce oracle message positions salts ordinal present
  · intro offset inside
    refine (aligned_digest_frame initial state (checkNonceWord ordinal+2+4*offset) ?_).trans ?_
    · intro k small
      simpa only [Nat.add_assoc] using words (2+4*offset+k) (by omega)
    · have addr : 8*(checkNonceWord ordinal+2+4*offset) =
          Assembly.submission.layout.proof+(528*ordinal+16+32*offset) := by
        change 8*(1291846156+66*ordinal+2+4*offset)=10334769248+(528*ordinal+16+32*offset)
        omega
      rw [addr]
      exact honest_input_sibling oracle message positions salts ordinal offset present inside

theorem record_honest_frontier (oracle : Oracle) (message : Message) (positions : Positions) (salts : CompleteSaltTape)
    (state : MachineState)
    (framed : RecordInputFrame (honestCheckInput oracle message positions salts) positions.card state)
    (ordinal : Nat) (present : ordinal < (Opening.openingNodes positions).length) :
    readBuffer state (8*(checkNonceWord positions.card+4*ordinal)) 32 =
      honestHeap oracle message salts (Opening.openingNodes positions)[ordinal] := by
  let input := honestCheckInput oracle message positions salts
  let initial := Assembly.submission.initialState .check input
  have cardinal : positions.card ≤ 16777216 := checker_positions_bound input
  have maximum : (Opening.openingNodes positions).length ≤ 128 := Opening.opening_nodes_bound positions
  refine (aligned_digest_frame initial state _ ?_).trans ?_
  · intro j small
    exact framed _ (by unfold checkNonceWord; omega) (Or.inr (Or.inr (by
      unfold checkSourceWord checkNonceWord
      omega)))
  · have addr : 8*(checkNonceWord positions.card+4*ordinal) =
        Assembly.submission.layout.proof+(528*positions.card+32*ordinal) := by
      change 8*(1291846156+66*positions.card+4*ordinal)=10334769248+(528*positions.card+32*ordinal)
      omega
    rw [addr]
    exact honest_input_frontier oracle message positions salts ordinal present

end TwoPermutationPrototype.Checker
