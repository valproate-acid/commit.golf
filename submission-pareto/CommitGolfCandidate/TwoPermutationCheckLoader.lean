import CommitGolfCandidate.TwoPermutationSubmission
import CommitGolfCandidate.InputOrder

/-! The trusted loader serializes check inputs into the production layout.
The executable checker proofs use these exact memory and register facts. -/
namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private theorem positions_card_bound (positions : Positions) : positions.card ≤ 2^24 := by
  have bound : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  exact bound

theorem check_initial_registers (input : CheckInput) :
    let state := Assembly.submission.initialState .check input
    state.pc = 4096 ∧
    state.getReg .x11 = 4294971392 ∧
    state.getReg .x13 = 5905584160 ∧
    state.getReg .x14 = 6039801952 ∧
    state.getReg .x15 = 10334769248 ∧
    state.getReg .x16 = BitVec.ofNat 64 input.positions.card ∧
    state.getReg .x17 = BitVec.ofNat 64 input.proof.length :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem check_run_admitted (input : CheckInput)
    (admitted : input.proof.length ≤ Assembly.submission.sizes.proof) :
    Assembly.submission.run .check input =
      execute checkerImage 17179934720 (Assembly.submission.initialState .check input) false := by
  simp only [Submission.run,admitted,decide_true,ite_true]
  rfl

theorem check_run_oversized (input : CheckInput)
    (oversized : Assembly.submission.sizes.proof < input.proof.length) :
    Assembly.submission.run .check input = pure ⟨.failure,initialMachine,0,0⟩ := by
  have rejected := Nat.not_le.mpr oversized
  simp only [Submission.run,rejected,decide_false,Bool.false_eq_true,ite_false]

theorem check_scratch_word_zero (input : CheckInput) (address : Nat)
    (below : address+8 ≤ 4294971392) :
    (Assembly.submission.initialState .check input).getMem (BitVec.ofNat 64 address) = 0 := by
  rw [initial_input_word Assembly.submission .check input _ (by omega)]
  have zero (offset : Nat) (inside : offset < 8) :
      inputByte Assembly.submission .check input (address+offset) = 0 := by
    have commitment : ¬ Assembly.submission.layout.commitment ≤ address+offset := by
      change ¬ 4294971392 ≤ address+offset
      omega
    have indices : ¬ Assembly.submission.layout.indices ≤ address+offset := by
      change ¬ 5905584160 ≤ address+offset
      omega
    have values : ¬ Assembly.submission.layout.values ≤ address+offset := by
      change ¬ 6039801952 ≤ address+offset
      omega
    have proof : ¬ Assembly.submission.layout.proof ≤ address+offset := by
      change ¬ 10334769248 ≤ address+offset
      omega
    have data : (Assembly.submission.image .check).data = [] := rfl
    simp [inputByte, Submission.inputBuffers, fixedBuffer, positionsBuffer, valuesBuffer,
      commitment, indices, values, proof, data]
  have sumZero : (∑ j ∈ Finset.range 8,
      (inputByte Assembly.submission .check input (address+j)).toNat * 2^(8*j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j member
    rw [zero j (Finset.mem_range.mp member)]
    simp
  rw [sumZero]
  rfl

theorem check_mark_zero (input : CheckInput) (node : Nat) (inside : node < 512) :
    (Assembly.submission.initialState .check input).getMem
      (BitVec.ofNat 64 (8*(512+node))) = 0 :=
  check_scratch_word_zero input _ (by omega)

/-- The checker sees exactly the submitted commitment. -/
theorem check_input_commitment (input : CheckInput) :
    readBuffer (Assembly.submission.initialState .check input) Assembly.submission.layout.commitment 32 =
      input.commitment := by
  have decoded := read_serialized_slice (Assembly.submission.initialState .check input) input.commitment
    Assembly.submission.layout.commitment 0 32 (by
      intro j hj
      rw [initial_input_byte Assembly.submission .check input _ (by change 4294971392+j < 2^64; omega)]
      have selected : Assembly.submission.layout.commitment ≤ Assembly.submission.layout.commitment+j ∧
          Assembly.submission.layout.commitment+j < Assembly.submission.layout.commitment+(DIGEST_BITS+7)/8 := by
        change _ ≤ _ ∧ _ < Assembly.submission.layout.commitment+32
        omega
      simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
        selected, and_self, decide_true, Nat.add_sub_cancel_left, Nat.zero_add])
  exact decoded.trans BitVec.extractLsb'_eq_self

/-- Every proof byte accepted by the ABI is loaded at the proof buffer address. -/
theorem check_input_proof_byte (input : CheckInput)
    (valid : input.proof.length ≤ Assembly.submission.sizes.proof) (offset : Nat)
    (inside : offset < input.proof.length) :
    (Assembly.submission.initialState .check input).getByte
      (BitVec.ofNat 64 (Assembly.submission.layout.proof+offset)) = input.proof[offset] := by
  have cardinal := positions_card_bound input.positions
  rw [initial_input_byte Assembly.submission .check input _ (by
    change 10334769248+offset < 2^64
    change input.proof.length ≤ 8858378240 at valid
    omega)]
  have outsideRoot : ¬ (Assembly.submission.layout.commitment ≤ Assembly.submission.layout.proof+offset ∧
      Assembly.submission.layout.proof+offset < Assembly.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ 10334769248+offset ∧ 10334769248+offset < 4294971424)
    omega
  have outsideIndices : ¬ (Assembly.submission.layout.indices ≤ Assembly.submission.layout.proof+offset ∧
      Assembly.submission.layout.proof+offset < Assembly.submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160 ≤ 10334769248+offset ∧ 10334769248+offset < 5905584160+8*input.positions.card)
    omega
  have outsideValues : ¬ (Assembly.submission.layout.values ≤ Assembly.submission.layout.proof+offset ∧
      Assembly.submission.layout.proof+offset < Assembly.submission.layout.values+(LEAF_SIZE/8)*input.positions.card) := by
    change ¬ (6039801952 ≤ 10334769248+offset ∧ 10334769248+offset < 6039801952+256*input.positions.card)
    omega
  have selected : Assembly.submission.layout.proof ≤ Assembly.submission.layout.proof+offset ∧
      Assembly.submission.layout.proof+offset < Assembly.submission.layout.proof+input.proof.length := by omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
    outsideRoot, outsideIndices, outsideValues, decide_false, selected, and_self, decide_true,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem inside, Option.getD_some]

/-- A proof slice is decoded from the exact bytes supplied to the trusted loader. -/
theorem check_input_proof_slice (input : CheckInput)
    (valid : input.proof.length ≤ Assembly.submission.sizes.proof) (offset count : Nat)
    (inside : offset+count ≤ input.proof.length) :
    readBuffer (Assembly.submission.initialState .check input) (Assembly.submission.layout.proof+offset) count =
      BitVec.ofNat (8*count) (∑ j ∈ Finset.range count,
        (input.proof[offset+j]?.getD 0).toNat * 2^(8*j)) := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro j hj
  have bounded : offset+j < input.proof.length := by have := Finset.mem_range.mp hj; omega
  rw [Nat.add_assoc, check_input_proof_byte input valid (offset+j) bounded,
    List.getElem?_eq_getElem bounded, Option.getD_some]

theorem check_input_proof_digest (input : CheckInput)
    (valid : input.proof.length ≤ Assembly.submission.sizes.proof) (offset : Nat)
    (inside : offset+32 ≤ input.proof.length) :
    readBuffer (Assembly.submission.initialState .check input) (Assembly.submission.layout.proof+offset) 32 =
      BitVec.ofNat 256 (∑ j ∈ Finset.range 32,
        (input.proof[offset+j]?.getD 0).toNat * 2^(8*j)) :=
  check_input_proof_slice input valid offset 32 inside

theorem check_loader_bounds (input : CheckInput) (admitted : input.proof.length ≤ Assembly.submission.sizes.proof) :
    input.positions.card ≤ LENGTH ∧ input.proof.length < 2^64 ∧
    Assembly.submission.layout.indices+8*input.positions.card ≤ Assembly.submission.layout.values ∧
    Assembly.submission.layout.values+256*input.positions.card ≤ Assembly.submission.layout.proof ∧
    Assembly.submission.layout.proof+input.proof.length ≤ MEMORY_BYTES := by
  have cardinal := positions_card_bound input.positions
  change input.proof.length ≤ 8858378240 at admitted
  change input.positions.card ≤ 16777216 ∧ input.proof.length < 2^64 ∧
    5905584160+8*input.positions.card ≤ 6039801952 ∧
    6039801952+256*input.positions.card ≤ 10334769248 ∧
    10334769248+input.proof.length ≤ 68719476736
  omega

/-- The checker receives the caller's leaf values in the ABI's sorted order. -/
theorem check_input_value_byte (input : CheckInput) (ordinal offset : Nat)
    (present : ordinal < input.positions.card) (inside : offset < 256) :
    (Assembly.submission.initialState .check input).getByte
      (BitVec.ofNat 64 (Assembly.submission.layout.values+256*ordinal+offset)) =
      (input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present))).extractLsb' (8*offset) 8 := by
  have cardinal := positions_card_bound input.positions
  rw [initial_input_byte Assembly.submission .check input _ (by
    change 6039801952+256*ordinal+offset < 2^64
    omega)]
  have outsideRoot : ¬ (Assembly.submission.layout.commitment ≤ Assembly.submission.layout.values+256*ordinal+offset ∧
      Assembly.submission.layout.values+256*ordinal+offset < Assembly.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
    change ¬ (4294971392 ≤ 6039801952+256*ordinal+offset ∧ 6039801952+256*ordinal+offset < 4294971424)
    omega
  have outsideIndices : ¬ (Assembly.submission.layout.indices ≤ Assembly.submission.layout.values+256*ordinal+offset ∧
      Assembly.submission.layout.values+256*ordinal+offset < Assembly.submission.layout.indices+8*input.positions.card) := by
    change ¬ (5905584160 ≤ 6039801952+256*ordinal+offset ∧
      6039801952+256*ordinal+offset < 5905584160+8*input.positions.card)
    omega
  have selected : Assembly.submission.layout.values ≤ Assembly.submission.layout.values+256*ordinal+offset ∧
      Assembly.submission.layout.values+256*ordinal+offset < Assembly.submission.layout.values+(LEAF_SIZE/8)*input.positions.card := by
    change _ ≤ _ ∧ _ < Assembly.submission.layout.values+256*input.positions.card
    omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, Finset.length_sort, Finset.card_attach,
    outsideRoot, outsideIndices, decide_false, selected, and_self, decide_true]
  have quotient : (Assembly.submission.layout.values+256*ordinal+offset-Assembly.submission.layout.values)/(LEAF_SIZE/8) = ordinal := by
    change _ / 256 = _
    omega
  have remainder : (Assembly.submission.layout.values+256*ordinal+offset-Assembly.submission.layout.values)%(LEAF_SIZE/8) = offset := by
    change _ % 256 = _
    omega
  rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]

theorem check_input_value (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) :
    readBuffer (Assembly.submission.initialState .check input)
      (Assembly.submission.layout.values + 256*ordinal) 256 =
      input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
        simpa using present)) := by
  let value := input.values ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by
    simpa using present))
  have decoded := read_serialized_slice (Assembly.submission.initialState .check input)
    value (Assembly.submission.layout.values + 256*ordinal) 0 256 (by
      intro j inside
      simpa only [Nat.zero_add] using check_input_value_byte input ordinal j present inside)
  exact decoded.trans BitVec.extractLsb'_eq_self

theorem check_input_value_index (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) :
    ((input.positions.attach.sort (fun i j => i.val ≤ j.val))[ordinal]'(by simpa using present)).val =
    (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present) := by
  apply Fin.ext
  simpa only [openingIndex, dite_eq_left present] using
    sorted_value_index input.positions ordinal present

private theorem read_word (state : MachineState) (address : Nat) (aligned : address%8 = 0) :
    readBuffer state address 8 = state.getMem (BitVec.ofNat 64 address) := by
  have slice := read_buffer_slice state address 32 0 8 (by decide)
  have word := read_digest_word state address 0 aligned (by decide)
  simpa only [Nat.mul_zero, Nat.add_zero] using slice.symm.trans word

/-- The checker's serialized index word is the same position selected by opening. -/
theorem check_input_position (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) :
    (Assembly.submission.initialState .check input).getMem
      (BitVec.ofNat 64 (Assembly.submission.layout.indices+8*ordinal)) =
        BitVec.ofNat 64 ((input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)).val := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have small : input.positions.card ≤ 16777216 := cardinal
  let index := (input.positions.sort (· ≤ ·))[ordinal]'(by simpa using present)
  have indexBound : index.val < 16777216 := index.isLt
  have bytes (offset : Nat) (inside : offset < 8) :
      (Assembly.submission.initialState .check input).getByte
        (BitVec.ofNat 64 (Assembly.submission.layout.indices+8*ordinal+offset)) =
          (BitVec.ofNat 64 index.val).extractLsb' (8*offset) 8 := by
    rw [initial_input_byte Assembly.submission .check input _ (by change 5905584160+8*ordinal+offset < 2^64; omega)]
    have outside : ¬ (Assembly.submission.layout.commitment ≤ Assembly.submission.layout.indices+8*ordinal+offset ∧
        Assembly.submission.layout.indices+8*ordinal+offset < Assembly.submission.layout.commitment+(DIGEST_BITS+7)/8) := by
      change ¬ (4294971392 ≤ 5905584160+8*ordinal+offset ∧
        5905584160+8*ordinal+offset < 4294971424)
      omega
    have selected : Assembly.submission.layout.indices ≤ Assembly.submission.layout.indices+8*ordinal+offset ∧
        Assembly.submission.layout.indices+8*ordinal+offset <
          Assembly.submission.layout.indices+8*(input.positions.sort (· ≤ ·)).length := by
      rw [Finset.length_sort]; omega
    simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer, positionsBuffer,
      outside, decide_false, selected, and_self, decide_true]
    have quotient : (Assembly.submission.layout.indices+8*ordinal+offset-Assembly.submission.layout.indices)/8 = ordinal := by omega
    have remainder : (Assembly.submission.layout.indices+8*ordinal+offset-Assembly.submission.layout.indices)%8 = offset := by omega
    rw [quotient, remainder, List.getElem?_eq_getElem (by simpa using present)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb', Nat.shiftRight_eq_div_pow,
      Nat.mod_eq_of_lt (by omega : index.val < 2^64)]
    rfl
  have decoded := read_serialized_slice (Assembly.submission.initialState .check input)
    (BitVec.ofNat 64 index.val) (Assembly.submission.layout.indices+8*ordinal) 0 8 (by
      simpa only [Nat.zero_add] using bytes)
  rw [read_word _ _ (by change (5905584160+8*ordinal)%8 = 0; omega)] at decoded
  change (Assembly.submission.initialState .check input).getMem
    (BitVec.ofNat 64 (Assembly.submission.layout.indices+8*ordinal)) =
      (BitVec.ofNat 64 index.val).extractLsb' 0 64 at decoded
  rw [BitVec.extractLsb'_eq_self] at decoded
  exact decoded

end TwoPermutationPrototype.Checker
