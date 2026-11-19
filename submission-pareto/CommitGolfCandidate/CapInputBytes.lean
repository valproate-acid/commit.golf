import CommitGolfCandidate.CapExperimentalABI
import CommitGolfCandidate.CapByteSlots

/-! Exact proof bytes selected by the experimental check ABI. All positions and
values remain arbitrary. The proof's full byte length is retained; a trailing
partial digest is neither rounded down nor omitted by this loader bridge. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096

theorem cap_check_input_proof_byte (input : CheckInput) (offset : Nat)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (inside : offset < input.proof.length) :
    (capProgram.initialState .check input).getByte
      (BitVec.ofNat 64 (capProgram.layout.proof + offset)) = input.proof[offset]?.getD 0 := by
  have cardinal : input.positions.card ≤ LENGTH := by
    simpa [Index] using Finset.card_le_univ input.positions
  have bounded := (cap_check_loader_bounds input admitted).2.2
  rw [initial_input_byte capProgram .check input _ (by omega)]
  have outsideCommit : ¬ (capProgram.layout.commitment ≤ capProgram.layout.proof + offset ∧
      capProgram.layout.proof + offset < capProgram.layout.commitment + (DIGEST_BITS+7)/8) := by
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes, LENGTH,
      LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES, DIGEST_BITS]
    omega
  have outsideIndices : ¬ (capProgram.layout.indices ≤ capProgram.layout.proof + offset ∧
      capProgram.layout.proof + offset <
        capProgram.layout.indices + 8 * (input.positions.sort (· ≤ ·)).length) := by
    rw [Finset.length_sort]
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  have outsideValues : ¬ (capProgram.layout.values ≤ capProgram.layout.proof + offset ∧
      capProgram.layout.proof + offset < capProgram.layout.values +
        (LEAF_SIZE/8) * (input.positions.attach.sort (fun i j => i.val ≤ j.val)).length) := by
    rw [Finset.length_sort, Finset.card_attach]
    norm_num [capProgram, capExperimental, candidate, layout, trapdoorBytes,
      LENGTH, LOG_LENGTH, LEAF_SIZE, DIGEST_BYTES] at cardinal ⊢
    omega
  have selected : capProgram.layout.proof ≤ capProgram.layout.proof + offset ∧
      capProgram.layout.proof + offset < capProgram.layout.proof + input.proof.length := by omega
  simp only [inputByte, Submission.inputBuffers, List.find?_cons, fixedBuffer,
    positionsBuffer, valuesBuffer, outsideCommit, outsideIndices, outsideValues,
    decide_false, selected, and_self, decide_true, Nat.add_sub_cancel_left]

/-- A complete encoded digest slot is read exactly from the actual proof buffer.
The byte suffix remains present in the admitted input and final length checks. -/
theorem cap_check_encoded_slot (input : CheckInput) (digests : List Digest) (suffix : Proof)
    (encoded : input.proof = capDigestEncoding digests ++ suffix)
    (admitted : input.proof.length ≤ capProgram.sizes.proof)
    (ordinal : Nat) (present : ordinal < digests.length) :
    readBuffer (capProgram.initialState .check input)
      (capProgram.layout.proof + 32 * ordinal) 32 = digests[ordinal] := by
  apply cap_encoding_read _ digests suffix _ ordinal present
  intro offset inside
  erw [Nat.add_assoc, cap_check_input_proof_byte input _ admitted]
  · rw [encoded]
  · rw [encoded, List.length_append, cap_digest_encoding_length]
    omega
end CommitGolfCandidate
