import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.TwoPermutationPackedRecordLeafPrelude
import CommitGolfCandidate.TwoPermutationPackedRecordLeafCalls
import CommitGolfCandidate.TwoPermutationPackedRecordComposition

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (RecordInputFrame honestIndex checkSourceWord
  checker_positions_bound aligned_buffer_frame buffer_window checker_value_data record_input_value
  beginRecord record_setup_register)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000

theorem staged_entry_words (input : CheckInput) (ordinal : Nat) (present : ordinal < input.positions.card)
    (before : MachineState) (fits : ProofWithin input) (cursor : RecordCursor input ordinal before)
    (framed : RecordInputFrame input ordinal before) :
    window (memoryView (staged before)) (checkSourceWord ordinal+5) =
      entryWords (input.values (honestIndex input.positions ordinal present)) := by
  let item := honestIndex input.positions ordinal present
  have card := checker_positions_bound input
  have stable := aligned_buffer_frame before (staged before) (checkSourceWord ordinal+5) 32 (by
    intro j within
    apply staged_word_frame input ordinal present before fits cursor
    · unfold checkSourceWord
      omega
    · exact Or.inr (by unfold checkSourceWord; omega))
  exact checker_value_data (fun _ => input.values item) item.val
    (stable.trans (record_input_value input ordinal present before framed))

theorem staged_honest_nonce_words (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (before : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal before) (framed : RecordInputFrame input ordinal before)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    checkerNonce (staged before) = saltWords (salts (honestIndex input.positions ordinal present)) := by
  have stagedPtr : (staged before).getReg .x4 = wordAddress 1534 := by
    unfold staged
    rw [copy_field_register _ _ _ (by decide),record_setup_register _ _ (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact cursor.nonceScratch
  have loaded : RecordInputFrame (honestCheckInput oracle message input.positions salts) ordinal before :=
    Eq.mp (congrArg (fun data => RecordInputFrame data ordinal before) canonical) framed
  have raw := packed_record_nonce oracle message input.positions salts ordinal present before loaded
  have copied := (staged_nonce_read input ordinal present before fits cursor).trans raw
  rw [checker_nonce_words _ 1534 stagedPtr,buffer_window (staged before) 1534 2]
  change (fun i : Fin 2 => (readBuffer (staged before) 12272 16).extractLsb' (64*i.val) 64) = _
  rw [copied]
  rfl

theorem canonical_entry_value (oracle : Oracle) (input : CheckInput) (message : Message)
    (salts : CompleteSaltTape) (item : {index // index ∈ input.positions})
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    input.values item = message item.val := by
  let lookup (record : CheckInput) : Entry :=
    if present : item.val ∈ record.positions then record.values ⟨item.val,present⟩ else 0
  have transported := congrArg lookup canonical
  have present : item.val ∈ (honestCheckInput oracle message input.positions salts).positions := item.property
  dsimp only [lookup] at transported
  rw [dif_pos item.property,dif_pos present] at transported
  exact transported

theorem honest_row_digest (oracle : Oracle) (message : Message) (salts : CompleteSaltTape) (index : Index) :
    pinnedLeafDigest oracle.permutation index (saltWords (salts index)) (entryWords (message index)) =
      pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts index := by
  rfl

end TwoPermutationPrototype.Packed.RecordLeaf
