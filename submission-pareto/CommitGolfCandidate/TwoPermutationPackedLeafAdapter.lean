import CommitGolfCandidate.TwoPermutationPackedRecordLeafMeaning
import CommitGolfCandidate.TwoPermutationPackedRecordLeafBlock

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Packed.Checker
open TwoPermutationPrototype.Checker (honestIndex RecordInputFrame)
open TwoPermutationPrototype.PackedCertificate (honestCheckInput)
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000

theorem block_trace (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal state) (framed : RecordInputFrame input ordinal state) :
    let item := honestIndex input.positions ordinal present
    let observed := block oracle ordinal item.val state
    Nonempty (PackedLeafTrace oracle item.val (input.values item) (readBuffer observed.state 12288 32) observed.rows) := by
  let item := honestIndex input.positions ordinal present
  have meaning := block_digest_rows oracle ordinal item.val state
  have values := staged_entry_words input ordinal present state fits cursor framed
  dsimp only at meaning
  rw [values] at meaning
  obtain ⟨rows,digest⟩ := meaning
  dsimp only
  refine ⟨⟨checkerNonce (staged state),?_,?_,digest.symm⟩⟩
  · rw [rows]
    exact List.mem_cons_self
  · rw [rows]
    exact List.mem_cons_of_mem _ List.mem_cons_self

theorem block_honest (oracle : Oracle) (input : CheckInput) (ordinal : Nat)
    (present : ordinal < input.positions.card) (state : MachineState) (fits : ProofWithin input)
    (cursor : RecordCursor input ordinal state) (framed : RecordInputFrame input ordinal state)
    (message : Message) (salts : CompleteSaltTape)
    (canonical : input = honestCheckInput oracle message input.positions salts) :
    let item := honestIndex input.positions ordinal present
    readBuffer (block oracle ordinal item.val state).state 12288 32 =
      pinnedFullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts item.val := by
  let item := honestIndex input.positions ordinal present
  have digest := (block_digest_rows oracle ordinal item.val state).2
  dsimp only at digest ⊢
  rw [digest,staged_entry_words input ordinal present state fits cursor framed,
    staged_honest_nonce_words oracle input ordinal present state fits cursor framed message salts canonical,
    canonical_entry_value oracle input message salts item canonical]
  exact honest_row_digest oracle message salts item.val

end TwoPermutationPrototype.Packed.RecordLeaf
