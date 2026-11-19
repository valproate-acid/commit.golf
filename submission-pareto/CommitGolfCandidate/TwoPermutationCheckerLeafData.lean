import CommitGolfCandidate.TwoPermutationCheckerLeafRun
import CommitGolfCandidate.TwoPermutationCheckerCopyDigest
import CommitGolfCandidate.TwoPermutationHidingEager

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- The oracle arguments use the same aligned words as the trusted loader. -/
theorem buffer_window (state : MachineState) (start count : Nat) :
    window (memoryView state) start =
      (fun i : Fin count => (readBuffer state (8*start) (8*count)).extractLsb' (64*i.val) 64) := by
  funext i
  have inside := i.isLt
  change memoryView state (start+i.val) = _
  rw [← read_word]
  have slice := read_buffer_slice state (8*start) (8*count) (8*i.val) 8 (by omega)
  simpa only [Nat.mul_add, ← Nat.mul_assoc, Nat.reduceMul] using slice.symm

/-- Equality of aligned memory words transports a complete checker input buffer. -/
theorem aligned_buffer_frame (before after : MachineState) (word count : Nat)
    (unchanged : ∀ offset < count, memoryView after (word+offset) = memoryView before (word+offset)) :
    readBuffer after (8*word) (8*count) = readBuffer before (8*word) (8*count) := by
  have windows : (window (memoryView after) word : Words count) = window (memoryView before) word := by
    funext index
    exact unchanged index.val index.isLt
  rw [buffer_window, buffer_window] at windows
  apply BitVec.eq_of_getLsbD_eq
  intro bit bounded
  let index : Fin count := ⟨bit/64, by omega⟩
  have agree := congrArg (fun word : BitVec 64 => word.getLsbD (bit%64)) (congrFun windows index)
  have cover : 64*(bit/64)+bit%64 = bit := by omega
  simpa [index, BitVec.getLsbD_extractLsb', Nat.mod_lt _ (by decide : 0 < 64), cover, Nat.add_comm] using agree

theorem checker_nonce_data {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : LeafReady state source nonce index) (salt : BitVec 128)
    (decoded : readBuffer state (8*nonce) 16 = salt) :
    checkerNonce state = saltWords salt := by
  rw [checker_nonce_words state nonce ready.proofPointer, buffer_window state nonce 2]
  change (fun i : Fin 2 => (readBuffer state (8*nonce) 16).extractLsb' (64*i.val) 64) = _
  rw [decoded]
  rfl

theorem checker_value_data {state : MachineState} {source : Nat} (message : Message) (index : Index)
    (decoded : readBuffer state (8*(source+5)) 256 = message index) :
    window (memoryView state) (source+5) = messageWords message index := by
  rw [buffer_window state (source+5) 32]
  change (fun i : Fin 32 => (readBuffer state (8*(source+5)) 256).extractLsb' (64*i.val) 64) = _
  rw [decoded]
  rfl

attribute [local irreducible] readBuffer

theorem honest_leaf_digest {state : MachineState} {source nonce : Nat} {index : Index}
    (oracle : Oracle) (message : Message) (salts : CompleteSaltTape)
    (ready : LeafReady state source nonce index)
    (saltData : readBuffer state (8*nonce) 16 = salts index)
    (valueData : readBuffer state (8*(source+5)) 256 = message index) :
    readBuffer (checkEvaluation oracle (recordRows (leafQueries state source index))).1.1 12288 32 =
      fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts index := by
  rw [checker_leaf_rows]
  dsimp only
  rw [checker_nonce_data ready _ saltData, checker_value_data message index valueData]
  exact checker_leaf_digest _ _ _ _

end TwoPermutationPrototype.Checker
