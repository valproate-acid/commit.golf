import CommitGolfCandidate.TwoPermutationCheckerLowerRun
import CommitGolfCandidate.TwoPermutationTranscript

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

theorem honest_heap_climb (oracle : Oracle) (leaves : DigestTape) (node : Nat)
    (positive : 2 ≤ node) (bounded : node < 2*LENGTH) :
    let heap := transcriptHeap false oracle.compression leaves
    oracle.compression (pathPair node (heap node) (heap (node ^^^ 1))) = heap (node/2) := by
  let heap := transcriptHeap false oracle.compression leaves
  change oracle.compression (pathPair node (heap node) (heap (node ^^^ 1))) = heap (node/2)
  have parent := transcript_heap_parent false oracle.compression leaves (node/2) (by omega) (by omega)
  change heap (node/2) = oracle.compression (heap (2*(node/2)+1) ++ heap (2*(node/2))) at parent
  rw [parent]
  by_cases even : node % 2 = 0
  · rw [pathPair, ite_eq_left even, Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show 2*(node/2)+1 = node+1 by omega, show 2*(node/2) = node by omega]
  · have odd : Odd node := Nat.odd_iff.mpr (by omega)
    rw [pathPair, ite_eq_right even, Nat.xor_one_of_odd odd]
    rw [show 2*(node/2)+1 = node by omega, show 2*(node/2) = node-1 by omega]

theorem aligned_digest_frame (before after : MachineState) (word : Nat)
    (unchanged : ∀ offset < 4, memoryView after (word+offset) = memoryView before (word+offset)) :
    readBuffer after (8*word) 32 = readBuffer before (8*word) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro offset bounded
  simpa only [memoryView, wordAddress, Nat.mul_add] using unchanged offset bounded

attribute [local irreducible] lowerRun lowerReply readBuffer transcriptHeap

theorem lower_run_recovers_heap {state : MachineState} {node proof : Nat}
    (oracle : Oracle) (leaves : DigestTape) (left : Nat) (bounded : left ≤ 16)
    (ready : left ≠ 0 → LowerReady state node proof)
    (nodeLow : 2^left ≤ node) (nodeHigh : node < 2*LENGTH)
    (counter : state.getReg .x29 = BitVec.ofNat 64 left)
    (room : proof+4*left ≤ 2^33)
    (child : readBuffer state 12288 32 = transcriptHeap false oracle.compression leaves node)
    (path : ∀ offset < left, readBuffer state (8*(proof+4*offset)) 32 =
      transcriptHeap false oracle.compression leaves ((node/2^offset) ^^^ 1)) :
    readBuffer (lowerRun oracle left state).state 12288 32 =
      transcriptHeap false oracle.compression leaves (node/2^left) := by
  induction left generalizing state node proof with
  | zero => simpa only [lowerRun, Nat.pow_zero, Nat.div_one] using child
  | succ left ih =>
    let heap := transcriptHeap false oracle.compression leaves
    have current := ready (by omega)
    have bound64 : node < 2^64 := by
      change node < 2*16777216 at nodeHigh
      omega
    have row := lower_recorded_query oracle current bound64
    dsimp only at row
    rw [lowerRun, row]
    dsimp only
    let pair := pathPair node (readBuffer state 12288 32) (readBuffer state (8*proof) 32)
    let reply : BitVec 256 := oracle.compression pair
    let middle := lowerReply state reply
    have geometry := lower_reply_geometry current bound64 reply left counter (by omega)
    have above := current.proofAbove
    have nextLow : 2^left ≤ node/2 := by
      apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
      simpa only [Nat.pow_succ] using nodeLow
    have nonzero : 0 < 2^left := by positivity
    have positive : 2 ≤ node := by omega
    have sibling : readBuffer state (8*proof) 32 = heap (node ^^^ 1) := by
      simpa only [Nat.pow_zero, Nat.div_one, Nat.mul_zero, Nat.add_zero] using path 0 (by omega)
    have nextChild : readBuffer middle 12288 32 = heap (node/2) := by
      change readBuffer (lowerReply state reply) 12288 32 = _
      rw [lower_reply_digest]
      change oracle.compression (pathPair node (readBuffer state 12288 32)
        (readBuffer state (8*proof) 32)) = _
      rw [child,sibling]
      exact honest_heap_climb oracle leaves node positive nodeHigh
    have quotient (offset : Nat) : (node/2)/2^offset = node/2^(offset+1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2]
    have nextPath (offset : Nat) (inside : offset < left) :
        readBuffer middle (8*(proof+4+4*offset)) 32 = heap (((node/2)/2^offset) ^^^ 1) := by
      rw [quotient, show proof+4+4*offset = proof+4*(offset+1) by omega]
      refine (aligned_digest_frame state middle _ fun k hk => ?_).trans (path (offset+1) (by omega))
      exact lower_reply_frame current reply _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
    have recovered := ih (state := middle) (node := node/2) (proof := proof+4) (by omega)
      (fun more => lower_reply_ready current bound64 reply left counter (by omega) (by omega) (by omega))
      nextLow (by omega) geometry.2.2.1 (by omega) nextChild nextPath
    simpa only [quotient] using recovered

theorem honest_lower_record {state : MachineState} {proof : Nat} (oracle : Oracle)
    (leaves : DigestTape) (index : Index) (ready : LowerReady state (LENGTH+index.val) proof)
    (counter : state.getReg .x29 = 16) (room : proof+64 ≤ 2^33)
    (child : readBuffer state 12288 32 = leaves index)
    (path : ∀ offset < 16, readBuffer state (8*(proof+4*offset)) 32 =
      transcriptHeap false oracle.compression leaves (((LENGTH+index.val)/2^offset) ^^^ 1)) :
    readBuffer (lowerRun oracle 16 state).state 12288 32 =
      transcriptHeap false oracle.compression leaves (capGroup index) := by
  exact lower_run_recovers_heap oracle leaves 16 (by decide) (fun _ => ready) (by
    change 65536 ≤ 16777216+index.val
    omega) (by
    have := index.isLt
    omega) counter room (child.trans (transcript_heap_leaf false oracle.compression leaves index).symm) path

end TwoPermutationPrototype.Checker
