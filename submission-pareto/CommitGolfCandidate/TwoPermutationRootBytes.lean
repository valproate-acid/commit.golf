import CommitGolfCandidate.TwoPermutationFullTree
import CommitGolfCandidate.TwoPermutationFixedDraw
import CommitGolfCandidate.TwoPermutationTranscript

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support
  read_buffer_slice splitBlocks)
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] checkEvaluation leavesTrace parentsTrace parentBatches fullParents readBuffer
  finalReply fullLeafDigests readyState parentSetup rootPrefix transcriptHeap

theorem root_preserves_heap_buffer (s : MachineState) (out : s.getReg .x8=4294971392) (start bytes : Nat)
    (above : 4294971424≤8*start) (limit : start+bytes < 2^33) (alignment : bytes%8=0) :
    readBuffer (rootPrefix s 10) (8*start) bytes=readBuffer s (8*start) bytes := by
  apply aligned_buffer_eq _ _ _ alignment
  intro k bound
  rw [root_copy_trap_word s out (start+k) (by omega) (by omega)]
  have slice := read_buffer_slice s (8*start) bytes (8*k) 8 (by omega)
  rw [show 8*start+8*k=8*(start+k) by omega,read_word] at slice
  simpa only [←Nat.mul_assoc] using slice.symm

def publicTree (oracle : Oracle) (msg : Message) (salts : CompleteSaltTape) :=
  transcriptHeap false oracle.compression (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) msg salts)

theorem serialized_parent_results (candidate : Submission) (abi : CommitABI candidate)
    (parents : MachineState) (heap : Nat → BitVec 256) (salts : Index → BitVec 128) (res : Execution)
    (state : res.state=rootPrefix parents 10) (heapReg : parents.getReg .x9=4294971424)
    (x8 : parents.getReg .x8=4294971392) (content : ParentContent parents heap salts 0) :
    (candidate.readCommit res).1=heap 1 ∧
    (∀ n, 0<n → n<2*LENGTH → (candidate.readCommit res).2.extractLsb' (256*n) 256=heap n) ∧
    (∀ i : Index, (candidate.readCommit res).2.extractLsb' (8*(80*LENGTH+16*i.val)) 128=salts i) := by
  simp only [Submission.readCommit,state,abi.output,abi.trapdoor]
  constructor
  · exact (root_copy_output parents heapReg x8).trans (content.nodes 1 (by decide) (by decide))
  constructor
  · intro n pos small
    have limit : n<2*2^24 := small
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 candidate.sizes.trapdoor (32*n) 32
      (by rw [abi.size];change _≤96*2^24;omega)
    rw [show 8*(32*n)=256*n by omega,show 4294971424+32*n=8*treeWord n by unfold treeWord;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents x8 _ 32 (by unfold treeWord;omega) (by unfold treeWord;omega) (by decide)]
    exact content.nodes n pos small
  · intro i
    have bound : i.val<2^24 := i.isLt
    have slice := read_buffer_slice (rootPrefix parents 10) 4294971424 candidate.sizes.trapdoor
      (80*LENGTH+16*i.val) 16 (by rw [abi.size];change 80*2^24+16*i.val+16≤96*2^24;omega)
    rw [show 4294971424+(80*LENGTH+16*i.val)=8*leafSalt i.val by change 4294971424+(80*2^24+16*i.val)=_;unfold leafSalt;omega] at slice
    apply slice.trans
    rw [root_preserves_heap_buffer parents x8 _ 16 (by unfold leafSalt;omega) (by unfold leafSalt;omega) (by decide)]
    exact content.nonces i

end TwoPermutationPrototype.RV64
