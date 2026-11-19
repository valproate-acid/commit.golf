import CommitGolfCandidate.QuadCommitLeafAccess

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute readBuffer writeBits packBuffer

theorem first_permutation_segment (s : MachineState) (slot : Fin 4096) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (coins : Bool) :
    execute image (2+fuel) s coins =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer
            (rawPrefix (window (memoryView s) (start+5)))))))
          let r ← execute image fuel (repliedA s slot start a) coins
          return r.charge 9 1) := by
  have ⟨m,r10,r12,hpc⟩ := first_execution s slot
  have atCall : (preparedA s slot).pc=leafPC slot 1 := by rw [hpc,pc]; exact leaf_pc_add slot 0 1
  have room := ready.sourceBound
  have src : (preparedA s slot).getReg .x10=wordAddress (start+5) := by
    rw [r10,ready.source]
  have dstReg : (preparedA s slot).getReg .x12=wordAddress (start+1) := by
    rw [r12,ready.source,wordAddress_add,wordAddress_add,BitVec.add_assoc];rfl
  have call := execute_permutation_call image fuel (preparedA s slot) coins (start+5) (start+1)
    (by omega) (by omega) src dstReg ((first_keeps _ _ _ (by decide) (by decide)).trans ready.selector)
    ((first_keeps _ _ _ (by decide) (by decide)).trans ready.size) ((first_keeps _ _ _ (by decide) (by decide)).trans ready.primitive)
    (fetch_leaf slot 1 (by decide) _ atCall)
  have same : window (memoryView (preparedA s slot)) (start+5)=rawPrefix (window (memoryView s) (start+5)) := by
    funext k; exact congrFun m _
  rw [same] at call
  rw [show 2+fuel=1+(fuel+1) by omega,first_ordinary_run _ _ _ _ pc (first_accesses s slot)]
  change (do let r ← execute image (fuel+1) (preparedA s slot) coins; return r.charge 1 0)=_
  rw [call]
  simp [repliedA,Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

theorem second_permutation_segment (s : MachineState) (slot : Fin 4096) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0)
    (a : BitVec 1600) (coins : Bool) :
    execute image (9+fuel) (repliedA s slot start a) coins =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer
            (pinnedWords (secondTag index) (nonceWords s slot) (replyWords a) (window (memoryView s) (start+5)))))))
          let r ← execute image fuel (finishedLeaf s slot start dst a b) coins
          return r.charge 16 1) := by
  let prev := repliedA s slot start a
  have src : prev.getReg .x10 = wordAddress (start+5) := after_a_input_cursor _ _ _ _ _ _ ready _
  obtain ⟨p5,p11,p13,p20,ppc⟩ := after_a_control _ _ _ _ _ _ ready pc a
  have ⟨_,r10,r12,hpc⟩ := second_execution prev slot (second_separate _ _ _ _ _ _ ready a)
  have atCall : (preparedB s slot start a).pc = leafPC slot 9 := by
    change ((secondInstructions slot).foldl execInstrBr prev).pc = _
    rw [hpc,show prev.pc=leafPC slot 2 from ppc]
    exact leaf_pc_add slot 2 7
  have inReg : (preparedB s slot start a).getReg .x10 = wordAddress (start+12) := by
    change ((secondInstructions slot).foldl execInstrBr prev).getReg .x10 = _
    rw [r10,src]
    exact (wordAddress_add (start+5) 7).symm
  have outReg : (preparedB s slot start a).getReg .x12 = wordAddress dst := by
    change ((secondInstructions slot).foldl execInstrBr prev).getReg .x12 = _
    rw [r12,show prev.getReg .x20 = s.getReg .x20 from p20,ready.destination]
  have sb := ready.sourceBound
  have call := execute_permutation_call image (fuel+1) (preparedB s slot start a) coins (start+12) dst
    (by omega) ready.heapBound inReg outReg ((second_keeps _ _ _ (by decide) (by decide) (by decide)).trans p5)
    ((second_keeps _ _ _ (by decide) (by decide) (by decide)).trans p11) ((second_keeps _ _ _ (by decide) (by decide) (by decide)).trans p13)
    (fetch_leaf slot 9 (by decide) _ atCall)
  rw [after_b_input _ _ _ _ _ _ ready a] at call
  have last (b : BitVec 1600) : execute image (fuel+1) (repliedB s slot start dst a b) coins =
      (do let r ← execute image fuel (finishedLeaf s slot start dst a b) coins; return r.charge 1 0) := by
    have atLast : (repliedB s slot start dst a b).pc = leafPC slot 10 := by
      unfold repliedB writeBits
      change (preparedB s slot start a).pc + 4 = _
      rw [atCall];exact leaf_pc_add slot 9 1
    exact CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf slot 10 (by decide) _ atLast) rfl
  rw [show 9+fuel=7+((fuel+1)+1) by omega,
    second_ordinary_run prev slot _ coins ppc (second_accesses _ _ _ _ _ _ ready a)]
  change (do let r ← execute image ((fuel+1)+1) (preparedB s slot start a) coins; return r.charge 7 0) = _
  rw [call]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro b _
  change BitVec 1600 at b
  change (do let result ← execute image (fuel+1) (repliedB s slot start dst a b) coins
             pure ((result.charge 8 1).charge 7 0)) = _
  rw [last b]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

def leafTrace (s : MachineState) (slot : Fin 4096) (start index dst : Nat) : OracleComp World MachineState := do
  let message := window (memoryView s) (start+5)
  let a ← World.query (.inr (.inr (.inl (packBuffer (rawPrefix message)))))
  let b ← World.query (.inr (.inr (.inl (packBuffer (pinnedWords (secondTag index) (nonceWords s slot) (replyWords a) message)))))
  return finishedLeaf s slot start dst a b

theorem execute_two_permutation_leaf (s : MachineState) (slot : Fin 4096) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (coins : Bool) :
    execute image (11+fuel) s coins =
      (do let done ← leafTrace s slot start index dst
          let r ← execute image fuel done coins
          return r.charge 25 2) := by
  rw [show 11+fuel=2+(9+fuel) by omega,first_permutation_segment _ _ _ _ _ _ _ ready pc]
  simp only [leafTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change BitVec 1600 at a
  rw [second_permutation_segment _ _ _ _ _ _ _ ready pc a coins]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl


end TwoPermutationPrototype.Quad.Commit.Leaves
