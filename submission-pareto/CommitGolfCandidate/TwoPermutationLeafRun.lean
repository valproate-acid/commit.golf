import CommitGolfCandidate.TwoPermutationLeafAccess

/-! Exact commitment-machine execution of one two-permutation leaf. The two
ordered query inputs and all answer-dependent writes are exposed to the
security and tree refinements. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute readBuffer writeBits packBuffer

theorem first_permutation_segment (s : MachineState) (slot : Fin 16) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (coins : Bool) :
    execute commitImage (9+fuel) s coins =
      (do let a ← World.query (.inr (.inr (.inl (packBuffer
            (firstInput index (nonceWords s slot) (window (memoryView s) (start+5)))))))
          let r ← execute commitImage fuel (repliedA s slot start a) coins
          return r.charge 16 1) := by
  obtain ⟨d0,d1⟩ := leaf_nonce_separate _ _ _ _ _ _ ready
  obtain ⟨_,r10,r12,r5,r11,r13,hpc⟩ := first_execution s slot d0 d1
  have atCall : (preparedA s slot).pc = leafPC slot 8 := by
    rw [preparedA,hpc,pc]; exact leaf_pc_add slot 0 8
  have room := ready.sourceBound
  have call := execute_permutation_call commitImage fuel (preparedA s slot) coins start start
    (by omega) (by omega) (r10.trans ready.source) (r12.trans ready.source)
    (r5.trans ready.selector) (r11.trans ready.size) (r13.trans ready.primitive)
    (fetch_leaf slot 8 (by decide) _ atCall)
  have input := first_call_input s slot start index (by omega) ready.source ready.tag d0 d1
  change window (memoryView (preparedA s slot)) start = _ at input
  rw [input] at call
  rw [show 9+fuel=8+(fuel+1) by omega,first_ordinary_run _ _ _ _ pc (first_accesses _ _ _ _ _ _ ready)]
  change (do let r ← execute commitImage (fuel+1) (preparedA s slot) coins; return r.charge 8 0) = _
  rw [call]
  simp [repliedA,Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

theorem second_permutation_segment (s : MachineState) (slot : Fin 16) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0)
    (a : BitVec 1600) (coins : Bool) :
    execute commitImage (6+fuel) (repliedA s slot start a) coins =
      (do let b ← World.query (.inr (.inr (.inl (packBuffer
            (secondInput index (replyWords a) (window (memoryView s) (start+5)))))))
          let r ← execute commitImage fuel (finishedLeaf s slot start dst a b) coins
          return r.charge 13 1) := by
  let prev := repliedA s slot start a
  have src : prev.getReg .x10 = wordAddress start := after_a_input_cursor _ _ _ _ _ _ ready _
  obtain ⟨p5,p11,p13,p20,ppc⟩ := after_a_control _ _ _ _ _ _ ready pc a
  have ⟨_,r10,r12,r5,r11,r13,hpc⟩ := second_execution prev slot
  have atCall : (preparedB s slot start a).pc = leafPC slot 13 := by
    change ((secondInstructions slot).foldl execInstrBr prev).pc = _
    rw [hpc,show prev.pc=leafPC slot 9 from ppc]
    exact leaf_pc_add slot 9 4
  have inReg : (preparedB s slot start a).getReg .x10 = wordAddress (start+12) := by
    change ((secondInstructions slot).foldl execInstrBr prev).getReg .x10 = _
    rw [r10,src,wordAddress_add];rfl
  have outReg : (preparedB s slot start a).getReg .x12 = wordAddress dst := by
    change ((secondInstructions slot).foldl execInstrBr prev).getReg .x12 = _
    rw [r12,show prev.getReg .x20 = s.getReg .x20 from p20,ready.destination]
  have sb := ready.sourceBound
  have call := execute_permutation_call commitImage (fuel+1) (preparedB s slot start a) coins (start+12) dst
    (by omega) ready.heapBound inReg outReg (r5.trans p5) (r11.trans p11) (r13.trans p13)
    (fetch_leaf slot 13 (by decide) _ atCall)
  rw [after_b_input _ _ _ _ _ _ ready a] at call
  have last (b : BitVec 1600) : execute commitImage (fuel+1) (repliedB s slot start dst a b) coins =
      (do let r ← execute commitImage fuel (finishedLeaf s slot start dst a b) coins; return r.charge 1 0) := by
    have atLast : (repliedB s slot start dst a b).pc = leafPC slot 14 := by
      unfold repliedB writeBits
      change (preparedB s slot start a).pc + 4 = _
      rw [atCall];exact leaf_pc_add slot 13 1
    exact CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (fetch_leaf slot 14 (by decide) _ atLast) rfl
  rw [show 6+fuel=4+((fuel+1)+1) by omega,
    second_ordinary_run prev slot _ coins ppc (second_accesses prev slot start src ready.sourceBound)]
  change (do let r ← execute commitImage ((fuel+1)+1) (preparedB s slot start a) coins; return r.charge 4 0) = _
  rw [call]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro b _
  change BitVec 1600 at b
  change (do let result ← execute commitImage (fuel+1) (repliedB s slot start dst a b) coins
             pure ((result.charge 8 1).charge 4 0)) = _
  rw [last b]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

def leafTrace (s : MachineState) (slot : Fin 16) (start index dst : Nat) : OracleComp World MachineState := do
  let message := window (memoryView s) (start+5)
  let a ← World.query (.inr (.inr (.inl (packBuffer (firstInput index (nonceWords s slot) message)))))
  let b ← World.query (.inr (.inr (.inl (packBuffer (secondInput index (replyWords a) message)))))
  return finishedLeaf s slot start dst a b

theorem execute_two_permutation_leaf (s : MachineState) (slot : Fin 16) (start index dst salts fuel : Nat)
    (ready : LeafReady s slot start index dst salts) (pc : s.pc = leafPC slot 0) (coins : Bool) :
    execute commitImage (15+fuel) s coins =
      (do let done ← leafTrace s slot start index dst
          let r ← execute commitImage fuel done coins
          return r.charge 29 2) := by
  rw [show 15+fuel=9+(6+fuel) by omega,first_permutation_segment _ _ _ _ _ _ _ ready pc]
  simp only [leafTrace,bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro a _
  change BitVec 1600 at a
  rw [second_permutation_segment _ _ _ _ _ _ _ ready pc a coins]
  simp [Execution.charge,bind_assoc,←Nat.add_assoc] <;> rfl

end TwoPermutationPrototype.RV64
