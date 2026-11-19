import CommitGolfCandidate.TwoPermutationPackedLeafFrame

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
private theorem nonce_immediates_table : ∀ slot : Fin 128,
    signExtend12 (BitVec.ofNat 12 (16*slot.val)) = BitVec.ofNat 64 (8*(2*slot.val)) ∧
    signExtend12 (BitVec.ofNat 12 (16*slot.val+8)) = BitVec.ofNat 64 (8*(2*slot.val+1)) := by decide

private theorem nonce_immediates (slot : Fin 4096) :
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128))) = BitVec.ofNat 64 (8*(2*(slot.val%128))) ∧
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128)+8)) = BitVec.ofNat 64 (8*(2*(slot.val%128)+1)) :=
  nonce_immediates_table ⟨slot.val%128, Nat.mod_lt _ (by decide)⟩


theorem first_accesses (s : MachineState) (slot : Fin 4096) (i : Nat) (hi : i<1) :
    memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i)=true := by interval_cases i <;> rfl

private theorem second_accesses_core (prev : MachineState) (slot : Fin 4096)
    (start salts i : Nat) (bound : start+37≤2^33) (nonceBound : salts+256≤2^33)
    (tag : prev.getReg .x10+56=wordAddress (start+12)) (nonce : prev.getReg .x22=wordAddress salts)
    (hi : i<7) : memoryArgumentsValid (secondPrefix prev slot i) (leafInstr slot (2+i))=true := by
  interval_cases i
  · rfl
  · change accessValid (prev.getReg .x10+56+0) 8=true
    rw [tag];exact leaf_word_access _ 0 (by omega)
  · change accessValid (prev.getReg .x22+signExtend12 (BitVec.ofNat 12 (16*(slot.val%128)))) 8=true
    rw [nonce,(nonce_immediates slot).1];exact leaf_word_access _ _ (by omega)
  · change accessValid (prev.getReg .x10+56+8) 8=true
    rw [tag];exact leaf_word_access _ 1 (by omega)
  · change accessValid (prev.getReg .x22+signExtend12 (BitVec.ofNat 12 (16*(slot.val%128)+8))) 8=true
    rw [nonce,(nonce_immediates slot).2];exact leaf_word_access _ _ (by omega)
  · change accessValid (prev.getReg .x10+56+16) 8=true
    rw [tag];exact leaf_word_access _ 2 (by omega)
  · rfl

theorem second_accesses (s : MachineState) (slot : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s slot start index dst salts) (a : BitVec 1600) (i : Nat) (hi : i<7) :
    let prev := repliedA s slot start a
    memoryArgumentsValid (secondPrefix prev slot i) (leafInstr slot (2+i))=true := by
  let prev := repliedA s slot start a
  have bound := ready.sourceBound
  have nonceBound := ready.nonceBound
  have tag : prev.getReg .x10+56=wordAddress (start+12) := by
    rw [show prev.getReg .x10=wordAddress (start+5) from after_a_input_cursor _ _ _ _ _ _ ready _]
    exact (wordAddress_add (start+5) 7).symm
  have nonce : prev.getReg .x22=wordAddress salts := (after_a_reg _ _ _ _ _ (by decide) (by decide)).trans ready.nonces
  exact second_accesses_core prev slot start salts i bound nonceBound tag nonce hi

end TwoPermutationPrototype.RV64.PackedLeaves
