import CommitGolfCandidate.QuadCommitLeafControlFetch

/-! Fetch helpers: image indexing and the leaf latch. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open Leaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] image leafCode levelsCode decodeInstruction

theorem repeated_code_at {α : Type} (chunk : List α) (n j k : Nat) (hj : j<n) (hk : k<chunk.length) :
    ((List.replicate n chunk).flatten)[chunk.length*j+k]?=chunk[k]? := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    rw [List.replicate_succ,List.flatten_cons]
    cases j with
    | zero => simpa only [Nat.mul_zero,Nat.zero_add] using (List.getElem?_append_left hk)
    | succ j =>
      rw [Nat.mul_succ]
      rw [List.getElem?_append_right (by omega)]
      rw [show chunk.length*j+chunk.length+k-chunk.length=chunk.length*j+k by omega]
      exact ih j (by omega)

theorem fetch_code_index (s : MachineState) (index : Nat) (bounded : index<2^32)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*index)) (instruction : Instr)
    (decoded : (image.code[index]?).bind decodeInstruction=some (.base instruction)) :
    fetch image s=some (.base instruction) := by
  have numeric : s.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    omega
  rw [fetch,numeric,if_pos (by omega),show (4096+4*index-4096)/4=index by omega]
  cases result : image.code[index]? with
  | none => simp [result] at decoded
  | some w => simpa [result] using decoded

theorem code_segment_at (head chunk suffix : List (BitVec 32))
    (code : image.code=head++chunk++suffix) (j : Nat) (inside : j<chunk.length) :
    image.code[head.length+j]?=chunk[j]? := by
  rw [code,List.append_assoc,List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact List.getElem?_append_left inside

def leafLatchPrefix := setupWords++leafCode
def leafLatchSuffix := leafZeroWords++levelsCode++rootSetupWords++rootWords

theorem leaf_latch_prefix_length : leafLatchPrefix.length=45183 := by
  unfold leafLatchPrefix
  rw [List.length_append,leaf_code_word_count]
  rfl

theorem fetch_leaf_latch (s : MachineState) (pc : s.pc=184828) :
    fetch image s=some (.base (.BEQ .x10 .x8 72)) := by
  apply fetch_code_index s 45183 (by omega) pc
  have atIndex := code_segment_at leafLatchPrefix leafLatchWords leafLatchSuffix
    (by unfold image leafLatchPrefix leafLatchSuffix;simp only [List.append_assoc]) 0 (by decide)
  rw [leaf_latch_prefix_length,Nat.add_zero] at atIndex
  rw [atIndex]
  change decodeInstruction 0x04850463=some (.base (.BEQ .x10 .x8 72))
  unfold decodeInstruction
  rfl

theorem fetch_leaf_jump (s : MachineState) (pc : s.pc=184832) :
    fetch image s=some (.base (.JAL .x0 1916536)) := by
  apply fetch_code_index s 45184 (by omega) pc
  have atIndex := code_segment_at leafLatchPrefix leafLatchWords leafLatchSuffix
    (by unfold image leafLatchPrefix leafLatchSuffix;simp only [List.append_assoc]) 1 (by decide)
  rw [leaf_latch_prefix_length] at atIndex
  rw [atIndex]
  change decodeInstruction 0xe79d306f=some (.base (.JAL .x0 1916536))
  unfold decodeInstruction
  rfl

end TwoPermutationPrototype.Quad.Commit
