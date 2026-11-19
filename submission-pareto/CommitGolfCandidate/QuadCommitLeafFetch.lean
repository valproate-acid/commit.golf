import CommitGolfCandidate.QuadCommitLeafOps
import CommitGolfCandidate.Execution

/-! Fetch the unchanged pinned leaf instructions at their new quad-layout locations. -/
namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
deriving instance DecidableEq for CommitGolf.Riscv.Instruction
set_option maxHeartbeats 3000000

/-- Word index of a leaf in the 4096-leaf body. -/
def leafIndex (u : Nat) : Nat := 19 + ((List.range u).flatMap leafWords).length

def leafPC (u : Fin 4096) (offset : Nat) : Word :=
  BitVec.ofNat 64 (4096 + 4*(leafIndex u.val+offset))

def leafInstr (slot : Fin 4096) (offset : Nat) : Instr :=
  ((leafInstructions slot)[offset]?).getD .EBREAK

theorem leaf_pc_add (slot : Fin 4096) (i j : Nat) :
    leafPC slot i + BitVec.ofNat 64 (4*j)=leafPC slot (i+j) := by
  unfold leafPC
  rw [←BitVec.ofNat_add]
  congr 1 <;> omega

theorem leaf_words_length_bound (u : Nat) : (leafWords u).length ≤ 14 := by
  simp only [leafWords,List.length_append,List.length_cons,List.length_nil]
  split <;> split <;> split <;> simp_all only [List.length_cons,List.length_nil] <;> omega

theorem leaf_prefix_length_bound (n : Nat) : ((List.range n).flatMap leafWords).length ≤ 14*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,List.length_append]
    simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      (show ((List.range n).flatMap leafWords).length + (leafWords n).length ≤ 14*(n+1) by
        have := leaf_words_length_bound n
        omega)

theorem leaf_words_length_min (u : Nat) : 11 ≤ (leafWords u).length := by
  simp only [leafWords,List.length_append,List.length_cons,List.length_nil]
  omega

theorem leaf_code_at (u k : Nat) (hu : u<4096) (hk : k<(leafWords u).length) :
    image.code[leafIndex u+k]? = (leafWords u)[k]? := by
  have splitRange : List.range 4096 = List.range (u+1) ++ (List.range (4096-(u+1))).map (u+1+·) := by
    rw [←List.range_add]
    congr 1
    omega
  have splitCode : leafCode = (List.range u).flatMap leafWords ++ leafWords u ++
      ((List.range (4096-(u+1))).map (u+1+·)).flatMap leafWords := by
    unfold leafCode
    rw [splitRange,List.range_succ,List.flatMap_append,List.flatMap_append]
    simp
  simp only [image,List.append_assoc]
  rw [show leafIndex u+k=setupWords.length+(((List.range u).flatMap leafWords).length+k) by
    change 19+_+k=19+(_+k)
    omega]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  rw [splitCode]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
  exact List.getElem?_append_left (by have := leaf_words_length_min u; omega)

private theorem nonce_load_table : ∀ s : Fin 256,
    decodeInstruction (BitVec.ofNat 32 (0x000b3f83 + 1048576 * (16*s.val))) =
      some (.base (.LD .x31 .x22 (BitVec.ofNat 12 (16*s.val)))) ∧
    decodeInstruction (BitVec.ofNat 32 (0x008b3f83 + 1048576 * (16*s.val))) =
      some (.base (.LD .x31 .x22 (BitVec.ofNat 12 (16*s.val+8)))) := by decide +kernel

private theorem output_table : ∀ s : Fin 45,
    decodeInstruction (BitVec.ofNat 32 (0x000a0613 + 1048576 * (slotImmediate s.val).toNat)) =
      some (.base (.ADDI .x12 .x20 (slotImmediate s.val))) := by decide +kernel

private theorem immediate_mod45 (u : Nat) : slotImmediate u = slotImmediate (u%45) := by
  unfold slotImmediate
  have a : u%45%45=u%45 := Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
  have b : u%45%5=u%5 := by omega
  rw [a,b]

attribute [local irreducible] decodeInstruction

private theorem leaf_decoded (u : Fin 4096) (k : Nat) (hk : k<11) :
    ((leafWords u.val)[k]?).bind decodeInstruction = some (.base (leafInstr u k)) := by
  have nonce := nonce_load_table ⟨u.val%256,Nat.mod_lt _ (by decide)⟩
  have output := output_table ⟨u.val%45,Nat.mod_lt _ (by decide)⟩
  have tableLen := leaf_words_length_min u.val
  unfold leafWords
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_cons,List.length_nil];omega)]
  rw [List.getElem?_append_left (by simp only [List.length_append,List.length_cons,List.length_nil];omega)]
  rw [List.getElem?_append_left (by simp;omega)]
  interval_cases k <;>
    simp only [leafInstr,leafInstructions,firstInstructions,secondInstructions,List.cons_append,
      List.nil_append,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      Option.bind_some]
  · unfold decodeInstruction; rfl
  · unfold decodeInstruction; rfl
  · unfold decodeInstruction; rfl
  · unfold decodeInstruction; rfl
  · exact nonce.1
  · unfold decodeInstruction; rfl
  · exact nonce.2
  · unfold decodeInstruction; rfl
  · rw [immediate_mod45 u.val]
    exact output
  · unfold decodeInstruction; rfl
  · unfold decodeInstruction; rfl

attribute [local irreducible] image

theorem fetch_leaf (slot : Fin 4096) (i : Nat) (inside : i<11) (s : MachineState)
    (pc : s.pc=leafPC slot i) :
    fetch image s=some (.base (leafInstr slot i)) := by
  have idxBound := leaf_prefix_length_bound slot.val
  have slotBound := slot.isLt
  have numeric : s.pc.toNat=4096+4*(leafIndex slot.val+i) := by
    rw [pc,leafPC,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    unfold leafIndex
    omega
  rw [fetch,numeric,if_pos (by omega),show (4096+4*(leafIndex slot.val+i)-4096)/4=leafIndex slot.val+i by omega]
  have decoded := leaf_decoded slot i inside
  rw [←leaf_code_at slot.val i slot.isLt (by have := leaf_words_length_min slot.val; omega)] at decoded
  cases result : image.code[leafIndex slot.val+i]? with
  | none => simp [result] at decoded
  | some w => simpa [result] using decoded

end TwoPermutationPrototype.Quad.Commit.Leaves
