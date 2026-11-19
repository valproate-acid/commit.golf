import CommitGolfCandidate.QuadCommitLeafRun
import CommitGolfCandidate.QuadCommitGeometry

namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.RV64.PackedLeaves
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
/-- Leaf `u` of pass `g` is leaf `4095 g + u` (the loop re-enters at slot 1). -/
def idx (g : Nat) (u : Fin 4096) := 4095*g+u.val
def leafDest (i : Nat) := leafWord i
def leafSalt (i : Nat) := Commit.saltWord i
def heapBase (g pos : Nat) := windowWord g pos
def nonceBase (g pos : Nat) := leafSalt (4095*g+(if pos=4096 then 4095 else 256*((pos+128)/256)))

private theorem destination_table : ∀ u : Fin 45,
    wordAddress 192 + signExtend12 (slotImmediate u.val) =
      wordAddress (46*(u.val/5)+4*(u.val%5)) := by decide +kernel

private theorem relative_leaf (g u : Nat) :
    leafWord (4095*g+u) = leafWord (4095*g+45*(u/45)) + 46*((u%45)/5)+4*(u%5) := by
  unfold leafWord groupWord
  omega

private theorem immediate_mod45 (u : Nat) : slotImmediate u = slotImmediate (u%45) := by
  unfold slotImmediate
  have a : u%45%45=u%45 := Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
  have b : u%45%5=u%5 := by omega
  rw [a,b]

theorem window_destination (g u : Nat) (inside : u<4096) :
    wordAddress (heapBase g u) + signExtend12 (slotImmediate u) =
      wordAddress (leafDest (4095*g+u)) := by
  rw [heapBase]
  unfold windowWord leafDest
  rw [wordAddress_add,BitVec.add_assoc,immediate_mod45]
  have table := destination_table ⟨u%45,Nat.mod_lt _ (by decide)⟩
  have phase : u%45%5=u%5 := by omega
  rw [table]
  simp only [Fin.val_mk]
  rw [phase,←wordAddress_add]
  simpa only [Nat.add_assoc] using (congrArg wordAddress (relative_leaf g u)).symm

structure Regs (s : MachineState) (g pos : Nat) : Prop where
  source : s.getReg .x10=wordAddress (leafStart (4095*g+pos)+5)
  heap : s.getReg .x20=wordAddress (heapBase g pos)
  salts : s.getReg .x22=wordAddress (nonceBase g pos)
  stride : s.getReg .x7=4096
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  pc : s.pc=BitVec.ofNat 64 (4096+4*leafIndex pos)

theorem ready_slot (s : MachineState) (g : Nat) (u : Fin 4096) (bound : g<4097) (r : Regs s g u.val) :
    LeafReady s u (leafStart (idx g u)) (idx g u) (leafDest (idx g u)) (nonceBase g u.val) := by
  have h := u.isLt
  refine ⟨r.source,?_,r.salts,?_,?_,?_,?_,?_,r.selector,r.size,r.primitive⟩
  · rw [r.heap]
    exact window_destination g u.val u.isLt
  · rw [commit_tag_address,wordAddress];congr 1;unfold leafStart;omega
  all_goals simp only [leafStart,leafDest,nonceBase,leafSalt,idx,leafWord,groupWord,Commit.saltWord] <;> (try split) <;> omega

structure RawRegs (s : MachineState) (g : Nat) (u : Fin 4096) : Prop where
  source : s.getReg .x10=wordAddress (leafStart (idx g u+1)+5)
  dest : s.getReg .x12=wordAddress (leafDest (idx g u))
  heap : s.getReg .x20=wordAddress (heapBase g u.val)
  salts : s.getReg .x22=wordAddress (nonceBase g u.val)
  stride : s.getReg .x7=4096
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1
  pc : s.pc=leafPC u 11

private theorem tail_source (state : MachineState) (dst : Nat) (b : BitVec 1600) :
    (execInstrBr (writeBits state (wordAddress dst) b) (.ADDI .x10 .x10 200)).getReg .x10 =
      state.getReg .x10 + 200 := by
  change (writeBits state (wordAddress dst) b).getReg .x10 + 200 = _
  rw [CommitGolfCandidate.writeBits_register]

private theorem tail_output (state : MachineState) (dst : Nat) (b : BitVec 1600) :
    (execInstrBr (writeBits state (wordAddress dst) b) (.ADDI .x10 .x10 200)).getReg .x12 =
      state.getReg .x12 := by
  change (writeBits state (wordAddress dst) b).getReg .x12 = _
  rw [CommitGolfCandidate.writeBits_register]

private theorem tail_pc (state : MachineState) (dst : Nat) (b : BitVec 1600) :
    (execInstrBr (writeBits state (wordAddress dst) b) (.ADDI .x10 .x10 200)).pc = state.pc + 8 := by
  change state.pc + 4 + 4 = _
  rw [BitVec.add_assoc]
  rfl

private theorem source_advance (start : Nat) :
    (wordAddress (start+5) + 56) + 200 = wordAddress (start+37) := by
  change (wordAddress (start+5) + wordAddress 7) + wordAddress 25 = _
  rw [← wordAddress_add, ← wordAddress_add]

private theorem finish_source_at (s : MachineState) (u : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s u start index dst salts) (a b : BitVec 1600) :
    (finishedLeaf s u start dst a b).getReg .x10 = wordAddress (start+37) := by
  let p := repliedA s u start a
  have separate : StampSeparate p u := second_separate s u start index dst salts ready a
  have inc := (second_execution p u separate).2.1
  have src : p.getReg .x10 = wordAddress (start+5) := after_a_input_cursor s u start index dst salts ready a
  exact (tail_source (preparedB s u start a) dst b).trans ((congrArg (· + 200) inc).trans
    ((congrArg (fun w : Word => (w+56)+200) src).trans (source_advance start)))

private theorem finish_output_at (s : MachineState) (u : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s u start index dst salts) (a b : BitVec 1600) :
    (finishedLeaf s u start dst a b).getReg .x12 = wordAddress dst := by
  let p := repliedA s u start a
  have separate : StampSeparate p u := second_separate s u start index dst salts ready a
  have output := (second_execution p u separate).2.2.1
  have base : p.getReg .x20=s.getReg .x20 := after_a_reg s u start a .x20 (by decide) (by decide)
  exact (tail_output (preparedB s u start a) dst b).trans (output.trans
    ((congrArg (· + signExtend12 (slotImmediate u.val)) base).trans ready.destination))

private theorem finish_pc_at (s : MachineState) (u : Fin 4096) (start index dst salts : Nat)
    (ready : LeafReady s u start index dst salts) (pc : s.pc = leafPC u 0) (a b : BitVec 1600) :
    (finishedLeaf s u start dst a b).pc = leafPC u 11 := by
  let p := repliedA s u start a
  have separate : StampSeparate p u := second_separate s u start index dst salts ready a
  have middle := (second_execution p u separate).2.2.2
  have first : p.pc=leafPC u 2 := (after_a_control s u start index dst salts ready pc a).2.2.2.2
  have atSecond : (preparedB s u start a).pc = leafPC u 9 :=
    middle.trans ((congrArg (·+28) first).trans (leaf_pc_add u 2 7))
  exact (tail_pc (preparedB s u start a) dst b).trans
    ((congrArg (·+8) atSecond).trans (leaf_pc_add u 9 2))

private theorem next_source (g : Nat) (u : Fin 4096) :
    leafStart (idx g u)+37 = leafStart (idx g u+1)+5 := by unfold leafStart;omega

theorem post_slot (s : MachineState) (g : Nat) (u : Fin 4096) (bound : g<4097) (r : Regs s g u.val)
    (a b : BitVec 1600) :
    let i := idx g u
    RawRegs (finishedLeaf s u (leafStart i) (leafDest i) a b) g u := by
  let i := idx g u
  let start := leafStart i
  let dst := leafDest i
  let salt := nonceBase g u.val
  have ready : LeafReady s u start i dst salt := ready_slot s g u bound r
  have hold := finished_reg_frame s u start dst a b
  exact ⟨(finish_source_at s u start i dst salt ready a b).trans (congrArg wordAddress (next_source g u)),
    finish_output_at s u start i dst salt ready a b,
    (hold .x20 (by decide) (by decide) (by decide)).trans r.heap,
    (hold .x22 (by decide) (by decide) (by decide)).trans r.salts,
    (hold .x7 (by decide) (by decide) (by decide)).trans r.stride,
    (hold .x5 (by decide) (by decide) (by decide)).trans r.selector,
    (hold .x11 (by decide) (by decide) (by decide)).trans r.size,
    (hold .x13 (by decide) (by decide) (by decide)).trans r.primitive,
    finish_pc_at s u start i dst salt ready r.pc a b⟩


end TwoPermutationPrototype.Quad.Commit.Leaves
