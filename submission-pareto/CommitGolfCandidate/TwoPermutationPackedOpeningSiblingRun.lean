import CommitGolfCandidate.TwoPermutationPackedOpeningCapEmit
import CommitGolfCandidate.TwoPermutationPackedOpeningGeometry

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (lowerNode trapdoorBase proofBase)

def lowerPC (level : Nat) : Word :=
  if bounded : level < 16 then BitVec.ofNat 64 (4096+4*siblingStart ⟨level,bounded⟩) else 0x1950

structure LowerCursor (state : MachineState) (index : Index) (ordinal level : Nat) : Prop where
  pc : state.pc = lowerPC level
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  node : state.getReg .x6 = BitVec.ofNat 64 (lowerNode index level)
  dest : state.getReg .x21 = BitVec.ofNat 64 (siblingDestination ordinal level)

def siblingBlock (level : Fin 16) (state : MachineState) : MachineState :=
  tailPrefix (copyState (siblingSite level) (headPrefix state 3)) level 2

theorem lower_pc_next (level : Fin 16) :
    BitVec.ofNat 64 (4096+4*(siblingEnd level+2)) = lowerPC (level.val+1) := by
  unfold lowerPC
  split
  · rw [sibling_next]
  · have last : level.val = 15 := by have := level.isLt; omega
    have eq : level = 15 := Fin.ext last
    subst level
    rfl

structure SiblingTrace (state : MachineState) (index : Index) (ordinal : Nat) (level : Fin 16) : Prop where
  run : RunsOpeningBlock state (siblingBlock level state) (5+siblingWidth level.val)
  next : LowerCursor (siblingBlock level state) index ordinal (level.val+1)
  bytes : ByteCopy state (siblingBlock level state) (siblingAddress index level.val)
    (siblingDestination ordinal level.val) (siblingWidth level.val)
  register : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x21 → reg ≠ .x31 →
    (siblingBlock level state).getReg reg = state.getReg reg
  input : ∀ address < proofBase,
    (siblingBlock level state).getMem (BitVec.ofNat 64 address) = state.getMem (BitVec.ofNat 64 address)

theorem execute_sibling (state : MachineState) (index : Index) (ordinal : Nat) (bounded : ordinal < LENGTH)
    (level : Fin 16) (cursor : LowerCursor state index ordinal level.val) :
    SiblingTrace state index ordinal level := by
  let site := siblingSite level
  let prepared := headPrefix state 3
  let copied := copyState site prepared
  let done := siblingBlock level state
  have head := sibling_head_post state
  have tail := sibling_tail_post copied level
  have ordinalFit := all_sibling_copies_fit index ordinal level.val bounded level.isLt
  have start : state.pc = BitVec.ofNat 64 (4096+4*siblingStart level) := by
    simpa only [lowerPC, dif_pos level.isLt, Fin.eta] using cursor.pc
  have before : prepared.pc = BitVec.ofNat 64 (4096+4*site.start) := by
    rw [head.1, start]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 12 = _
    rw [← BitVec.ofNat_add, ← sibling_copy_start level]
    congr 1
  have field : FieldInputs site prepared (siblingAddress index level.val)
      (siblingDestination ordinal level.val) := by
    refine ⟨before, physical_sibling_source state index _ cursor.heap cursor.node,
      (head.2.2.2 .x21 (by decide)).trans cursor.dest, ?_, ?_, ordinalFit.1, ordinalFit.2.1⟩
    · simpa only [site, sibling_width_exact] using ordinalFit.2.2.1
    · simpa only [site, sibling_width_exact] using ordinalFit.2.2.2
  have tailPC : copied.pc = BitVec.ofNat 64 (4096+4*siblingEnd level) := field.final_pc
  have ranHead : RunsOpeningBlock state prepared 3 :=
    fun fuel coins => execute_sibling_head state level start fuel coins
  have ranTail : RunsOpeningBlock copied done 2 :=
    fun fuel coins => execute_sibling_tail copied level tailPC fuel coins
  have trace := (ranHead.next field.run).next ranTail
  have kept (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x21) (d : reg ≠ .x31) :
      done.getReg reg = state.getReg reg :=
    (tail.2.2.2.2 reg c a).trans
      ((copy_register site prepared reg d).trans (head.2.2.2 reg b))
  refine ⟨?_, ⟨?_, (kept .x9 (by decide) (by decide) (by decide) (by decide)).trans cursor.heap, ?_, ?_⟩,
    ?_, kept, ?_⟩
  · change RunsOpeningBlock state done (5+siblingWidth level.val)
    rw [show 5+siblingWidth level.val = 3+2*site.halfwords+2 by
      rw [show 2*site.halfwords = siblingWidth level.val from sibling_width_exact level]
      omega]
    exact trace
  · have final : done.pc = BitVec.ofNat 64 (4096+4*(siblingEnd level+2)) := by
      change (tailPrefix copied level 2).pc = _
      rw [tail.1, tailPC]
      change BitVec.ofNat 64 _+BitVec.ofNat 64 8 = _
      rw [← BitVec.ofNat_add]
      congr 1
    exact final.trans (lower_pc_next level)
  · apply physical_sibling_parent
    exact (copy_register site prepared .x6 (by decide)).trans
      ((head.2.2.2 .x6 (by decide)).trans cursor.node)
  · apply physical_sibling_destination
    exact (copy_register site prepared .x21 (by decide)).trans ((head.2.2.2 .x21 (by decide)).trans cursor.dest)
  · change ByteCopy state (tailPrefix copied level 2) _ _ _
    simpa only [site, sibling_width_exact] using field.bytes.move head.2.1.symm tail.2.1
  · intro address below
    have above : proofBase ≤ siblingDestination ordinal level.val := by unfold siblingDestination recordBase; omega
    have stable := field.words_before proofBase address below above (by decide)
    have saved : done.mem = copied.mem := tail.2.1
    have reads : prepared.mem = state.mem := head.2.1
    change done.getMem _ = _
    simpa only [MachineState.getMem, saved, reads] using stable

end TwoPermutationPrototype.PackedOpening
