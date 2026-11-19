import CommitGolfCandidate.TwoPermutationPackedGroupCompare
import CommitGolfCandidate.TwoPermutationPackedGroupLatchView
import CommitGolfCandidate.TwoPermutationPackedGroupGeometry
import CommitGolfCandidate.TwoPermutationPackedGroupCopy
namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (GroupAccepted groupMemory group_memory_set group_memory_four aligned_access distinct_word_offset word_offset)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute GroupBlock.done compareGroup copiedGroup

private def groupPrepared (s : MachineState) (node : Nat) : MachineState × Nat :=
  let t := GroupBlock.setup.done s
  if s.getMem (wordAddress (512+node))=0 then
    (GroupBlock.mark.done (copiedGroup t),16)
  else
    let result := compareGroup 4 t
    (result.1,6+result.2)

def groupRun (s : MachineState) (node : Nat) : MachineState × Nat :=
  let result := groupPrepared s node
  if GroupAccepted s node then (GroupBlock.latch.done result.1,result.2+4) else result

structure GroupFrame (s t : MachineState) (node remaining : Nat) : Prop where
  pc : t.pc=if GroupAccepted s node then (if remaining=0 then 0x1444 else 0x1058) else 0x15b0
  memory : t.mem=(groupMemory s node).mem
  saved : ∀ r, GroupSaved r → t.getReg r=s.getReg r
  advanced : GroupAccepted s node → t.getReg .x8=s.getReg .x8+8 ∧ t.getReg .x19=s.getReg .x19+256 ∧
    t.getReg .x18=BitVec.ofNat 64 remaining

private def BeforeSaved (reg : Reg) : Prop := reg ∉ ([.x7,.x28,.x29,.x30,.x31] : List Reg)

private theorem prepared_run (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    let result := groupPrepared s node
    GroupHop s result.1 result.2 ∧ result.2≤19 ∧
      result.1.pc=(if GroupAccepted s node then 0x1434 else 0x15b0) ∧
      result.1.mem=(groupMemory s node).mem ∧
      ∀ r : Reg, BeforeSaved r → result.1.getReg r=s.getReg r := by
  let t := GroupBlock.setup.done s
  obtain ⟨pc,mark,root,mem,regs⟩ := group_setup_view s ready.pc
  rw [ready.mark] at pc mark
  rw [ready.root] at root
  have setup : GroupHop s t 6 := GroupBlock.hop .setup s ready.pc (by
    change accessValid (groupMarkAddress s) 8=true
    rw [ready.mark]
    exact aligned_access _ (by have := ready.high;omega))
  have src : t.getReg .x23=wordAddress 1536 := (regs _ (by decide) (by decide) (by decide)).trans ready.scratch
  have rd (j : Fin 4) : accessValid (t.getReg .x28+BitVec.ofNat 64 (8*j.val)) 8=true := by
    rw [root,word_offset]
    apply aligned_access
    have := ready.high
    omega
  have sd (j : Fin 4) : accessValid (t.getReg .x23+BitVec.ofNat 64 (8*j.val)) 8=true := by
    rw [src,word_offset]
    exact aligned_access _ (by omega)
  have fields (r : Reg) (saved : BeforeSaved r) : r≠.x7 ∧ r≠.x28 ∧ r≠.x29 ∧ r≠.x30 ∧ r≠.x31 := by
    simpa [BeforeSaved,not_or] using saved
  by_cases fresh : s.getMem (wordAddress (512+node))=0
  · have ok : GroupAccepted s node := Or.inl fresh
    have copyPC : t.pc=0x140c := by simpa only [if_pos fresh] using pc
    let c := copiedGroup t
    have copy : GroupHop t c 8 := execute_group_copy t copyPC sd rd
    have markPC : c.pc=0x142c := by rw [show c.pc=t.pc+32 from copied_group_pc t,copyPC];rfl
    have markReg : c.getReg .x7=wordAddress (512+node) := (copied_group_register _ _ (by decide)).trans mark
    have writeMark : GroupHop c (GroupBlock.mark.done c) 2 := GroupBlock.hop .mark c markPC (by
      change accessValid (c.getReg .x7) 8=true
      rw [markReg]
      exact aligned_access _ (by have := ready.high;omega))
    have separate (i j : Fin 4) :
        t.getReg .x23+BitVec.ofNat 64 (8*i.val)≠t.getReg .x28+BitVec.ofNat 64 (8*j.val) := by
      rw [src,root]
      exact distinct_word_offset _ _ _ _ (by omega) (by have := ready.high;omega) (by omega)
    have copiedMem := copied_group_memory t separate
    rw [src,root] at copiedMem
    obtain ⟨dest,store,kept⟩ := group_mark_view c markPC
    rw [groupPrepared,if_pos fresh,groupMemory,if_pos fresh,if_pos ok]
    refine ⟨(setup.thenDo copy).thenDo writeMark,by change 16≤19;decide,dest,?_,?_⟩
    · rw [store,markReg]
      exact group_memory_set (copiedMem.trans (group_memory_four mem _ _)) _ _
    · intro r h
      obtain ⟨a,b,d,_,e⟩ := fields _ h
      exact (kept r d).trans ((copied_group_register _ _ e).trans (regs r a b d))
  · have duplicatePC : t.pc=0x13d8 := by simpa only [if_neg fresh] using pc
    have readable : GroupReadable t := fun j => ⟨rd j,sd j⟩
    obtain ⟨run,cost,unchanged,kept,exit⟩ := compare_group_run t 4 (by decide) duplicatePC readable
    have same : (∀ i : Fin 4, 4-4≤ i.val → sameGroupWord t i) ↔ GroupAccepted s node := by
      rw [GroupAccepted,or_iff_right fresh,read_digest_eq_iff _ _ _ _ (by omega) (by decide)]
      have word (j : Fin 4) : sameGroupWord t j ↔
          s.getMem (BitVec.ofNat 64 (8*(2048+4*node)+8*j.val))=s.getMem (BitVec.ofNat 64 (12288+8*j.val)) := by
        simp only [sameGroupWord,src,root,wordAddress,←BitVec.ofNat_add,MachineState.getMem,mem,t]
      constructor
      · intro all j hi
        exact (word ⟨j,hi⟩).mp (all ⟨j,hi⟩ (by omega))
      · intro all j _
        exact (word j).mpr (all j.val j.isLt)
    rw [groupPrepared,if_neg fresh,groupMemory,if_neg fresh]
    refine ⟨setup.thenDo run,by change 6+(compareGroup 4 t).2≤19;omega,?_,unchanged.trans mem,?_⟩
    · simpa only [same] using exit
    · intro r h
      obtain ⟨a,b,d,e,_⟩ := fields _ h
      exact (kept r d e).trans (regs r a b d)

private theorem run_frame (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    let result := groupRun s node
    GroupHop s result.1 result.2 ∧ result.2≤23 ∧ GroupFrame s result.1 node remaining := by
  obtain ⟨run,cost,exit,mem,regs⟩ := prepared_run s node remaining ready
  let p := (groupPrepared s node).1
  have old (r : Reg) (h : GroupSaved r) : BeforeSaved r := by
    simp [GroupSaved,BeforeSaved,not_or] at *
    tauto
  by_cases ok : GroupAccepted s node
  · have entry : p.pc=0x1434 := by simpa only [if_pos ok] using exit
    have latch : GroupHop p (GroupBlock.latch.done p) 4 := GroupBlock.hop .latch p entry trivial
    have counter : p.getReg .x18=BitVec.ofNat 64 (remaining+1) := (regs .x18 (by unfold BeforeSaved;decide)).trans ready.counter
    obtain ⟨pc,a,b,c,m,r⟩ := group_latch_view p entry remaining counter ready.small
    rw [groupRun,if_pos ok]
    refine ⟨run.thenDo latch,by omega,⟨by simpa only [if_pos ok] using pc,m.trans mem,?_,?_⟩⟩
    · intro reg h
      have kept : reg≠.x8 ∧ reg≠.x19 ∧ reg≠.x18 := by simp [GroupSaved,not_or] at h;tauto
      exact (r _ kept.1 kept.2.1 kept.2.2).trans (regs _ (old _ h))
    · intro _
      rw [show p.getReg .x8=s.getReg .x8 from regs _ (by unfold BeforeSaved;decide)] at a
      rw [show p.getReg .x19=s.getReg .x19 from regs _ (by unfold BeforeSaved;decide)] at b
      exact ⟨a,b,c⟩
  · rw [groupRun,if_neg ok]
    exact ⟨run,by omega,⟨by simpa only [if_neg ok] using exit,mem,fun r h => regs r (old r h),fun h => (ok h).elim⟩⟩

theorem group_run_execute (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    GroupHop s (groupRun s node).1 (groupRun s node).2 := (run_frame s node remaining ready).1

theorem group_run_state (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    GroupFrame s (groupRun s node).1 node remaining := (run_frame s node remaining ready).2.2

theorem group_run_cost (s : MachineState) (node remaining : Nat) (ready : GroupReady node remaining s) :
    (groupRun s node).2≤23 := (run_frame s node remaining ready).2.1

end TwoPermutationPrototype.Packed.Checker
