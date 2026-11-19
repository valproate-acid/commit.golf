import CommitGolfCandidate.QuadCommitPentaRoot

/-! The tree phase of the penta commit image from any leaf-entry state with the right registers:
leaves, clearing the last level-0 group, levels 1 .. 10, the root node, root copy and HALT. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling Penta
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
attribute [local irreducible] image execute rootPrefix writeBits

/-- Registers of the leaf-entry state (PC 4172) needed by the whole tree phase. -/
structure ReadyRegs (s : MachineState) : Prop where
  regs : Leaves.Regs s 0 0
  out : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424

/-- Entry conditions of a level pass at word index `W`. -/
structure Entry (W : Nat) (s : MachineState) : Prop where
  pc : s.pc=BitVec.ofNat 64 (4096+4*W)
  heap : s.getReg .x9=4294971424
  out : s.getReg .x8=4294971392
  selector : s.getReg .x5=0
  size : s.getReg .x11=200
  primitive : s.getReg .x13=1

theorem entry_post {k : Nat} (L : Layout k) (s : MachineState) (e : Entry L.W s)
    {out : MachineState} (hit : out ∈ support (levelTrace L s)) : Entry (L.T+3*L.r+L.z) out := by
  obtain ⟨pc,keep⟩ := level_post L s e.pc e.heap e.selector e.size e.primitive hit
  exact ⟨pc,(keep .x9 (by decide) (by decide) (by decide)).trans e.heap,
    (keep .x8 (by decide) (by decide) (by decide)).trans e.out,
    (keep .x5 (by decide) (by decide) (by decide)).trans e.selector,
    (keep .x11 (by decide) (by decide) (by decide)).trans e.size,
    (keep .x13 (by decide) (by decide) (by decide)).trans e.primitive⟩

theorem chain_level {k : Nat} (L : Layout k) (s : MachineState) (e : Entry L.W s) (rest fuel C N : Nat)
    (cont : MachineState → OracleComp World MachineState)
    (later : ∀ out, Entry (L.T+3*L.r+L.z) out →
      execute image (rest+fuel) out true =
        (do let o ← cont out
            let result ← execute image fuel o true
            return result.charge C N)) :
    execute image (levelSteps L+rest+fuel) s true =
      (do let o ← (levelTrace L s >>= cont)
          let result ← execute image fuel o true
          return result.charge (levelCycles L+C) (pentaCount (k+1)+N)) := by
  rw [Nat.add_assoc,level_run L s e.pc e.heap e.selector e.size e.primitive]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro out hit
  rw [later out (entry_post L s e hit)]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;intro o
  apply bind_congr;intro result
  simp only [Execution.charge]
  congr 2 <;> omega

def levels (s : MachineState) : OracleComp World MachineState := do
  let s1 ← levelTrace layout1 s
  let s2 ← levelTrace layout2 s1
  let s3 ← levelTrace layout3 s2
  let s4 ← levelTrace layout4 s3
  let s5 ← levelTrace layout5 s4
  let s6 ← levelTrace layout6 s5
  let s7 ← levelTrace layout7 s6
  let s8 ← levelTrace layout8 s7
  let s9 ← levelTrace layout9 s8
  let s10 ← levelTrace layout10 s9
  pure s10

theorem levels_run (s : MachineState) (e : Entry 45217 s) (fuel : Nat) :
    execute image (12583425+fuel) s true =
      (do let out ← levels s
          let result ← execute image fuel out true
          return result.charge 41943574 4194307) := by
  have finish (out : MachineState) (e : Entry 236533 out) :
      execute image (0+fuel) out true =
        (do let o ← pure out
            let result ← execute image fuel o true
            return result.charge 0 0) := by
    simp [Execution.charge]
  have s10 := fun s e => chain_level layout10 s e 0 fuel 0 0 pure finish
  have s9 := fun s e => chain_level layout9 s e _ fuel _ _ _ (fun out e' => s10 out e')
  have s8 := fun s e => chain_level layout8 s e _ fuel _ _ _ (fun out e' => s9 out e')
  have s7 := fun s e => chain_level layout7 s e _ fuel _ _ _ (fun out e' => s8 out e')
  have s6 := fun s e => chain_level layout6 s e _ fuel _ _ _ (fun out e' => s7 out e')
  have s5 := fun s e => chain_level layout5 s e _ fuel _ _ _ (fun out e' => s6 out e')
  have s4 := fun s e => chain_level layout4 s e _ fuel _ _ _ (fun out e' => s5 out e')
  have s3 := fun s e => chain_level layout3 s e _ fuel _ _ _ (fun out e' => s4 out e')
  have s2 := fun s e => chain_level layout2 s e _ fuel _ _ _ (fun out e' => s3 out e')
  have s1 := chain_level layout1 s e _ fuel _ _ _ (fun out e' => s2 out e')
  have steps : 12583425=levelSteps layout1+(levelSteps layout2+(levelSteps layout3+(levelSteps layout4+
      (levelSteps layout5+(levelSteps layout6+(levelSteps layout7+(levelSteps layout8+(levelSteps layout9+
      (levelSteps layout10+0))))))))) := by decide
  have cycles : levelCycles layout1+(levelCycles layout2+(levelCycles layout3+(levelCycles layout4+
      (levelCycles layout5+(levelCycles layout6+(levelCycles layout7+(levelCycles layout8+(levelCycles layout9+
      (levelCycles layout10+0)))))))))=41943574 := by decide
  have calls : pentaCount (0+1)+(pentaCount (1+1)+(pentaCount (2+1)+(pentaCount (3+1)+(pentaCount (4+1)+
      (pentaCount (5+1)+(pentaCount (6+1)+(pentaCount (7+1)+(pentaCount (8+1)+(pentaCount (9+1)+0)))))))))=4194307 := by
    decide
  rw [cycles,calls] at s1
  rw [steps]
  exact s1

def body (ready : MachineState) : OracleComp World MachineState := do
  let first ← Leaves.unitTrace ready 0 0
  let leaves ← Leaves.groups 4097 0 first
  let tops ← levels (zeroed leaves 32 16 16)
  let reply ← World.query (.inr (.inr (.inl (packBuffer (window (memoryView tops) (pentaGroupWord 10 0))))))
  return rootPrefix (writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply) 10

attribute [local irreducible] body Leaves.unitTrace Leaves.groups levels

/-- From the leaf-entry state: the first leaf, 4097 leaf passes, the level-0 ragged slots,
levels 1 .. 10, the root node, root copy and HALT. -/
theorem execute_after_ready (ready : MachineState) (r : ReadyRegs ready) (fuel : Nat) :
    execute image (197583502+fuel) ready true =
      (do let result ← body ready
          return ⟨.success,result,461824682,37748740⟩) := by
  have rs := r.regs
  rw [show 197583502+fuel=11+Leaves.extra 0+((45155*4097-1)+(16+(12583425+(5+(11+fuel))))) by
      simp [Leaves.extra,Leaves.heapExtra,Leaves.nonceExtra,Leaves.adjustExtra];omega,
    Leaves.unit_run ready 0 0 _ (by decide) (by decide) rs]
  simp only [body,bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro first reached
  have r1 := Leaves.unit_post ready 0 0 (by decide) (by decide) rs reached
  have out1 : first.getReg .x8=4294971392 :=
    (Leaves.unit_saved ready 0 0 .x8 (by simp [Leaves.SavedReg]) reached).trans r.out
  rw [Leaves.groups_run first 4097 0 _ (by decide) (fun _ => r1) out1]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro leaves reachedL
  obtain ⟨leafPC,leafDest,keep⟩ := Leaves.groups_post first 4097 0 (by decide) r1 (by decide) reachedL
  have saved (reg : Reg) (h : Leaves.SavedReg reg) : leaves.getReg reg=ready.getReg reg :=
    (keep reg h).trans (Leaves.unit_saved ready 0 0 reg h reached)
  rw [zero_run 45201 32 16 leaf_zero_segment (by decide) leaves (Leaves.leafDest (2^24-1)) leafPC leafDest
    (by decide) (by decide) (by decide)]
  simp only [bind_assoc,pure_bind]
  let z := zeroed leaves 32 16 16
  have regZ (reg : Reg) : z.getReg reg=leaves.getReg reg := zeroed_reg leaves 32 16 16 le_rfl reg
  have entry : Entry 45217 z := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [zeroed_pc leaves 32 16 16 le_rfl,leafPC];rfl
    · rw [regZ,saved .x9 (by simp [Leaves.SavedReg]),r.heap]
    · rw [regZ,saved .x8 (by simp [Leaves.SavedReg]),r.out]
    · rw [regZ,saved .x5 (by simp [Leaves.SavedReg]),rs.selector]
    · rw [regZ,saved .x11 (by simp [Leaves.SavedReg]),rs.size]
    · rw [regZ,saved .x13 (by simp [Leaves.SavedReg]),rs.primitive]
  rw [levels_run z entry]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro tops reachedT
  have entryT : Entry 236533 tops := by
    simp only [levels,mem_support_bind_iff] at reachedT
    obtain ⟨s1,h1,s2,h2,s3,h3,s4,h4,s5,h5,s6,h6,s7,h7,s8,h8,s9,h9,h10⟩ := reachedT
    have e1 := entry_post layout1 _ entry h1
    have e2 := entry_post layout2 _ e1 h2
    have e3 := entry_post layout3 _ e2 h3
    have e4 := entry_post layout4 _ e3 h4
    have e5 := entry_post layout5 _ e4 h5
    have e6 := entry_post layout6 _ e5 h6
    have e7 := entry_post layout7 _ e6 h7
    have e8 := entry_post layout8 _ e7 h8
    have e9 := entry_post layout9 _ e8 h9
    exact entry_post layout10 _ e9 h10
  rw [execute_root_node tops entryT.pc entryT.heap entryT.selector entryT.size entryT.primitive]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro reply
  let w := writeBits (rootNode tops 4) (wordAddress (heapWord 1)) reply
  have wpc : w.pc=950248 := by
    change (writeBits _ _ _).pc=_
    rw [written_pc]
    simp only [rootNode,rootNodeOps,List.take,List.foldl,execInstrBr,MachineState.setPC,entryT.pc];rfl
  have wheap : w.getReg .x9=4294971424 := by
    change (writeBits _ _ _).getReg .x9=_
    rw [CommitGolfCandidate.writeBits_register,root_node_keep tops .x9 (by decide) (by decide),entryT.heap]
  have wout : w.getReg .x8=4294971392 := by
    change (writeBits _ _ _).getReg .x8=_
    rw [CommitGolfCandidate.writeBits_register,root_node_keep tops .x8 (by decide) (by decide),entryT.out]
  rw [execute_root w wpc wheap wout]
  simp only [pure_bind,Execution.charge]
  simp [Leaves.extra,Leaves.heapExtra,Leaves.nonceExtra,Leaves.adjustExtra,w]

end TwoPermutationPrototype.Quad.Commit
