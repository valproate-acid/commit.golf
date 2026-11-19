import CommitGolfCandidate.TwoPermutationLeafGroup

/-! Group-end cursor updates and the single backward branch in the submitted
two-permutation commitment image. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute

theorem group_preserved_reg (g count u : Nat) (s : MachineState) (reg : Reg)
    (src : Reg.x10 ≠ reg) (out : Reg.x12 ≠ reg) (tmp : Reg.x31 ≠ reg) {done : MachineState}
    (hit : done ∈ support (groupTrace g count u s)) : done.getReg reg = s.getReg reg := by
  induction count generalizing u s with
  | zero =>
    simp only [groupTrace,support_pure,Set.mem_singleton_iff] at hit
    rw [hit]
  | succ k ih =>
    simp only [groupTrace,slotTrace,leafTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at hit
    obtain ⟨next,⟨a,_,b,_,rfl⟩,tail⟩ := hit
    exact (ih (u+1) _ tail).trans (finished_reg_frame _ _ _ _ a b reg src out tmp)

def nextPC (g : Nat) : Word := if g+1=2^20 then 5132 else 4160

def afterGroup (s : MachineState) (g : Nat) : MachineState :=
  ((s.setReg .x20 (s.getReg .x20 + 512)).setReg .x22 (s.getReg .x22 + 256)).setPC (nextPC g)

theorem next_heap_word (g : Nat) :
    wordAddress (leafDest (16*g)) + 512 = wordAddress (leafDest (16*(g+1))) := by
  change wordAddress (leafDest (16*g)) + wordAddress 64 = _
  rw [← wordAddress_add]; congr 1 <;> simp [leafDest,Nat.mul_add] <;> omega

theorem next_salt_word (g : Nat) :
    wordAddress (leafSalt (16*g)) + 256 = wordAddress (leafSalt (16*(g+1))) := by
  change wordAddress (leafSalt (16*g)) + wordAddress 32 = _
  rw [← wordAddress_add]; congr 1 <;> simp [leafSalt,Nat.mul_add] <;> omega

theorem heap_end_iff (g : Nat) (bound : g < 2^20) :
    wordAddress (leafDest (16*(g+1))) = wordAddress (leafDest (2^24)) ↔ g+1=2^20 := by
  constructor
  · intro h
    have h' := wordAddress_injective_of_bound (a := leafDest (16*(g+1))) (b := leafDest (2^24))
      (by simp [leafDest];omega) (by decide) h
    unfold leafDest at h'; omega
  · intro h
    rw [h]
    rfl

private theorem latch_fetch_0 (s : MachineState) (pc : s.pc=5120) :
    fetch commitImage s=some (.base (.ADDI .x20 .x20 512)) := by rw [fetch,pc];rfl
private theorem latch_fetch_1 (s : MachineState) (pc : s.pc=5124) :
    fetch commitImage s=some (.base (.ADDI .x22 .x22 256)) := by rw [fetch,pc];rfl
private theorem latch_fetch_2 (s : MachineState) (pc : s.pc=5128) :
    fetch commitImage s=some (.base (.BNE .x20 .x21 7224)) := by rw [fetch,pc];rfl

theorem group_latch_run (s : MachineState) (g fuel : Nat) (bound : g < 2^20)
    (r : GroupRegs s g 16) (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) (coins : Bool) :
    execute commitImage (3+fuel) s coins =
      (do let result ← execute commitImage fuel (afterGroup s g) coins
          return result.charge 3 0) := by
  let s1 := execInstrBr s (.ADDI .x20 .x20 512)
  let s2 := execInstrBr s1 (.ADDI .x22 .x22 256)
  have start : s.pc = 5120 := r.pc
  have pc1 : s1.pc = 5124 := by change s.pc + 4 = _;rw [start];rfl
  have pc2 : s2.pc = 5128 := by change s1.pc + 4 = _;rw [pc1];rfl
  have eq : s2.getReg .x20 = s2.getReg .x21 ↔ g+1=2^20 := by
    change s.getReg .x20 + 512 = s.getReg .x21 ↔ _
    rw [r.heap,stop,next_heap_word,heap_end_iff g bound]
  have branch : ordinaryStep s2 (.base (.BNE .x20 .x21 7224)) = some (afterGroup s g) := by
    change some (if s2.getReg .x20 != s2.getReg .x21 then s2.setPC (s2.pc+signExtend13 7224) else s2.setPC (s2.pc+4)) = _
    simp only [bne_iff_ne]
    rw [pc2]
    by_cases done : g+1=2^20
    · rw [if_neg (not_not_intro (eq.mpr done))]
      simp only [afterGroup,nextPC,done,ite_true]
      rfl
    · rw [if_pos (fun equal => done (eq.mp equal))]
      simp only [afterGroup,nextPC,done,ite_false]
      rfl
  rw [show 3+fuel=fuel+1+1+1 by omega,
    CommitGolfCandidate.execute_ordinary_step _ _ _ s1 _ _ (latch_fetch_0 s start) rfl,
    CommitGolfCandidate.execute_ordinary_step _ _ _ s2 _ _ (latch_fetch_1 s1 pc1) rfl,
    CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _ (latch_fetch_2 s2 pc2) branch]
  simp [Execution.charge,instructionCycles,←Nat.add_assoc]

theorem group_latch_next (s : MachineState) (g : Nat) (more : g+1 < 2^20) (r : GroupRegs s g 16) :
    GroupRegs (afterGroup s g) (g+1) 0 := by
  refine ⟨?_,?_,?_,r.selector,r.size,r.primitive,?_⟩
  · change s.getReg .x10 = _
    rw [r.source,show 16*g+16=16*(g+1)+0 by omega]
  · change s.getReg .x20+512=_
    rw [r.heap,next_heap_word]
  · change s.getReg .x22+256=_
    rw [r.salts,next_salt_word]
  · change nextPC g=4160
    exact if_neg (Nat.ne_of_lt more)

end TwoPermutationPrototype.RV64
