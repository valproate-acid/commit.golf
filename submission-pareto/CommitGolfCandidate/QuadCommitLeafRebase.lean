import CommitGolfCandidate.QuadCommitLeafControlFetch
import CommitGolfCandidate.QuadCommitLeafProduction

/-! Exact rebases of the centered 45-leaf output window and the centered 256-leaf salt window,
and the end-of-body salt step back (the loop re-enters at leaf 1). -/
namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute image

def heapUpdate (s : MachineState) := (s.setReg .x20 (s.getReg .x12+1776)).setPC (s.pc+4)
def nonceUpdate (s : MachineState) := (s.setReg .x22 (s.getReg .x22+s.getReg .x7)).setPC (s.pc+4)
def adjustUpdate (s : MachineState) := (s.setReg .x22 (s.getReg .x22+signExtend12 4080)).setPC (s.pc+4)
def rebased (s : MachineState) (u : Nat) :=
  let h := if u%45=44 then heapUpdate s else s
  let n := if u%256=127 then nonceUpdate h else h
  if u=4095 then adjustUpdate n else n

theorem heap_at (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11)
    (h : u.val%45=44) (fuel : Nat) :
    execute image (1+fuel) s true =
      (do let out ← execute image fuel (heapUpdate s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_heap_rebase u h s here) (show ordinaryStep s _=some (heapUpdate s) by rfl)]
  rfl

theorem nonce_at (s : MachineState) (u : Fin 4096)
    (here : s.pc=leafPC u (11+heapExtra u.val)) (h : u.val%256=127) (fuel : Nat) :
    execute image (1+fuel) s true =
      (do let out ← execute image fuel (nonceUpdate s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_nonce_rebase u h s here) (show ordinaryStep s _=some (nonceUpdate s) by rfl)]
  rfl

theorem adjust_at (s : MachineState) (u : Fin 4096)
    (here : s.pc=leafPC u 11) (h : u.val=4095) (fuel : Nat) :
    execute image (1+fuel) s true =
      (do let out ← execute image fuel (adjustUpdate s) true
          return out.charge 1 0) := by
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (fetch_salt_adjust u h s here) (show ordinaryStep s _=some (adjustUpdate s) by rfl)]
  rfl

theorem rebase_run (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11) (fuel : Nat) :
    execute image (extra u.val+fuel) s true =
      (do let out ← execute image fuel (rebased s u.val) true
          return out.charge (extra u.val) 0) := by
  by_cases last : u.val=4095
  · have h : ¬ u.val%45=44 := by omega
    have n : ¬ u.val%256=127 := by omega
    have count : extra u.val=1 := by
      unfold extra heapExtra nonceExtra adjustExtra; rw [if_neg h,if_neg n,if_pos last]
    have shape : rebased s u.val=adjustUpdate s := by
      simp only [rebased,if_neg h,if_neg n,if_pos last]
    rw [count,shape,adjust_at s u here last]
  have a : adjustExtra u.val=0 := by simp [adjustExtra,last]
  by_cases h : u.val%45=44
  · by_cases n : u.val%256=127
    · simp only [extra,a,heapExtra,nonceExtra,rebased,h,n,last,ite_true,ite_false,Nat.add_zero]
      rw [show 1+1+fuel=1+(1+fuel) by omega,heap_at s u here h]
      have next : (heapUpdate s).pc=leafPC u (11+heapExtra u.val) := by
        change s.pc+4=_
        rw [here,heapExtra,if_pos h]
        exact leaf_pc_add u 11 1
      rw [nonce_at _ u next n]
      simp [Execution.charge,←Nat.add_assoc]
    · simpa only [extra,a,heapExtra,nonceExtra,rebased,h,n,last,ite_true,ite_false,Nat.add_zero] using heap_at s u here h fuel
  · by_cases n : u.val%256=127
    · have next : s.pc=leafPC u (11+heapExtra u.val) := by simpa only [heapExtra,if_neg h,Nat.add_zero] using here
      simpa only [extra,a,heapExtra,nonceExtra,rebased,h,n,last,ite_false,ite_true,Nat.zero_add,Nat.add_zero] using nonce_at s u next n fuel
    · simp [extra,a,heapExtra,nonceExtra,rebased,h,n,last,Execution.charge]

private theorem pc_step (u : Fin 4096) :
    leafPC u 11+BitVec.ofNat 64 (4*extra u.val)=BitVec.ofNat 64 (4096+4*leafIndex (u.val+1)) := by
  unfold leafPC
  rw [←BitVec.ofNat_add,leaf_index_next]
  congr 1 <;> omega

private theorem next_heap (g u : Nat) (hu : u<4096) (h : u%45=44) :
    wordAddress (leafDest (4095*g+u))+1776=wordAddress (heapBase g (u+1)) := by
  change wordAddress _+wordAddress 222=_
  rw [←wordAddress_add]
  congr 1
  unfold heapBase windowWord leafDest leafWord groupWord
  omega

private theorem same_heap (g u : Nat) (hu : u<4096) (h : ¬u%45=44) :
    heapBase g u=heapBase g (u+1) := by
  unfold heapBase windowWord
  congr 2
  omega

private theorem next_nonce (g u : Nat) (hu : u<4095) (h : u%256=127) :
    wordAddress (nonceBase g u)+4096=wordAddress (nonceBase g (u+1)) := by
  change wordAddress _+wordAddress 512=_
  rw [←wordAddress_add]
  congr 1
  unfold nonceBase leafSalt Commit.saltWord
  rw [if_neg (by omega),if_neg (by omega)]
  omega

private theorem step_back (a : Nat) : wordAddress (a+2)+signExtend12 4080=wordAddress a := by
  rw [wordAddress_add,BitVec.add_assoc,show wordAddress 2+signExtend12 4080=0 by decide +kernel]
  exact BitVec.add_zero _

private theorem last_nonce (g : Nat) :
    wordAddress (nonceBase g 4095)+signExtend12 4080=wordAddress (nonceBase g 4096) := by
  rw [show nonceBase g 4095=nonceBase g 4096+2 by
    unfold nonceBase leafSalt Commit.saltWord
    rw [if_neg (by omega),if_pos rfl]
    omega]
  exact step_back _

private theorem same_nonce (g u : Nat) (hu : u<4095) (h : ¬u%256=127) :
    nonceBase g u=nonceBase g (u+1) := by
  unfold nonceBase
  rw [if_neg (by omega),if_neg (by omega),show (u+1+128)/256=(u+128)/256 by omega]

theorem rebase_regs (s : MachineState) (g : Nat) (u : Fin 4096) (r : RawRegs s g u) :
    Regs (rebased s u.val) g (u.val+1) := by
  have src : s.getReg .x10=wordAddress (leafStart (4095*g+(u.val+1))+5) := by
    simpa only [idx,Nat.add_assoc] using r.source
  have pc := pc_step u
  by_cases last : u.val=4095
  · have h : ¬ u.val%45=44 := by omega
    have n : ¬ u.val%256=127 := by omega
    have count : extra u.val=1 := by
      unfold extra heapExtra nonceExtra adjustExtra; rw [if_neg h,if_neg n,if_pos last]
    have shape : rebased s u.val=adjustUpdate s := by
      simp only [rebased,if_neg h,if_neg n,if_pos last]
    rw [count] at pc
    rw [shape]
    refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
    · change s.getReg .x20=_
      rw [r.heap,same_heap g u.val u.isLt h]
    · change s.getReg .x22+signExtend12 4080=_
      rw [r.salts,last]
      exact last_nonce g
    · change s.pc+4=_
      rw [r.pc]
      exact pc
  have a : adjustExtra u.val=0 := by simp [adjustExtra,last]
  have lt : u.val<4095 := by omega
  by_cases h : u.val%45=44
  · by_cases n : u.val%256=127
    · simp only [rebased,h,n,last,ite_true,ite_false]
      simp only [extra,a,heapExtra,nonceExtra,h,n,ite_true,Nat.add_zero] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x12+1776=_
        rw [r.dest]
        exact next_heap g u.val u.isLt h
      · change s.getReg .x22+s.getReg .x7=_
        rw [r.salts,r.stride]
        exact next_nonce g u.val lt n
      · change s.pc+4+4=_
        rw [r.pc,BitVec.add_assoc]
        exact pc
    · simp only [rebased,h,n,last,ite_true,ite_false]
      simp only [extra,a,heapExtra,nonceExtra,h,n,ite_true,ite_false,Nat.add_zero] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x12+1776=_
        rw [r.dest]
        exact next_heap g u.val u.isLt h
      · change s.getReg .x22=_
        rw [r.salts,same_nonce g u.val lt n]
      · change s.pc+4=_
        rw [r.pc]
        exact pc
  · by_cases n : u.val%256=127
    · simp only [rebased,h,n,last,ite_false,ite_true]
      simp only [extra,a,heapExtra,nonceExtra,h,n,ite_false,ite_true,Nat.add_zero] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x20=_
        rw [r.heap,same_heap g u.val u.isLt h]
      · change s.getReg .x22+s.getReg .x7=_
        rw [r.salts,r.stride]
        exact next_nonce g u.val lt n
      · change s.pc+4=_
        rw [r.pc]
        exact pc
    · simp only [rebased,h,n,last,ite_false]
      simp only [extra,a,heapExtra,nonceExtra,h,n,ite_false,Nat.add_zero] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · rw [r.heap,same_heap g u.val u.isLt h]
      · rw [r.salts,same_nonce g u.val lt n]
      · rw [r.pc]
        simpa using pc

theorem rebase_mem (s : MachineState) (u : Nat) : (rebased s u).mem=s.mem := by
  unfold rebased
  split <;> split <;> split <;> rfl

end TwoPermutationPrototype.Quad.Commit.Leaves
