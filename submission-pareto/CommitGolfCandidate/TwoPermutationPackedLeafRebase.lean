import CommitGolfCandidate.TwoPermutationPackedLeafProduction

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
attribute [local irreducible] execute packedWideCommitImage

def heapExtra (u : Nat) : Nat := if u%64=63 then 1 else 0
def nonceExtra (u : Nat) : Nat := if u%128=127 then 1 else 0
def extra (u : Nat) := heapExtra u + nonceExtra u

def heapUpdate (s : MachineState) := (s.setReg .x20 (s.getReg .x12+32)).setPC (s.pc+4)
def nonceUpdate (s : MachineState) := (s.setReg .x22 (s.getReg .x22+s.getReg .x7)).setPC (s.pc+4)
def rebased (s : MachineState) (u : Nat) :=
  let h := if u%64=63 then heapUpdate s else s
  if u%128=127 then nonceUpdate h else h

theorem heap_at (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11) (h : u.val%64=63) (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (heapUpdate s) true
          return out.charge 1 0) := by
  let tile : Fin 64 := ⟨u.val/64, by have := u.isLt;omega⟩
  have pc : s.pc=BitVec.ofNat 64 (4096+4*packed_heapRebaseIndex tile.val) := by
    rw [here];unfold leafPC packed_wideLeafPC packed_heapRebaseIndex
    have same : 64*tile.val+63=u.val := by dsimp [tile];omega
    rw [same]
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (packed_wide_fetch_heap_rebase tile s pc) (show ordinaryStep s _=some (heapUpdate s) by rfl)]
  rfl

theorem nonce_at (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11+4) (h : u.val%128=127) (fuel : Nat) :
    execute packedWideCommitImage (1+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (nonceUpdate s) true
          return out.charge 1 0) := by
  let seg : Fin 32 := ⟨u.val/128, by have := u.isLt;omega⟩
  have pc : s.pc=BitVec.ofNat 64 (4096+4*packed_nonceRebaseIndex seg.val) := by
    rw [here];unfold leafPC packed_wideLeafPC packed_nonceRebaseIndex
    have same : 128*seg.val+127=u.val := by dsimp [seg];omega
    rw [same]
    change BitVec.ofNat 64 _+BitVec.ofNat 64 4=_;rw [←BitVec.ofNat_add];congr 1 <;> omega
  rw [Nat.add_comm 1 fuel,CommitGolfCandidate.execute_ordinary_step _ _ _ _ _ _
    (packed_wide_fetch_nonce_rebase seg s pc) (show ordinaryStep s _=some (nonceUpdate s) by rfl)]
  rfl

theorem rebase_run (s : MachineState) (u : Fin 4096) (here : s.pc=leafPC u 11) (fuel : Nat) :
    execute packedWideCommitImage (extra u.val+fuel) s true =
      (do let out ← execute packedWideCommitImage fuel (rebased s u.val) true
          return out.charge (extra u.val) 0) := by
  by_cases h : u.val%64=63
  · by_cases n : u.val%128=127
    · simp only [extra,heapExtra,nonceExtra,rebased,h,n,ite_true]
      rw [show 1+1+fuel=1+(1+fuel) by omega,heap_at s u here h]
      have next : (heapUpdate s).pc=leafPC u 11+4 := congrArg (·+4) here
      rw [nonce_at _ u next n]
      simp [Execution.charge,←Nat.add_assoc]
    · simpa only [extra,heapExtra,nonceExtra,rebased,h,n,ite_true,ite_false,Nat.add_zero] using heap_at s u here h fuel
  · have n : u.val%128≠127 := by omega
    simp [extra,heapExtra,nonceExtra,rebased,h,n,Execution.charge]

theorem extra_count (u : Nat) : (u+1)/64+(u+1)/128 = u/64+u/128+extra u := by
  unfold extra heapExtra nonceExtra
  split <;> split <;> omega

private theorem pc_step (u : Fin 4096) :
    leafPC u 11+BitVec.ofNat 64 (4*extra u.val)=packed_wideLeafPC (u.val+1) 0 := by
  unfold leafPC packed_wideLeafPC packed_wideLeafIndex
  rw [←BitVec.ofNat_add];congr 1 <;> have := extra_count u.val <;> omega

private theorem next_heap (g u : Nat) (h : u%64=63) :
    wordAddress (leafDest (4096*g+u))+32=wordAddress (heapBase g (u+1)) := by
  change wordAddress _+wordAddress 4=_;rw [←wordAddress_add];congr 1 <;> unfold heapBase leafDest <;> omega

private theorem next_nonce (g u : Nat) (h : u%128=127) :
    wordAddress (nonceBase g u)+2048=wordAddress (nonceBase g (u+1)) := by
  change wordAddress _+wordAddress 256=_;rw [←wordAddress_add];congr 1 <;> unfold nonceBase leafSalt <;> omega

theorem rebase_regs (s : MachineState) (g : Nat) (u : Fin 4096) (r : RawRegs s g u) :
    Regs (rebased s u.val) g (u.val+1) := by
  have src : s.getReg .x10=wordAddress (leafStart (4096*g+(u.val+1))+5) := by simpa only [idx,Nat.add_assoc] using r.source
  have pc := pc_step u
  by_cases h : u.val%64=63
  · by_cases n : u.val%128=127
    · simp only [rebased,h,n,ite_true]
      simp only [extra,heapExtra,nonceExtra,h,n,ite_true] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x12+32=_;rw [r.dest];exact next_heap g u.val h
      · change s.getReg .x22+s.getReg .x7=_;rw [r.salts,r.stride];exact next_nonce g u.val n
      · change s.pc+4+4=_;rw [r.pc,BitVec.add_assoc];exact pc
    · simp only [rebased,h,n,ite_true,ite_false]
      simp only [extra,heapExtra,nonceExtra,h,n,ite_true,ite_false] at pc
      refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
      · change s.getReg .x12+32=_;rw [r.dest];exact next_heap g u.val h
      · change s.getReg .x22=_;rw [r.salts];unfold nonceBase;rw [show (u.val+1)/128=u.val/128 by omega]
      · change s.pc+4=_;rw [r.pc];exact pc
  · have n : u.val%128≠127 := by omega
    simp only [rebased,h,n,ite_false]
    simp only [extra,heapExtra,nonceExtra,h,n,ite_false] at pc
    refine ⟨src,?_,?_,r.stride,r.selector,r.size,r.primitive,?_⟩
    · rw [r.heap];unfold heapBase;rw [show (u.val+1)/64=u.val/64 by omega]
    · rw [r.salts];unfold nonceBase;rw [show (u.val+1)/128=u.val/128 by omega]
    · rw [r.pc];simpa using pc

theorem rebase_mem (s : MachineState) (u : Nat) : (rebased s u).mem=s.mem := by
  unfold rebased;split <;> split <;> rfl

end TwoPermutationPrototype.RV64.PackedLeaves
