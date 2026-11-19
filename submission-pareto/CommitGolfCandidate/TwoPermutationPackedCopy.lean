import CommitGolfCandidate.ProjectedHalfwordMemory

/-! The packed opener and checker use straight-line pairs of LHU and SH.
The exact image provides a fetch proof for every offset. -/
namespace TwoPermutationPrototype.Packed
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp ProjectedHalfword
set_option maxRecDepth 8192
set_option maxHeartbeats 1100000
attribute [local irreducible] execute

structure CopyCode where
  image : Image
  start : Nat
  count : Nat
  source : Reg
  dest : Reg
  destOffset : Nat
  sourceTemp : source≠.x31
  destTemp : dest≠.x31
  offsetBound : destOffset+2*count≤64
  load : ∀ j, j<count → ∀ s : MachineState, s.pc=BitVec.ofNat 64 (4096+4*(start+2*j)) →
    fetch image s=some (.base (.LHU .x31 source (BitVec.ofNat 12 (2*j))))
  store : ∀ j, j<count → ∀ s : MachineState, s.pc=BitVec.ofNat 64 (4096+4*(start+2*j+1)) →
    fetch image s=some (.base (.SH dest .x31 (BitVec.ofNat 12 (destOffset+2*j))))

structure CopyReady (code : CopyCode) (s : MachineState) (source target j : Nat) : Prop where
  pc : s.pc=BitVec.ofNat 64 (4096+4*(code.start+2*j))
  src : s.getReg code.source=BitVec.ofNat 64 source
  dst : s.getReg code.dest+BitVec.ofNat 64 code.destOffset=BitVec.ofNat 64 target
  srcBound : source+2*code.count≤MEMORY_BYTES
  dstBound : target+2*code.count≤MEMORY_BYTES
  srcAligned : source%2=0
  dstAligned : target%2=0

private def copyLoad (c : CopyCode) (s : MachineState) (i : Nat) :=
  (s.setReg .x31 ((s.getHalfword (s.getReg c.source+BitVec.ofNat 64 (2*i))).zeroExtend 64)).setPC (s.pc+4)

def copyStep (c : CopyCode) (s : MachineState) (i : Nat) :=
  let loaded := copyLoad c s i
  (loaded.setHalfword (s.getReg c.dest+BitVec.ofNat 64 (c.destOffset+2*i))
    ((loaded.getReg .x31).truncate 16)).setPC (loaded.pc+4)

def copyRun (code : CopyCode) : Nat → Nat → MachineState → MachineState
  | _, 0, state => state
  | j, n+1, state => copyRun code (j+1) n (copyStep code state j)

def copyField (code : CopyCode) (s : MachineState) := copyRun code 0 code.count s

private theorem small_sign (n : Nat) (bounded : n<64) :
    signExtend12 (BitVec.ofNat 12 n)=BitVec.ofNat 64 n := by
  interval_cases n <;> rfl

private theorem load_reg (c : CopyCode) (s : MachineState) (j : Nat) (r : Reg) (kept : r≠.x31) :
    (copyLoad c s j).getReg r=s.getReg r := by
  simp only [copyLoad,MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm kept)]

private theorem copy_step_reg (c : CopyCode) (s : MachineState) (j : Nat) (r : Reg) (kept : r≠.x31) :
    (copyStep c s j).getReg r=s.getReg r := by
  have st (u : MachineState) (a : Word) (v : BitVec 16) : (u.setHalfword a v).getReg r=u.getReg r :=
    by cases r <;> rfl
  simp only [copyStep,MachineState.getReg_setPC,st,load_reg _ _ _ _ kept]

private theorem check_half (address : Nat) (bounded : address+2≤MEMORY_BYTES) (aligned : address%2=0) :
    accessValid (BitVec.ofNat 64 address) 2=true := by
  have limit : MEMORY_BYTES<2^64 := by decide
  simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : address<2^64),
    Bool.and_eq_true,decide_eq_true_eq]
  exact ⟨bounded,aligned⟩

private theorem dst_addr (c : CopyCode) (s : MachineState) (target j : Nat)
    (dest : s.getReg c.dest+BitVec.ofNat 64 c.destOffset=BitVec.ofNat 64 target) :
    s.getReg c.dest + BitVec.ofNat 64 (c.destOffset+2*j)=BitVec.ofNat 64 (target+2*j) := by
  rw [BitVec.ofNat_add c.destOffset,← BitVec.add_assoc,dest,← BitVec.ofNat_add]

private theorem step_execute (c : CopyCode) (s : MachineState) (source target j : Nat)
    (ready : CopyReady c s source target j) (bounded : j<c.count) (fuel : Nat) (coins : Bool) :
    execute c.image (2+fuel) s coins = do
      let result ← execute c.image fuel (copyStep c s j) coins
      return result.charge 2 0 := by
  have size := c.offsetBound
  have sw := ready.srcBound
  have tw := ready.dstBound
  have sal := ready.srcAligned
  have tal := ready.dstAligned
  have sa : s.getReg c.source+BitVec.ofNat 64 (2*j)=BitVec.ofNat 64 (source+2*j) := by
    rw [ready.src,←BitVec.ofNat_add]
  have da := dst_addr c s target j ready.dst
  have validSrc := check_half (source+2*j) (by omega) (by omega)
  have validDst := check_half (target+2*j) (by omega) (by omega)
  have signS := small_sign (2*j) (by omega)
  have signT := small_sign (c.destOffset+2*j) (by omega)
  let l := copyLoad c s j
  have stepL : ordinaryStep s (.base (.LHU .x31 c.source (BitVec.ofNat 12 (2*j))))=some l := by
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,signS,sa,validSrc,↓reduceIte,
      execInstrBr,l,copyLoad]
  have lpc : l.pc=BitVec.ofNat 64 (4096+4*(c.start+2*j+1)) := by
    change s.pc+4=_
    rw [ready.pc,show (4:Word)=BitVec.ofNat 64 4 by rfl,←BitVec.ofNat_add]
    congr 1
  have stepS : ordinaryStep l (.base (.SH c.dest .x31 (BitVec.ofNat 12 (c.destOffset+2*j))))=
      some (copyStep c s j) := by
    have destL : l.getReg c.dest=s.getReg c.dest := load_reg _ _ _ _ c.destTemp
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,signT,destL,da,validDst,↓reduceIte,execInstrBr]
    simp only [da,copyStep,l]
  have first := execute_ordinary_step c.image _ s l (fuel+1) coins (c.load _ bounded _ ready.pc) stepL
  have second := execute_ordinary_step c.image _ l (copyStep c s j) fuel coins (c.store _ bounded _ lpc) stepS
  rw [show 2+fuel=(fuel+1)+1 by omega,first,second]
  simp only [instructionCycles,bind_assoc,pure_bind,Execution.charge,Nat.zero_add,←Nat.add_assoc]

private theorem step_ready (c : CopyCode) (s : MachineState) (source target j : Nat)
    (ready : CopyReady c s source target j) :
    CopyReady c (copyStep c s j) source target (j+1) := by
  refine ⟨?_,(copy_step_reg _ _ _ _ c.sourceTemp).trans ready.src,?_,ready.srcBound,
    ready.dstBound,ready.srcAligned,ready.dstAligned⟩
  · change s.pc+4+4=_
    rw [ready.pc,BitVec.add_assoc,show (4:Word)+4=BitVec.ofNat 64 8 by rfl,← BitVec.ofNat_add]
    congr 1
  · rw [copy_step_reg _ _ _ _ c.destTemp,ready.dst]

private theorem step_memory (c : CopyCode) (s : MachineState) (source target j : Nat)
    (ready : CopyReady c s source target j) :
    (copyStep c s j).mem =
      (s.setHalfword (BitVec.ofNat 64 (target+2*j)) (s.getHalfword (BitVec.ofNat 64 (source+2*j)))).mem := by
  have addr := dst_addr c s target j ready.dst
  have sourceAddr : s.getReg c.source+BitVec.ofNat 64 (2*j)=BitVec.ofNat 64 (source+2*j) := by
    rw [ready.src,←BitVec.ofNat_add]
  have value : ((copyLoad c s j).getReg .x31).truncate 16 = s.getHalfword (BitVec.ofNat 64 (source+2*j)) := by
    simp only [copyLoad,sourceAddr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide : Reg.x31≠.x0)]
    generalize s.getHalfword (BitVec.ofNat 64 (source+2*j))=x
    apply BitVec.eq_of_toNat_eq
    have fit : x.toNat < 2^16 := x.isLt
    simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (show x.toNat < 2^64 by omega)]
  change ((copyLoad c s j).setHalfword _ _).mem=_
  rw [addr,value]
  rfl

private theorem run_execute (c : CopyCode) (s : MachineState) (source target j n : Nat)
    (ready : CopyReady c s source target j) (bounded : j+n≤c.count) (fuel : Nat) (coins : Bool) :
    execute c.image (2*n+fuel) s coins = do
      let result ← execute c.image fuel (copyRun c j n s) coins
      return result.charge (2*n) 0 := by
  induction n generalizing s j with
  | zero => simp [copyRun,Execution.charge]
  | succ n ih =>
    rw [show 2*(n+1)+fuel=2+(2*n+fuel) by omega,step_execute c s source target j ready (by omega),
      ih _ _ (step_ready _ _ _ _ _ ready) (by omega)]
    simp only [copyRun,bind_assoc,pure_bind,Execution.charge,Nat.zero_add]
    congr 1
    funext result
    congr 2
    omega

private theorem run_memory (c : CopyCode) (s : MachineState) (source target j n : Nat)
    (ready : CopyReady c s source target j) :
    (copyRun c j n s).mem =
      (copyLoopMemory false n s (BitVec.ofNat 64 (source+2*j)) (BitVec.ofNat 64 (target+2*j))).mem := by
  induction n generalizing s j with
  | zero => rfl
  | succ n ih =>
    rw [copyRun,ih _ _ (step_ready _ _ _ _ _ ready),copyLoopMemory]
    have adv (n : Nat) : advance false (BitVec.ofNat 64 (n+2*j))=BitVec.ofNat 64 (n+2*(j+1)) := by
      change BitVec.ofNat 64 (n+2*j)+BitVec.ofNat 64 2=_
      rw [←BitVec.ofNat_add]
      congr 1
    rw [adv,adv]
    exact copyLoopMemory_congr _ _ _ _ _ _ (step_memory _ _ _ _ _ ready)

theorem copy_field_execute (c : CopyCode) (s : MachineState) (source target : Nat)
    (ready : CopyReady c s source target 0) (fuel : Nat) (coins : Bool) :
    execute c.image (2*c.count+fuel) s coins = do
      let result ← execute c.image fuel (copyField c s) coins
      return result.charge (2*c.count) 0 := run_execute _ _ _ _ _ _ ready (by omega) _ _

theorem copy_field_memory (c : CopyCode) (s : MachineState) (source target : Nat)
    (ready : CopyReady c s source target 0) :
    (copyField c s).mem=(copyLoopMemory false c.count s (BitVec.ofNat 64 source) (BitVec.ofNat 64 target)).mem := by
  simpa only [copyField,Nat.mul_zero,Nat.add_zero] using run_memory c s source target 0 c.count ready

theorem copy_field_register (c : CopyCode) (s : MachineState) (reg : Reg) (kept : reg≠.x31) :
    (copyField c s).getReg reg=s.getReg reg := by
  have aux (j n : Nat) (st : MachineState) : (copyRun c j n st).getReg reg=st.getReg reg := by
    induction n generalizing j st with
    | zero => rfl
    | succ n ih => exact (ih (j+1) (copyStep c st j)).trans (copy_step_reg c st j reg kept)
  exact aux _ _ _

theorem copy_field_pc (c : CopyCode) (s : MachineState) (source target : Nat)
    (ready : CopyReady c s source target 0) :
    (copyField c s).pc=BitVec.ofNat 64 (4096+4*(c.start+2*c.count)) := by
  have aux (j n : Nat) (st : MachineState) (r : CopyReady c st source target j) :
      (copyRun c j n st).pc=BitVec.ofNat 64 (4096+4*(c.start+2*(j+n))) := by
    induction n generalizing j st with
    | zero => simpa only [copyRun,Nat.add_zero] using r.pc
    | succ n ih =>
      simpa only [copyRun,show j+1+n=j+(n+1) by omega] using ih _ _ (step_ready _ _ _ _ _ r)
  simpa only [copyField,Nat.zero_add] using aux 0 c.count s ready

end TwoPermutationPrototype.Packed
