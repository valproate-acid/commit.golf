import CommitGolfCandidate.QuadNonceCommitExec

/-! Words 0..13 (24-byte seed RANDOM at saltBase-176), the jump into the generator, the
generator return (x10 := x18, x12 := x9, jump to word 18) and word 18 (x7 := 4096).
The resulting leaf-entry state satisfies `ReadyRegs` (PC 4172). -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
open TwoPermutationPrototype.RV64 Leaves
set_option maxRecDepth 60000
set_option maxHeartbeats 620000
attribute [local irreducible] execute image chainRun

def seedOps : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 0,
   .LUI .x20 1,.ADDI .x20 .x20 1536,.ADD .x20 .x9 .x20,
   .LUI .x22 442369,.ADDI .x22 .x22 0,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 (-176),.ADDI .x11 .x0 24,.ADDI .x11 .x11 0]
def startOps : List Instr :=
  [.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.JAL .x0 946128,
    .ADDI .x12 .x22 0,.LUI .x7 65538,.ADDI .x7 .x7 0,.ADD .x7 .x7 .x22]
def finishOps : List Instr :=
  [.ADDI .x10 .x18 0,.ADDI .x12 .x9 0,.JAL .x0 1147544,.SLLI .x7 .x13 12]

def seedSetup (s : MachineState) := seedOps.foldl execInstrBr s
def seedWritten (s : MachineState) (k : BitVec 192) :=
  writeBits (seedSetup s) (BitVec.ofNat 64 (nonceChainSource 0)) k
def chainInitial (s : MachineState) (k : BitVec 192) := startOps.foldl execInstrBr (seedWritten s k)
def chainFinish (s : MachineState) := finishOps.foldl execInstrBr s

structure Saved (s : MachineState) : Prop where
  root : s.getReg .x8=4294971392
  heap : s.getReg .x9=4294971424
  source : s.getReg .x18=4096
  leaves : s.getReg .x20=wordAddress (heapBase 0 0)
  salts : s.getReg .x22=wordAddress (Leaves.leafSalt 0)

structure SeedRegisters (s : MachineState) : Prop extends Saved s where
  target : s.getReg .x10=BitVec.ofNat 64 (nonceChainSource 0)
  size : s.getReg .x11=24
  selector : s.getReg .x5=2

theorem seed_registers (s : MachineState) (entry : CommitEntry s) : SeedRegisters (seedSetup s) := by
  refine ⟨⟨?_,?_,?_,?_,?_⟩,?_,?_,?_⟩ <;>
    dsimp [seedSetup,seedOps,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [show s.regs .x10=4096 from entry.message,
    show s.regs .x11=4294971392 from entry.commitment,show s.regs .x12=4294971424 from entry.heap]
  all_goals rfl

theorem seed_pc (s : MachineState) (pc : s.pc=4096) : (seedSetup s).pc=4148 := by
  change s.pc+4+4+4+4+4+4+4+4+4+4+4+4+4=_
  rw [pc]
  rfl

private theorem seed_ops_eq (i : Nat) (inside : i<13) :
    (nonceSetupOps[i]?).getD .EBREAK = (seedOps[i]?).getD .EBREAK := by
  interval_cases i <;> rfl

theorem seed_run (s : MachineState) (pc : s.pc=4096) (fuel : Nat) :
    execute image (13+fuel) s true =
      (do let result ← execute image fuel (seedSetup s) true
          return result.charge 13 0) := by
  unfold seedSetup
  apply execute_unit_steps (states := fun i => (seedOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((seedOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · have atPC : ((seedOps.take i).foldl execInstrBr s).pc=BitVec.ofNat 64 (4096+4*i) := by
      interval_cases i <;> simp only [seedOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
    rw [fetch_nonce_setup i (by omega) _ atPC,seed_ops_eq i hi]
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem seed_draw (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (1+fuel) (seedSetup s) true =
      (do let k ← liftM ($ᵗ BitVec 192 : ProbComp (BitVec 192))
          let result ← execute image fuel (seedWritten s k) true
          return result.charge 4 0) := by
  have r := seed_registers s e
  have fetched : fetch image (seedSetup s) = some (.base .ECALL) :=
    fetch_nonce_setup 13 (by decide) _ (seed_pc s e.pc)
  have valid : randomArgumentsValid (seedSetup s) = true := by
    rw [randomArgumentsValid,r.target,r.size];decide
  have raw :
      execute image (1+fuel) (seedSetup s) true =
        (do let k ← liftM ($ᵗ BitVec (8*((seedSetup s).getReg .x11).toNat) :
              ProbComp (BitVec (8*((seedSetup s).getReg .x11).toNat)))
            let result ← execute image fuel
              (writeBits (seedSetup s) ((seedSetup s).getReg .x10) k) true
            return result.charge (1+(((seedSetup s).getReg .x11).toNat+7)/8) 0) := by
    rw [Nat.add_comm 1 fuel,execute,fetched]
    simp only [r.selector,valid]
    rfl
  rw [r.size,r.target] at raw
  exact raw

theorem after_seed (s : MachineState) (e : CommitEntry s) (k : BitVec 192) :
    (seedWritten s k).pc=4152 := by
  rw [seedWritten,written_pc,seed_pc s e.pc]
  rfl

private theorem start_ops_eq (i : Nat) (inside : i<8) :
    (if i<4 then (nonceSetupOps[14+i]?).getD .EBREAK else (genOps[i-4]?).getD .EBREAK) =
      (startOps[i]?).getD .EBREAK := by
  interval_cases i <;> rfl

theorem start_run (s : MachineState) (pc : s.pc=4152) (fuel : Nat) :
    execute image (8+fuel) s true =
      (do let result ← execute image fuel (startOps.foldl execInstrBr s) true
          return result.charge 8 0) := by
  apply execute_unit_steps (states := fun i => (startOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((startOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · rw [←start_ops_eq i hi]
    by_cases low : i<4
    · have atPC : ((startOps.take i).foldl execInstrBr s).pc=BitVec.ofNat 64 (4096+4*(14+i)) := by
        interval_cases i <;> simp only [startOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
      rw [if_pos low]
      exact fetch_nonce_setup (14+i) (by omega) _ atPC
    · have high : 4 ≤ i := by omega
      have atPC : ((startOps.take i).foldl execInstrBr s).pc=BitVec.ofNat 64 (4096+4*(236549+(i-4))) := by
        interval_cases i <;> simp only [startOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
      rw [if_neg low]
      exact fetch_gen (i-4) (by omega) _ atPC
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private theorem finish_ops_eq (i : Nat) (inside : i<4) :
    (if i<3 then (genOps[869+i]?).getD .EBREAK else (nonceSetupOps[18]?).getD .EBREAK) =
      (finishOps[i]?).getD .EBREAK := by
  interval_cases i <;> rfl

theorem finish_run (s : MachineState) (pc : s.pc=953768) (fuel : Nat) :
    execute image (4+fuel) s true =
      (do let result ← execute image fuel (finishOps.foldl execInstrBr s) true
          return result.charge 4 0) := by
  apply execute_unit_steps (states := fun i => (finishOps.take i).foldl execInstrBr s)
  intro i hi
  refine ⟨.base ((finishOps[i]?).getD .EBREAK),?_,?_,?_⟩
  · rw [←finish_ops_eq i hi]
    by_cases low : i<3
    · have atPC : ((finishOps.take i).foldl execInstrBr s).pc=BitVec.ofNat 64 (4096+4*(236549+(869+i))) := by
        interval_cases i <;> simp only [finishOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
      rw [if_pos low]
      exact fetch_gen (869+i) (by omega) _ atPC
    · have high : i=3 := by omega
      subst high
      have atPC : ((finishOps.take 3).foldl execInstrBr s).pc=BitVec.ofNat 64 (4096+4*18) := by
        simp only [finishOps,List.take,List.foldl,execInstrBr,MachineState.setPC,pc] <;> rfl
      rw [if_neg low]
      exact fetch_nonce_setup 18 (by decide) _ atPC
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-! ### Register frames -/

private theorem start_regs (s : MachineState) (pc : s.pc=4152) :
    (startOps.foldl execInstrBr s).pc=BitVec.ofNat 64 (nonceChainPC 0) ∧ ChainPermReady (startOps.foldl execInstrBr s) ∧
    (startOps.foldl execInstrBr s).getReg .x10=s.getReg .x10 ∧
    (startOps.foldl execInstrBr s).getReg .x12=s.getReg .x22 ∧
    (startOps.foldl execInstrBr s).getReg .x7=268443648+s.getReg .x22 := by
  refine ⟨?_,⟨rfl,rfl,rfl⟩,rfl,?_,rfl⟩
  · change s.pc+4+4+4+signExtend21 946128+4+4+4+4=_
    rw [pc]
    rfl
  · exact BitVec.add_zero _

private theorem start_saved (s : MachineState) (h : Saved s) : Saved (startOps.foldl execInstrBr s) :=
  ⟨h.root,h.heap,h.source,h.leaves,h.salts⟩

theorem initial_frame (s : MachineState) (e : CommitEntry s) (k : BitVec 192) :
    NonceChainFrame (chainInitial s k) 0 ∧ Saved (chainInitial s k) := by
  have r := seed_registers s e
  have keep (reg : Reg) : (seedWritten s k).getReg reg = (seedSetup s).getReg reg := writeBits_register ..
  obtain ⟨pc,ready,input,output,limit⟩ := start_regs _ (after_seed s e k)
  rw [keep,r.target] at input
  rw [keep,r.salts] at output limit
  refine ⟨⟨pc,ready,input,output,limit⟩,?_⟩
  have saved' : Saved (seedWritten s k) :=
    ⟨(keep _).trans r.root,(keep _).trans r.heap,(keep _).trans r.source,
      (keep _).trans r.leaves,(keep _).trans r.salts⟩
  exact start_saved _ saved'

theorem advance_saved (s : MachineState) (j : Nat) (y : BitVec 1600) (h : Saved s) : Saved (chainAdvance s j y) := by
  have keep (r : Reg) (ha : r ≠ .x10 := by decide) (hb : r ≠ .x12 := by decide) :=
    chain_advance_register s j y r ha hb
  exact ⟨(keep .x8).trans h.root,(keep .x9).trans h.heap,(keep .x18).trans h.source,
    (keep .x20).trans h.leaves,(keep .x22).trans h.salts⟩

theorem run_frame (j n : Nat) (s : MachineState) (frame : NonceChainFrame s j) (base : Saved s)
    (last : MachineState) (hit : last ∈ support (chainRun j s n)) :
    NonceChainFrame last (j+n) ∧ Saved last := by
  induction n generalizing j s with
  | zero =>
    simp only [chainRun,support_pure,Set.mem_singleton_iff] at hit
    simpa [hit] using And.intro frame base
  | succ n ih =>
    simp only [chainRun,mem_support_bind_iff] at hit
    obtain ⟨y,_,tail⟩ := hit
    simpa only [show j+(n+1)=(j+1)+n by omega] using
      ih (j+1) _ (chain_advance_frame s j y frame) (advance_saved s j y base) tail

theorem finish_regs (s : MachineState) (frame : NonceChainFrame s nonceChainCount) (h : Saved s) :
    ReadyRegs (chainFinish s) := by
  have pc : s.pc=953768 := frame.pc
  obtain ⟨selector,size,primitive⟩ := frame.ready
  refine ⟨⟨?_,h.leaves,h.salts,?_,selector,size,primitive,?_⟩,h.root,h.heap⟩
  · change s.getReg .x18+signExtend12 0=_
    rw [h.source]
    rfl
  · change s.getReg .x13 <<< (12 : Nat) = _
    rw [primitive]
    rfl
  · change s.pc+4+4+signExtend21 1147544+4=_
    rw [pc]
    rfl

def expansion (s : MachineState) (k : BitVec 192) : OracleComp World MachineState :=
  chainRun 0 (chainInitial s k) nonceChainCount

theorem expansion_post (s : MachineState) (e : CommitEntry s) (k : BitVec 192)
    (last : MachineState) (hit : last ∈ support (expansion s k)) :
    last.pc=953768 ∧ ReadyRegs (chainFinish last) := by
  obtain ⟨frame,saved⟩ := initial_frame s e k
  obtain ⟨tail,kept⟩ := run_frame 0 nonceChainCount _ frame saved last hit
  exact ⟨tail.pc,finish_regs last tail kept⟩

theorem after_draw (s : MachineState) (e : CommitEntry s) (k : BitVec 192) (fuel : Nat) :
    execute image (4581052+fuel) (seedWritten s k) true =
      (do let last ← expansion s k
          let result ← execute image fuel (chainFinish last) true
          return result.charge 15257788 nonceChainCount) := by
  have start := start_run _ (after_seed s e k) ((nonceChainSteps nonceChainCount)+(4+fuel))
  have loop := nonce_chain_run (chainInitial s k) 0 nonceChainCount (by decide) (initial_frame s e k).1 (4+fuel)
  rw [show 4581052+fuel = 8+(nonceChainSteps nonceChainCount+(4+fuel)) by unfold nonceChainSteps nonceChainCount;omega,start]
  change (execute image (nonceChainSteps nonceChainCount+(4+fuel)) (chainInitial s k) true >>= _) = _
  rw [show nonceChainSteps nonceChainCount+(4+fuel) =
    nonceChainSteps (0+nonceChainCount)-nonceChainSteps 0+(4+fuel) by simp only [Nat.zero_add,nonceChainSteps,Nat.mul_zero,Nat.zero_div,Nat.add_zero,Nat.sub_zero],loop]
  simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support
  intro last hit
  rw [finish_run _ (expansion_post s e k _ hit).1]
  simp only [bind_assoc,pure_bind]
  apply bind_congr
  intro result
  simp only [Execution.charge]
  have rate : nonceChainCycles (0+nonceChainCount)-nonceChainCycles 0 = 15257776 := by decide
  rw [rate]
  congr 2 <;> omega

end TwoPermutationPrototype.Quad.Commit.Chain
