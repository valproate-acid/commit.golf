import CommitGolfCandidate.TwoPermutationLeafInvariant

/-! First sixteen instructions of the production commitment. A single private
draw initializes all 128-bit nonces at their final trapdoor offsets. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local irreducible] execute writeBits

def initialInstructions : List Instr :=
  [.ADDI .x8 .x11 0,.ADDI .x9 .x12 0,.ADDI .x18 .x10 4056,.LUI .x19 131072,
   .ADD .x20 .x9 .x19,.ADD .x21 .x20 .x19,.LUI .x22 327680,.ADD .x22 .x9 .x22,
   .ADDI .x5 .x0 2,.ADDI .x10 .x22 0,.LUI .x11 65536]

def readyInstructions : List Instr :=
  [.ADDI .x5 .x0 0,.ADDI .x11 .x0 200,.ADDI .x13 .x0 1,.ADDI .x10 .x18 0]

def initialPrefix (s : MachineState) (i : Nat) := (initialInstructions.take i).foldl execInstrBr s
def readyPrefix (s : MachineState) (i : Nat) := (readyInstructions.take i).foldl execInstrBr s

theorem initial_run (s : MachineState) (pc : s.pc=4096) (fuel : Nat) :
    execute commitImage (11+fuel) s true =
      (do let result ← execute commitImage fuel (initialPrefix s 11) true
          return result.charge 11 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := initialPrefix s)
  intro i inside
  refine ⟨.base ((initialInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · interval_cases i <;> simp only [initialPrefix,initialInstructions,List.take,List.foldl,execInstrBr,
      MachineState.setPC,fetch,pc] <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem ready_run (s : MachineState) (pc : s.pc=4144) (fuel : Nat) :
    execute commitImage (4+fuel) s true =
      (do let result ← execute commitImage fuel (readyPrefix s 4) true
          return result.charge 4 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := readyPrefix s)
  intro i inside
  refine ⟨.base ((readyInstructions[i]?).getD .EBREAK),?_,?_,?_⟩
  · interval_cases i <;> simp only [readyPrefix,readyInstructions,List.take,List.foldl,execInstrBr,
      MachineState.setPC,fetch,pc] <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

structure CommitEntry (s : MachineState) : Prop where
  pc : s.pc = 4096
  message : s.getReg .x10 = 4096
  commitment : s.getReg .x11 = 4294971392
  heap : s.getReg .x12 = 4294971424

theorem setup_pc (s : MachineState) (pc : s.pc=4096) : (initialPrefix s 11).pc=4140 := by
  change s.pc+4+4+4+4+4+4+4+4+4+4+4 = _
  rw [pc];rfl

structure SetupRegisters (s : MachineState) : Prop where
  out : s.getReg .x8 = 4294971392
  heap : s.getReg .x9 = 4294971424
  source : s.getReg .x18 = wordAddress (leafStart 0)
  stride : s.getReg .x19 = 536870912
  leaves : s.getReg .x20 = wordAddress (leafDest 0)
  stop : s.getReg .x21 = wordAddress (leafDest (2^24))
  salts : s.getReg .x22 = wordAddress (leafSalt 0)
  target : s.getReg .x10 = wordAddress (leafSalt 0)
  size : s.getReg .x11 = 268435456
  selector : s.getReg .x5 = 2

theorem setup_registers (s : MachineState) (entry : CommitEntry s) : SetupRegisters (initialPrefix s 11) := by
  constructor <;>
    dsimp [initialPrefix,initialInstructions,execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.getReg]
  all_goals try simp only [show s.regs .x10=4096 from entry.message,
    show s.regs .x11=4294971392 from entry.commitment,show s.regs .x12=4294971424 from entry.heap]
  all_goals rfl

def readyState (s : MachineState) {bits : Nat} (coins : BitVec bits) :=
  readyPrefix (writeBits (initialPrefix s 11) (wordAddress (leafSalt 0)) coins) 4

theorem written_pc {bits : Nat} (s : MachineState) (dst : Word) (coins : BitVec bits) :
    (writeBits s dst coins).pc = s.pc + 4 := by simp only [writeBits,MachineState.setPC]

theorem ready_regs (s : MachineState) (pc : s.pc = 4144) :
    (readyPrefix s 4).getReg .x10 = s.getReg .x18 ∧ (readyPrefix s 4).getReg .x5 = 0 ∧
    (readyPrefix s 4).getReg .x11=200 ∧ (readyPrefix s 4).getReg .x13=1 ∧ (readyPrefix s 4).pc=4160 ∧
    ∀ reg ∈ [Reg.x20,.x21,.x22,.x8,.x9,.x19], (readyPrefix s 4).getReg reg = s.getReg reg := by
  refine ⟨?_,rfl,rfl,rfl,?_,?_⟩
  · change s.getReg .x18 + 0 = _;simp
  · change s.pc+4+4+4+4=_;rw [pc];rfl
  · intro reg member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem post_random_regs (s : MachineState) (entry : CommitEntry s) {bits : Nat} (coins : BitVec bits) :
    GroupRegs (readyState s coins) 0 0 ∧ (readyState s coins).getReg .x21=wordAddress (leafDest (2^24)) ∧
    (readyState s coins).getReg .x8=4294971392 ∧ (readyState s coins).getReg .x9=4294971424 ∧
    (readyState s coins).getReg .x19=536870912 := by
  have regs := setup_registers s entry
  let after := writeBits (initialPrefix s 11) (wordAddress (leafSalt 0)) coins
  have saved (reg : Reg) : after.getReg reg = (initialPrefix s 11).getReg reg := CommitGolfCandidate.writeBits_register ..
  have pc : after.pc=4144 := by rw [show after.pc = _ from written_pc _ _ _,setup_pc s entry.pc];rfl
  obtain ⟨src,selector,size,primitive,here,keep⟩ := ready_regs after pc
  refine ⟨⟨src.trans ((saved .x18).trans regs.source),
    (keep .x20 (by simp)).trans ((saved .x20).trans regs.leaves),
    (keep .x22 (by simp)).trans ((saved .x22).trans regs.salts),selector,size,primitive,here⟩,
    (keep .x21 (by simp)).trans ((saved .x21).trans regs.stop),
    (keep .x8 (by simp)).trans ((saved .x8).trans regs.out),
    (keep .x9 (by simp)).trans ((saved .x9).trans regs.heap),
    (keep .x19 (by simp)).trans ((saved .x19).trans regs.stride)⟩

theorem draw_run (s : MachineState) (pc : s.pc=4140) (r : SetupRegisters s) (fuel : Nat) :
    execute commitImage (1+fuel) s true =
      (do let answer ← liftM ($ᵗ BitVec (8*(s.getReg .x11).toNat) : ProbComp (BitVec (8*(s.getReg .x11).toNat)))
          let result ← execute commitImage fuel (writeBits s (wordAddress (leafSalt 0)) answer) true
          return result.charge 33554433 0) := by
  have fetched : fetch commitImage s=some (.base .ECALL) := by rw [fetch,pc];rfl
  have valid : randomArgumentsValid s=true := by rw [randomArgumentsValid,r.target,r.size];decide
  rw [Nat.add_comm 1 fuel,execute,fetched]
  have cost : 1+((s.getReg .x11).toNat+7)/8=33554433 := by rw [r.size];rfl
  simp only [r.selector,valid,r.target,cost]
  rfl

theorem execute_setup (s : MachineState) (entry : CommitEntry s) (fuel : Nat) :
    execute commitImage (16+fuel) s true =
      (do let answer ← liftM ($ᵗ BitVec (8*((initialPrefix s 11).getReg .x11).toNat) : ProbComp (BitVec (8*((initialPrefix s 11).getReg .x11).toNat)))
          let result ← execute commitImage fuel (readyState s answer) true
          return result.charge 33554448 0) := by
  rw [show 16+fuel=11+(1+(4+fuel)) by omega,initial_run s entry.pc,
    draw_run _ (setup_pc s entry.pc) (setup_registers s entry)]
  simp only [bind_assoc]
  apply bind_congr_of_forall_mem_support
  intro answer _
  have pc : (writeBits (initialPrefix s 11) (wordAddress (leafSalt 0)) answer).pc=4144 := by
    rw [written_pc,setup_pc s entry.pc];rfl
  rw [ready_run _ pc]
  simp [Execution.charge,←Nat.add_assoc,readyState]

end TwoPermutationPrototype.RV64
