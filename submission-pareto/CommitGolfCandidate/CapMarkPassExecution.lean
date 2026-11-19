import CommitGolfCandidate.CapMarkStart

/-! Whole occupancy pass, including its two entry instructions. The caller must
provide actual header/body fetches and initialized leaf occupancy. All memory
accesses remain discharged by the bounded descending-loop theorem. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
attribute [local irreducible] capMarkPrefix capMarkLoopRun capCountedRun
attribute [local irreducible] capMarkHeaderState capMarkHeaderSet

def capMarkMachinePass (marks leavesReg : Reg) (state : MachineState)
    (leaves : Nat) : MachineState :=
  capMarkLoopRun marks (leaves - 1) (capMarkHeaderState leavesReg state)

private theorem charge_twice (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

theorem cap_mark_pass_execute (image : Image) (marks leavesReg : Reg)
    (entry : Word)
    (headerFetched : CapMarkHeaderFetched image leavesReg entry)
    (bodyFetched : CapMarkFetched image marks (entry + 8))
    (selected : CapMarksRegister marks) (leaves : Nat) (marked : Nat → Bool)
    (positive : 0 < leaves) (bounded : leaves ≤ 256)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (state : MachineState) (pc : state.pc = entry)
    (base : state.getReg marks = 28672)
    (count : state.getReg leavesReg = BitVec.ofNat 64 leaves)
    (ready : CapMarksReady state leaves (leaves - 1) marked)
    (fuel : Nat) (allowCoins : Bool) :
    execute image ((2 + 10 * (leaves - 1)) + fuel) state allowCoins =
      (do let result ← execute image fuel
            (capMarkMachinePass marks leavesReg state leaves) allowCoins
          return result.charge (2 + 10 * (leaves - 1)) 0) := by
  have internal : leaves - 1 < leaves := Nat.sub_lt positive (by decide)
  have initialized := cap_mark_header_ready marks leavesReg state entry leaves marked
    selected base count pc positive bounded ready
  rw [Nat.add_assoc,
    cap_mark_header_execute image leavesReg entry headerFetched state pc]
  rw [cap_mark_loop_execute image marks (entry + 8) bodyFetched selected leaves
    (leaves - 1) marked bounded internal equations
    (capMarkHeaderState leavesReg state) initialized]
  simp only [bind_assoc, pure_bind, charge_twice, capMarkMachinePass]

theorem cap_mark_pass_finished (marks leavesReg : Reg) (state : MachineState)
    (entry : Word) (leaves : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (positive : 0 < leaves) (bounded : leaves ≤ 256)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (pc : state.pc = entry) (base : state.getReg marks = 28672)
    (count : state.getReg leavesReg = BitVec.ofNat 64 leaves)
    (ready : CapMarksReady state leaves (leaves - 1) marked) :
    CapMarkLoopReady marks (entry + 8)
      (capMarkMachinePass marks leavesReg state leaves) leaves 0 marked :=
  cap_mark_loop_finished marks (entry + 8) leaves (leaves - 1) marked selected bounded
    (Nat.sub_lt positive (by decide)) equations (capMarkHeaderState leavesReg state)
    (cap_mark_header_ready marks leavesReg state entry leaves marked
      selected base count pc positive bounded ready)

theorem cap_mark_pass_register (marks leavesReg : Reg) (state : MachineState)
    (leaves : Nat) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x7 ∧ reg ≠ .x20 ∧ reg ≠ .x23 ∧ reg ≠ .x30) :
    (capMarkMachinePass marks leavesReg state leaves).getReg reg = state.getReg reg :=
  (cap_mark_loop_register marks (leaves - 1) (capMarkHeaderState leavesReg state)
    reg outside).trans (cap_mark_header_register leavesReg state reg outside.2.2.1)

theorem cap_mark_pass_memory (marks leavesReg : Reg) (state : MachineState)
    (entry : Word) (leaves : Nat) (marked : Nat → Bool)
    (selected : CapMarksRegister marks) (positive : 0 < leaves) (bounded : leaves ≤ 256)
    (equations : ∀ node, 0 < node → node < leaves →
      marked node = (marked (2 * node) || marked (2 * node + 1)))
    (pc : state.pc = entry) (base : state.getReg marks = 28672)
    (count : state.getReg leavesReg = BitVec.ofNat 64 leaves)
    (ready : CapMarksReady state leaves (leaves - 1) marked) :
    (capMarkMachinePass marks leavesReg state leaves).mem =
      (capMarkPass state (leaves - 1)).mem :=
  (cap_mark_loop_memory marks (entry + 8) leaves (leaves - 1) marked selected bounded
    (Nat.sub_lt positive (by decide)) equations (capMarkHeaderState leavesReg state)
    (cap_mark_header_ready marks leavesReg state entry leaves marked
      selected base count pc positive bounded ready)).trans
    (cap_mark_pass_memory_congr (capMarkHeaderState leavesReg state) state
      (leaves - 1) (cap_mark_header_memory leavesReg state))

end CommitGolfCandidate
