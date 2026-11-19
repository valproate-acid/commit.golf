import CommitGolfCandidate.Execution

/-! Counted ordinary-loop composition over an abstract transition. Callers must
supply a checked interpreter step and transport readiness after every step;
this lemma supplies no instruction or memory admission facts on its own. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def capCountedRun (step : MachineState → MachineState) : Nat → MachineState → MachineState
  | 0, state => state
  | remaining + 1, state => capCountedRun step remaining (step state)

private theorem charge_twice (result : Execution) (first second : Nat) :
    (result.charge first 0).charge second 0 = result.charge (second + first) 0 := by
  simp only [Execution.charge, Nat.zero_add, Nat.add_assoc]

private theorem charge_zero (result : Execution) :
    result.charge 0 0 = result := by
  cases result
  simp only [Execution.charge, Nat.zero_add]

private theorem fuel_succ (cost remaining fuel : Nat) :
    cost * (remaining + 1) + fuel = cost + (cost * remaining + fuel) := by
  simp only [Nat.mul_add, Nat.mul_one]
  omega

private theorem cost_succ (cost remaining : Nat) :
    cost + cost * remaining = cost * (remaining + 1) := by
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem cap_counted_loop_execute (image : Image) (cost : Nat)
    (step : MachineState → MachineState)
    (finish : Nat → MachineState → MachineState)
    (ready : Nat → MachineState → Prop)
    (zero : ∀ state, finish 0 state = state)
    (successor : ∀ remaining state, finish (remaining + 1) state =
      finish remaining (step state))
    (transport : ∀ remaining state, ready (remaining + 1) state →
      ready remaining (step state))
    (checked : ∀ remaining state, ready (remaining + 1) state →
      ∀ fuel allowCoins, execute image (cost + fuel) state allowCoins =
        (do let result ← execute image fuel (step state) allowCoins
            return result.charge cost 0))
    (remaining : Nat) (state : MachineState) (valid : ready remaining state)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (cost * remaining + fuel) state allowCoins =
      (do let result ← execute image fuel (finish remaining state) allowCoins
          return result.charge (cost * remaining) 0) := by
  induction remaining generalizing state with
  | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, zero, charge_zero, bind_pure]
  | succ remaining ih =>
      rw [fuel_succ, checked remaining state valid,
        ih (step state) (transport remaining state valid)]
      simp only [bind_assoc, pure_bind, charge_twice, cost_succ, successor]

theorem cap_counted_loop_ready
    (step : MachineState → MachineState)
    (finish : Nat → MachineState → MachineState)
    (ready : Nat → MachineState → Prop)
    (zero : ∀ state, finish 0 state = state)
    (successor : ∀ remaining state, finish (remaining + 1) state =
      finish remaining (step state))
    (transport : ∀ remaining state, ready (remaining + 1) state →
      ready remaining (step state))
    (remaining : Nat) (state : MachineState) (valid : ready remaining state) :
    ready 0 (finish remaining state) := by
  induction remaining generalizing state with
  | zero => simpa only [zero] using valid
  | succ remaining ih =>
      rw [successor]
      exact ih (step state) (transport remaining state valid)

theorem cap_counted_run_execute (image : Image) (cost : Nat)
    (step : MachineState → MachineState) (ready : Nat → MachineState → Prop)
    (transport : ∀ remaining state, ready (remaining + 1) state →
      ready remaining (step state))
    (checked : ∀ remaining state, ready (remaining + 1) state →
      ∀ fuel allowCoins, execute image (cost + fuel) state allowCoins =
        (do let result ← execute image fuel (step state) allowCoins
            return result.charge cost 0))
    (remaining : Nat) (state : MachineState) (valid : ready remaining state)
    (fuel : Nat) (allowCoins : Bool) :
    execute image (cost * remaining + fuel) state allowCoins =
      (do let result ← execute image fuel (capCountedRun step remaining state) allowCoins
          return result.charge (cost * remaining) 0) :=
  cap_counted_loop_execute image cost step (capCountedRun step) ready
    (capCountedRun.eq_1 step)
    (fun remaining state => capCountedRun.eq_2 step state remaining) transport checked
    remaining state valid fuel allowCoins

theorem cap_counted_run_ready
    (step : MachineState → MachineState) (ready : Nat → MachineState → Prop)
    (transport : ∀ remaining state, ready (remaining + 1) state →
      ready remaining (step state))
    (remaining : Nat) (state : MachineState) (valid : ready remaining state) :
    ready 0 (capCountedRun step remaining state) :=
  cap_counted_loop_ready step (capCountedRun step) ready
    (capCountedRun.eq_1 step)
    (fun remaining state => capCountedRun.eq_2 step state remaining) transport remaining state valid

end CommitGolfCandidate
