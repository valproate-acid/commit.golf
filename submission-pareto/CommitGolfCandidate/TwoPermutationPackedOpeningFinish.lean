import CommitGolfCandidate.TwoPermutationPackedOpeningCapPreparation
import CommitGolfCandidate.TwoPermutationPackedOpeningCapEmit
import CommitGolfCandidate.TwoPermutationPackedOpeningExit

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open Opening (markBase trapdoorBase proofBase markMachine markParentPrefix mark_addresses parentAddress
  marks_before_trapdoor nat_address_injective)

private theorem observed_store_outside (before after : MachineState) (dest value address : Word)
    (memory : after.mem = (before.setMem dest value).mem) (outside : address ≠ dest) :
    after.getMem address = before.getMem address := by
  have observed : after.getMem address = (before.setMem dest value).getMem address :=
    congrFun memory address
  exact observed.trans (MachineState.getMem_setMem_ne outside)

attribute [local irreducible] markParentPrefix execute

private theorem sweep_frame (state : MachineState) (remaining address : Nat) (bounded : remaining < 256)
    (above : trapdoorBase ≤ address) (fit : address < 2^64)
    (pc : state.pc = if remaining = 0 then 0x1998 else 0x1970)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have parentPC : state.pc = 0x1970 := by simpa using pc
    have ⟨_, _, parent⟩ := mark_addresses state (remaining+1) base count
    have mark := mark_parent_post state parentPC
    have different : BitVec.ofNat 64 address ≠ parentAddress state := by
      rw [parent]
      intro same
      have below := marks_before_trapdoor
      have cellFit : markBase + 8*(remaining+1) < 2^64 := by unfold markBase; omega
      have eq := nat_address_injective fit cellFit same
      omega
    have ⟨nextPC, nextCount⟩ := mark_sweep_pc state remaining (by omega) parentPC count
    have nextBase := mark.2.1.trans base
    have earlier := observed_store_outside _ _ _ _ _ mark.1 different
    change (markMachine (markParentPrefix state 10) remaining).getMem (BitVec.ofNat 64 address) = _
    exact (ih _ (by omega) nextPC nextBase nextCount).trans earlier

theorem cap_preparation_frame (state : MachineState) (address : Nat) (above : trapdoorBase ≤ address)
    (fit : address < 2^64) (base : state.getReg .x26 = BitVec.ofNat 64 markBase) :
    (capPreparation state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  change (markMachine (markSweepEntry state) 255).getMem (BitVec.ofNat 64 address) =
    (markSweepEntry state).getMem (BitVec.ofNat 64 address)
  exact sweep_frame _ 255 address (by decide) above fit rfl base rfl

attribute [local simp] at_root_test

attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem

@[local simp] private theorem abi_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

theorem root_exit (state : MachineState) (pc : state.pc = 0x1a3c)
    (root : state.getReg .x6 = 1#64) (fuel : Nat) (allowCoins : Bool) :
    let result := exitPrefix (advancePrefix state 41 2) 3
    execute openingImage (6 + fuel) state allowCoins = pure ⟨.success, result, 6, 0⟩ ∧
    result.mem = state.mem ∧ result.getReg .x11 = state.getReg .x21 - state.getReg .x20 := by
  let checked := advancePrefix state 41 2
  have ready : checked.pc = 0x1a5c := by rw [advance_root_target state pc, root]; simp
  have memory : checked.mem = state.mem := by
    simp [checked, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
    rfl
  have dest : checked.getReg .x21 = state.getReg .x21 := by
    simp [checked, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  have start : checked.getReg .x20 = state.getReg .x20 := by
    simp [checked, advancePrefix, advanceCode, execInstrBr, signExtend12, root]
  refine ⟨?_, (exit_memory checked).trans memory, ?_⟩
  · rw [show 6 + fuel = 2 + (4 + fuel) by omega, execute_advance_root_test _ pc,
      execute_exit _ ready]
    simp [Execution.charge, checked]
  · rw [exit_register, dest, start]

theorem terminal_length (state : MachineState) (outputLen : Nat)
    (final : state.getReg .x21 = BitVec.ofNat 64 (proofBase+outputLen))
    (start : state.getReg .x20 = BitVec.ofNat 64 proofBase)
    (fits : proofBase + outputLen ≤ MEMORY_BYTES) :
    (state.getReg .x21 - state.getReg .x20).toNat = outputLen := by
  rw [final, start, BitVec.ofNat_sub_ofNat_of_le (w := 64) _ _ (by
    have : proofBase < 2^64 := by decide
    omega) (by omega), Nat.add_sub_cancel_left, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  unfold MEMORY_BYTES at fits
  omega

end TwoPermutationPrototype.PackedOpening
