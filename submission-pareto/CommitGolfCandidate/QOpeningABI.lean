import CommitGolfCandidate.QOpeningCapSubtree
import CommitGolfCandidate.QOpeningRecordPrefix

namespace TwoPermutationPrototype.QOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate TwoPermutationPrototype.Sampling
  RiscvZkvm.Rv64 OracleComp

structure OpeningABI (s : Submission) extends OpeningLayout s where
  image : s.image .opening = openingImage
  capacity : proofCapacity ≤ s.sizes.proof
  fuel : 512 * LENGTH + 65536 ≤ s.steps .opening

def openingNodes (positions : Positions) : List Nat :=
  if positions.card = 0 then [] else capFrontierNodes (groupsBefore positions positions.card) 1 8

def openingLength (positions : Positions) : Nat :=
  528 * positions.card + 32 * (openingNodes positions).length

def openingMachineCycles (positions : Positions) : Nat :=
  if positions.card = 0 then 7
  else 13 + 256 * positions.card + 2552 +
    capSubtreeCycles (groupsBefore positions positions.card) 1 8 + 6

theorem opening_nodes_bound (positions : Positions) : (openingNodes positions).length ≤ 128 := by
  unfold openingNodes
  split
  · simp
  · rw [cap_frontier_length]
    exact production_boundary_bound _

theorem opening_length_bound (positions : Positions) : openingLength positions ≤ proofCapacity := by
  have cardinal : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  have small := opening_nodes_bound positions
  unfold openingLength proofCapacity
  omega

private theorem observed_store_outside (before after : MachineState) (dest value address : Word)
    (memory : after.mem = (before.setMem dest value).mem) (outside : address ≠ dest) :
    after.getMem address = before.getMem address := by
  have observed : after.getMem address = (before.setMem dest value).getMem address :=
    congrFun memory address
  exact observed.trans (MachineState.getMem_setMem_ne outside)

attribute [local irreducible] markParentPrefix execute

private theorem sweep_frame (state : MachineState) (remaining address : Nat) (bounded : remaining < 256)
    (above : trapdoorBase ≤ address) (fit : address < 2^64)
    (pc : state.pc = if remaining = 0 then 0x10dc else 0x10b4)
    (base : state.getReg .x26 = BitVec.ofNat 64 markBase)
    (count : state.getReg .x6 = BitVec.ofNat 64 remaining) :
    (markMachine state remaining).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction remaining generalizing state with
  | zero => rfl
  | succ remaining ih =>
    have parentPC : state.pc = 0x10b4 := by simpa using pc
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

attribute [local simp] getReg_setReg getReg_setMem

@[local simp] private theorem abi_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

end TwoPermutationPrototype.QOpening
