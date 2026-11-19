import CommitGolfCandidate.TwoPermutationPackedLowerRecursion
import CommitGolfCandidate.TwoPermutationPackedLevelSpec

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

def adaptLowerStep (step : Oracle → MachineState → Nat → Nat → Nat → RecordBlock) (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat)
    (state : MachineState) : RecordBlock :=
  step oracle state (Opening.lowerNode index level) (lowerProofByte ordinal level) (16-level)

theorem lower_step_from_level (step : Oracle → MachineState → Nat → Nat → Nat → RecordBlock)
    (facts : ∀ oracle state node proof left, LevelReady state node proof left →
      LevelFacts oracle state node proof left (step oracle state node proof left)) :
    LowerStepRefines (adaptLowerStep step) := by
  intro oracle ordinal index level state inside room cursor
  let node := Opening.lowerNode index level
  let proof := lowerProofByte ordinal level
  let left := 16-level
  have widthEq : width (decide (left=16)) = lowerSiblingWidth level := by
    rw [lower_width_from_counter]
    change width (decide (16-level=16)) = _
    by_cases first : 16-level=16 <;> simp [width,first]
  have wireEq : wire state proof (decide (left=16)) = lowerWireSibling state ordinal level := by
    rw [lower_wire_sibling_from_cursor]
    change wire state (lowerProofByte ordinal level) (decide (16-level=16)) = _
    by_cases first : 16-level=16 <;> simp [wire,first]
  have bounds := lower_proof_geometry ordinal level inside room
  have nodeBound : node < 2^64 := by
    have fit := Opening.lower_node_bound index level
    change Opening.lowerNode index level < 33554432 at fit
    exact fit.trans (by decide)
  have ready : LevelReady state node proof left :=
    ⟨cursor.pc.trans (ite_eq_right (by omega)),cursor.node,cursor.proof,cursor.counter,
      cursor.digest,cursor.pair,cursor.selector,cursor.syscallBytes,cursor.syscallSelector,
      nodeBound,by unfold left; omega,by unfold left; omega,bounds.1,bounds.2.1,
      by rw [widthEq]; exact bounds.2.2⟩
  have realStep := facts oracle state node proof left ready
  change LowerStepFacts oracle ordinal index level state (step oracle state node proof left)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,realStep.syscallBytes,realStep.syscallSelector⟩,
    realStep.cost,realStep.saved,realStep.frame,?_,?_,realStep.run⟩
  · simpa only [show left=1 ↔ level+1=16 by unfold left; omega] using realStep.pc
  · rw [Opening.lower_node_next]
    exact realStep.nodeReg
  · rw [lower_proof_byte_next,← widthEq]
    exact realStep.proofReg
  · rw [show 16-(level+1)=left-1 by unfold left; omega]
    exact realStep.counter
  · exact (realStep.saved .x23 (by decide)).trans cursor.digest
  · exact (realStep.saved .x24 (by decide)).trans cursor.pair
  · exact (realStep.saved .x5 (by decide)).trans cursor.selector
  · simpa only [levelPair,wireEq] using realStep.digest
  · simpa only [levelPair,wireEq] using realStep.row

end TwoPermutationPrototype.Packed.Checker
