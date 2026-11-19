import CommitGolfCandidate.TwoPermutationPackedLeafAdapter
import CommitGolfCandidate.TwoPermutationPackedRecordLeafPhysical

namespace TwoPermutationPrototype.Packed.RecordLeaf
open CommitGolf TwoPermutationPrototype.Packed.Checker

theorem actual_leaf_block : LeafBlockRefines block := by
  intro oracle input ordinal present state fits cursor framed
  have exactRun := physical_facts oracle input ordinal present state fits cursor framed
  refine ⟨by change 41 ≤ 169; decide,exactRun.run,exactRun.cursor,exactRun.saved,exactRun.frame,?_,?_⟩
  · exact block_trace oracle input ordinal present state fits cursor framed
  · exact block_honest oracle input ordinal present state fits cursor framed

end TwoPermutationPrototype.Packed.RecordLeaf
