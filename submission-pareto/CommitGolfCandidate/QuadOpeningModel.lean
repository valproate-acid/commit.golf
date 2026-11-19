import CommitGolfCandidate.QOpeningProofBytes
import CommitGolfCandidate.QuadOpeningLevel

/-! The proof bytes as a function of the trapdoor, and their agreement with the penta transcript
builder whenever the trapdoor slots hold the penta tree nodes and the salts. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling OracleComp
open QOpening (trapdoorSalt)

/-- One 1424-byte record read from the trapdoor. -/
def trapdoorRecord {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor)) (index : Index) : List Byte :=
  saltBytes (trapdoorSalt (s := s) trapdoor index) ++
  (List.range PENTA_LEVELS).flatMap fun k =>
    (List.range 4).flatMap fun j => digestBytes (pentaTrapdoorNode trapdoor k (pentaNeighbour index k j))

def proofFromTrapdoor {s : Submission} (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) : Proof :=
  (positions.sort (· ≤ ·)).flatMap (trapdoorRecord (s := s) trapdoor)

private theorem sorted_value_indices (positions : Positions) :
    (positions.attach.sort (fun i j => i.val ≤ j.val)).map Subtype.val =
      positions.sort (· ≤ ·) := by
  have mapped := Finset.map_sort (r := fun i j : {i // i ∈ positions} => i.val ≤ j.val)
    (r' := fun i j : Index => i ≤ j) (f := Function.Embedding.subtype (· ∈ positions))
    (s := positions.attach) (by intro a _ b _; rfl)
  simpa only [Finset.attach_map_val, Function.Embedding.coe_subtype] using mapped

theorem neighbour_inside (index : Index) (k j : Nat) :
    pentaNeighbour index k j < 5 * pentaCount (k+1) := by
  have count := div_lt_count index.val index.isLt (k+1)
  have slot := (pentaRot index k j).isLt
  unfold pentaNeighbour
  omega

/-- The pure transcript reconstructed from the trapdoor slots agrees with the reference penta
transcript for any node function and leaves stored by commit. -/
theorem proof_from_trapdoor_matches (s : Submission) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (penta : PentaFunction) (leaves : DigestTape) (salts : CompleteSaltTape)
    (node : ∀ level j, level < PENTA_LEVELS → j < 5 * pentaCount (level + 1) →
      pentaTrapdoorNode trapdoor level j = pentaNode penta leaves level j)
    (salt : ∀ index, trapdoorSalt (s := s) trapdoor index = salts index) :
    proofFromTrapdoor (s := s) trapdoor positions =
      (pentaTranscriptBuilder penta positions (fun i => salts i.val) leaves).2 := by
  unfold proofFromTrapdoor pentaTranscriptBuilder
  dsimp only
  rw [← sorted_value_indices positions, List.flatMap_map]
  apply List.flatMap_congr
  intro index _
  unfold trapdoorRecord pentaRecord
  rw [salt]
  congr 1
  apply List.flatMap_congr
  intro k member
  apply List.flatMap_congr
  intro j _
  rw [node k _ (List.mem_range.mp member) (neighbour_inside index.val k j)]

end TwoPermutationPrototype.QuadOpening
