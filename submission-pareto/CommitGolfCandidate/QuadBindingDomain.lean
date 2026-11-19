import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.TwoPermutationPinnedRecorded
import CommitGolfCandidate.S3PermSingleCall
import CommitGolfCandidate.TwoPermutationProjectionEvent

/-! Penta binding includes every public permutation query, in both directions.
Raw first-leaf inputs may belong to D5; there is no domain-separation premise. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2100

/-- D5 is the 320-zero-bit prefix domain, little-endian. -/
def pentaDomain : Set Block := {b | b.extractLsb' 0 320 = 0}

def pentaEncode (x : BitVec 1280) : Block := x ++ (0#320)

theorem penta_encode_injective : Function.Injective pentaEncode := by
  intro x y eq
  have hit := congrArg (fun b : Block => b.extractLsb' 320 1280) eq
  change (x ++ (0#320)).extractLsb' 320 1280 = (y ++ (0#320)).extractLsb' 320 1280 at hit
  exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)

def pentaSingleCall : SingleCall Block (BitVec 1280) (BitVec 256) :=
  ⟨pentaEncode, penta_encode_injective, fun b => b.extractLsb' 0 256⟩

theorem penta_input_encoded (c : Fin 5 → BitVec 256) :
    pentaInput c = pentaEncode ((((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) := rfl

theorem penta_input_domain (c : Fin 5 → BitVec 256) : pentaInput c ∈ pentaDomain := by
  change (pentaInput c).extractLsb' 0 320 = 0
  exact BitVec.extractLsb'_append_eq_right

/-- Distinct D5 inputs with equal low-256-bit outputs, including calls originating
as raw first-leaf queries rather than node queries. -/
def PentaWitness (rows : List PublicRow) : Prop :=
  ∃ (x y : BitVec 1280) (a b : Block),
    PublicRow.permutation (pentaEncode x) a ∈ rows ∧
    PublicRow.permutation (pentaEncode y) b ∈ rows ∧
    x ≠ y ∧ a.extractLsb' 0 256 = b.extractLsb' 0 256

theorem PentaWitness.mono {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later) (hit : PentaWitness earlier) : PentaWitness later := by
  obtain ⟨x,y,a,b,ha,hb,ne,eq⟩ := hit
  exact ⟨x,y,a,b,contained _ ha,contained _ hb,ne,eq⟩

theorem penta_witness_bad (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (hit : PentaWitness rows) :
    ¬ pentaSingleCall.badSpec.Good t := by
  obtain ⟨x,y,a,b,ha,hb,ne,eq⟩ := hit
  obtain ⟨e,he,hin,hout⟩ := stored _ _ ha
  obtain ⟨f,hf,fin,fout⟩ := stored _ _ hb
  exact (pentaSingleCall.not_good_iff t).2 (pentaSingleCall.collision_imp_bad ne
    ⟨e,he,hin,congrArg (fun r : Block => r.extractLsb' 0 256) hout⟩
    ⟨f,hf,fin,(congrArg (fun r : Block => r.extractLsb' 0 256) fout).trans eq.symm⟩)

end TwoPermutationPrototype.Sampling
