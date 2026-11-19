import CommitGolfCandidate.QuadCheckImage

/-! Fetch interfaces for all unchanged codecs. The image has the original PCs. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.Packed.Checker (FieldSite ProjectSite)
set_option maxRecDepth 8192

abbrev packedImage : Image := quadCheckImage

theorem field_fetch_load (site : FieldSite) (j : Nat) (bounded : j<site.count) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(site.start+2*j))) :
    fetch packedImage state=some (.base (FieldSite.load j)) := by
  refine cap_image_fetch packedImage state _ _
    (by cases site <;> simp [FieldSite.start,FieldSite.count] at bounded ⊢ <;> omega) pc ?_
  cases site <;> simp only [FieldSite.count] at bounded <;> interval_cases j <;> rfl

theorem field_fetch_store (site : FieldSite) (j : Nat) (bounded : j<site.count) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(site.start+2*j+1))) :
    fetch packedImage state=some (.base (site.store j)) := by
  refine cap_image_fetch packedImage state _ _
    (by cases site <;> simp [FieldSite.start,FieldSite.count] at bounded ⊢ <;> omega) pc ?_
  cases site <;> simp only [FieldSite.count] at bounded <;> interval_cases j <;> rfl

theorem project_fetch (site : ProjectSite) (s : MachineState)
    (here : s.pc=BitVec.ofNat 64 (4096+4*site.start)) :
    fetch packedImage s=some (.base .ECALL) := by
  refine cap_image_fetch _ _ _ _ (by cases site <;> decide) here ?_
  cases site <;> rfl

theorem project_fetch_mask (site : ProjectSite) (s : MachineState)
    (here : s.pc=BitVec.ofNat 64 (4096+4*(site.start+1))) :
    fetch packedImage s=some (.base (.SH site.dest .x0 30)) := by
  refine cap_image_fetch _ _ _ _ (by cases site <;> decide) here ?_
  cases site <;> rfl

end TwoPermutationPrototype.Quad.Checker
