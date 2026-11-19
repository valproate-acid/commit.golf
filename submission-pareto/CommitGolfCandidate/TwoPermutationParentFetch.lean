import CommitGolfCandidate.TwoPermutationParent

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def parentPC (slot : Nat) : Word := BitVec.ofNat 64 (5152+12*slot)
def parentCode (offset : Fin 3) : BitVec 32 :=
  if offset.val=0 then 0x73 else if offset.val=1 then 0xfc050513 else 0xfe060613

private def ValidBlock (block : Nat) : Prop := ∀ i : Fin 16, ∀ k : Fin 3, 16*block+i.val < 255 →
  Manifest.commitWords[264+3*(16*block+i.val)+k.val]? = some (parentCode k)
private theorem fetched_block0 : ValidBlock 0 := by unfold ValidBlock; decide +kernel
private theorem fetched_block1 : ValidBlock 1 := by unfold ValidBlock; decide +kernel
private theorem fetched_block2 : ValidBlock 2 := by unfold ValidBlock; decide +kernel
private theorem fetched_block3 : ValidBlock 3 := by unfold ValidBlock; decide +kernel
private theorem fetched_block4 : ValidBlock 4 := by unfold ValidBlock; decide +kernel
private theorem fetched_block5 : ValidBlock 5 := by unfold ValidBlock; decide +kernel
private theorem fetched_block6 : ValidBlock 6 := by unfold ValidBlock; decide +kernel
private theorem fetched_block7 : ValidBlock 7 := by unfold ValidBlock; decide +kernel
private theorem fetched_block8 : ValidBlock 8 := by unfold ValidBlock; decide +kernel
private theorem fetched_block9 : ValidBlock 9 := by unfold ValidBlock; decide +kernel
private theorem fetched_block10 : ValidBlock 10 := by unfold ValidBlock; decide +kernel
private theorem fetched_block11 : ValidBlock 11 := by unfold ValidBlock; decide +kernel
private theorem fetched_block12 : ValidBlock 12 := by unfold ValidBlock; decide +kernel
private theorem fetched_block13 : ValidBlock 13 := by unfold ValidBlock; decide +kernel
private theorem fetched_block14 : ValidBlock 14 := by unfold ValidBlock; decide +kernel
private theorem fetched_block15 : ValidBlock 15 := by unfold ValidBlock; decide +kernel

private theorem slots_present (i : Nat) (inside : i < 255) (k : Fin 3) :
    Manifest.commitWords[264+3*i+k.val]? = some (parentCode k) := by
  have block_bound : i/16 < 16 := by omega
  have block : ValidBlock (i/16) := by
    generalize i/16 = b at block_bound ⊢
    interval_cases b
    · exact fetched_block0
    · exact fetched_block1
    · exact fetched_block2
    · exact fetched_block3
    · exact fetched_block4
    · exact fetched_block5
    · exact fetched_block6
    · exact fetched_block7
    · exact fetched_block8
    · exact fetched_block9
    · exact fetched_block10
    · exact fetched_block11
    · exact fetched_block12
    · exact fetched_block13
    · exact fetched_block14
    · exact fetched_block15

  have equal : 16*(i/16)+(i%16)=i := by omega
  simpa only [equal] using block ⟨i%16,by omega⟩ k (by simpa only [equal] using inside)

private theorem fetch_at (s : MachineState) (slot : Nat) (bound : slot < 255) (k : Fin 3)
    (pc : s.pc = parentPC slot+BitVec.ofNat 64 (4*k.val)) :
    fetch commitImage s=decodeInstruction (parentCode k) := by
  have addr : s.pc.toNat=5152+12*slot+4*k.val := by
    rw [pc,parentPC,←BitVec.ofNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt];have := k.isLt;omega
  rw [fetch,addr,if_pos (by omega)]
  change (match Manifest.commitWords[(5152+12*slot+4*k.val-4096)/4]? with
    | some w => _ | none => _) = _
  rw [show (5152+12*slot+4*k.val-4096)/4=264+3*slot+k.val by omega,slots_present slot bound k]

theorem parent_fetched (slot : Nat) (bound : slot<255) : ParentFetched (parentPC slot) := by
  intro s
  refine ⟨fun pc => ?_,fun pc => ?_,fun pc => ?_⟩
  · exact fetch_at s slot bound 0 (by simpa using pc)
  · exact fetch_at s slot bound 1 pc
  · exact fetch_at s slot bound 2 pc

theorem parent_pc_next (i : Nat) : parentPC i+12=parentPC (i+1) := by
  change parentPC i+BitVec.ofNat 64 12=_
  unfold parentPC
  rw [←BitVec.ofNat_add]; congr 1 <;> omega

end TwoPermutationPrototype.RV64
