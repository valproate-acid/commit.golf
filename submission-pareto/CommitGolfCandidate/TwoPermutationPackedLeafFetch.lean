import CommitGolfCandidate.TwoPermutationPackedParentImage

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
attribute [local irreducible] ArtifactEncoding.decode

def packed_wideLeafIndex (slot : Nat) : Nat := 18+11*slot+slot/64+slot/128
def packed_wideLeafPC (slot offset : Nat) : Word := BitVec.ofNat 64 (4096+4*(packed_wideLeafIndex slot+offset))

def packed_wideFirstOps (_slot : Nat) : List Instr :=
  [.ADDI .x12 .x10 4064]

def packed_wideSecondOps (slot : Nat) : List Instr :=
  [.ADDI .x10 .x10 56, .SD .x10 .x10 0,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot%128))), .SD .x10 .x31 8,
   .LD .x31 .x22 (BitVec.ofNat 12 (16*(slot%128)+8)), .SD .x10 .x31 16,
   .ADDI .x12 .x20 (BitVec.ofNat 12 (32*(slot%64)))]

def packed_wideLeafOp (slot offset : Nat) : Instr :=
  (((packed_wideFirstOps slot) ++ [.ECALL] ++ packed_wideSecondOps slot ++ [.ECALL,.ADDI .x10 .x10 200])[offset]?).getD .EBREAK

private def packed_wideCodeWord (index : Nat) : BitVec 32 :=
  if inCode : index < 233170 then CommitGolfCandidate.PackedCommitArtifact.commitCode.get 32 ⟨index,inCode⟩ else 0

private def LeafTileDecodes (tile : Nat) : Prop :=
  ∀ slot : Fin 64, ∀ offset : Fin 11,
    Manifest.decodeBase (packed_wideCodeWord (packed_wideLeafIndex (64*tile+slot.val)+offset.val)) =
    some (packed_wideLeafOp (64*tile+slot.val) offset.val)

private theorem tile0 : LeafTileDecodes 0 := by unfold LeafTileDecodes; decide +kernel
private theorem tile1 : LeafTileDecodes 1 := by unfold LeafTileDecodes; decide +kernel
private theorem tile2 : LeafTileDecodes 2 := by unfold LeafTileDecodes; decide +kernel
private theorem tile3 : LeafTileDecodes 3 := by unfold LeafTileDecodes; decide +kernel
private theorem tile4 : LeafTileDecodes 4 := by unfold LeafTileDecodes; decide +kernel
private theorem tile5 : LeafTileDecodes 5 := by unfold LeafTileDecodes; decide +kernel
private theorem tile6 : LeafTileDecodes 6 := by unfold LeafTileDecodes; decide +kernel
private theorem tile7 : LeafTileDecodes 7 := by unfold LeafTileDecodes; decide +kernel
private theorem tile8 : LeafTileDecodes 8 := by unfold LeafTileDecodes; decide +kernel
private theorem tile9 : LeafTileDecodes 9 := by unfold LeafTileDecodes; decide +kernel
private theorem tile10 : LeafTileDecodes 10 := by unfold LeafTileDecodes; decide +kernel
private theorem tile11 : LeafTileDecodes 11 := by unfold LeafTileDecodes; decide +kernel
private theorem tile12 : LeafTileDecodes 12 := by unfold LeafTileDecodes; decide +kernel
private theorem tile13 : LeafTileDecodes 13 := by unfold LeafTileDecodes; decide +kernel
private theorem tile14 : LeafTileDecodes 14 := by unfold LeafTileDecodes; decide +kernel
private theorem tile15 : LeafTileDecodes 15 := by unfold LeafTileDecodes; decide +kernel
private theorem tile16 : LeafTileDecodes 16 := by unfold LeafTileDecodes; decide +kernel
private theorem tile17 : LeafTileDecodes 17 := by unfold LeafTileDecodes; decide +kernel
private theorem tile18 : LeafTileDecodes 18 := by unfold LeafTileDecodes; decide +kernel
private theorem tile19 : LeafTileDecodes 19 := by unfold LeafTileDecodes; decide +kernel
private theorem tile20 : LeafTileDecodes 20 := by unfold LeafTileDecodes; decide +kernel
private theorem tile21 : LeafTileDecodes 21 := by unfold LeafTileDecodes; decide +kernel
private theorem tile22 : LeafTileDecodes 22 := by unfold LeafTileDecodes; decide +kernel
private theorem tile23 : LeafTileDecodes 23 := by unfold LeafTileDecodes; decide +kernel
private theorem tile24 : LeafTileDecodes 24 := by unfold LeafTileDecodes; decide +kernel
private theorem tile25 : LeafTileDecodes 25 := by unfold LeafTileDecodes; decide +kernel
private theorem tile26 : LeafTileDecodes 26 := by unfold LeafTileDecodes; decide +kernel
private theorem tile27 : LeafTileDecodes 27 := by unfold LeafTileDecodes; decide +kernel
private theorem tile28 : LeafTileDecodes 28 := by unfold LeafTileDecodes; decide +kernel
private theorem tile29 : LeafTileDecodes 29 := by unfold LeafTileDecodes; decide +kernel
private theorem tile30 : LeafTileDecodes 30 := by unfold LeafTileDecodes; decide +kernel
private theorem tile31 : LeafTileDecodes 31 := by unfold LeafTileDecodes; decide +kernel
private theorem tile32 : LeafTileDecodes 32 := by unfold LeafTileDecodes; decide +kernel
private theorem tile33 : LeafTileDecodes 33 := by unfold LeafTileDecodes; decide +kernel
private theorem tile34 : LeafTileDecodes 34 := by unfold LeafTileDecodes; decide +kernel
private theorem tile35 : LeafTileDecodes 35 := by unfold LeafTileDecodes; decide +kernel
private theorem tile36 : LeafTileDecodes 36 := by unfold LeafTileDecodes; decide +kernel
private theorem tile37 : LeafTileDecodes 37 := by unfold LeafTileDecodes; decide +kernel
private theorem tile38 : LeafTileDecodes 38 := by unfold LeafTileDecodes; decide +kernel
private theorem tile39 : LeafTileDecodes 39 := by unfold LeafTileDecodes; decide +kernel
private theorem tile40 : LeafTileDecodes 40 := by unfold LeafTileDecodes; decide +kernel
private theorem tile41 : LeafTileDecodes 41 := by unfold LeafTileDecodes; decide +kernel
private theorem tile42 : LeafTileDecodes 42 := by unfold LeafTileDecodes; decide +kernel
private theorem tile43 : LeafTileDecodes 43 := by unfold LeafTileDecodes; decide +kernel
private theorem tile44 : LeafTileDecodes 44 := by unfold LeafTileDecodes; decide +kernel
private theorem tile45 : LeafTileDecodes 45 := by unfold LeafTileDecodes; decide +kernel
private theorem tile46 : LeafTileDecodes 46 := by unfold LeafTileDecodes; decide +kernel
private theorem tile47 : LeafTileDecodes 47 := by unfold LeafTileDecodes; decide +kernel
private theorem tile48 : LeafTileDecodes 48 := by unfold LeafTileDecodes; decide +kernel
private theorem tile49 : LeafTileDecodes 49 := by unfold LeafTileDecodes; decide +kernel
private theorem tile50 : LeafTileDecodes 50 := by unfold LeafTileDecodes; decide +kernel
private theorem tile51 : LeafTileDecodes 51 := by unfold LeafTileDecodes; decide +kernel
private theorem tile52 : LeafTileDecodes 52 := by unfold LeafTileDecodes; decide +kernel
private theorem tile53 : LeafTileDecodes 53 := by unfold LeafTileDecodes; decide +kernel
private theorem tile54 : LeafTileDecodes 54 := by unfold LeafTileDecodes; decide +kernel
private theorem tile55 : LeafTileDecodes 55 := by unfold LeafTileDecodes; decide +kernel
private theorem tile56 : LeafTileDecodes 56 := by unfold LeafTileDecodes; decide +kernel
private theorem tile57 : LeafTileDecodes 57 := by unfold LeafTileDecodes; decide +kernel
private theorem tile58 : LeafTileDecodes 58 := by unfold LeafTileDecodes; decide +kernel
private theorem tile59 : LeafTileDecodes 59 := by unfold LeafTileDecodes; decide +kernel
private theorem tile60 : LeafTileDecodes 60 := by unfold LeafTileDecodes; decide +kernel
private theorem tile61 : LeafTileDecodes 61 := by unfold LeafTileDecodes; decide +kernel
private theorem tile62 : LeafTileDecodes 62 := by unfold LeafTileDecodes; decide +kernel
private theorem tile63 : LeafTileDecodes 63 := by unfold LeafTileDecodes; decide +kernel

theorem packed_wide_leaf_decode (slot : Fin 4096) (offset : Fin 11) :
    Manifest.decodeBase (packed_wideCodeWord (packed_wideLeafIndex slot.val+offset.val)) =
      some (packed_wideLeafOp slot.val offset.val) := by
  have bound : slot.val/64 < 64 := by have := slot.isLt; omega
  have group : LeafTileDecodes (slot.val/64) := by
    generalize slot.val/64=tile at bound ⊢
    interval_cases tile
    · exact tile0
    · exact tile1
    · exact tile2
    · exact tile3
    · exact tile4
    · exact tile5
    · exact tile6
    · exact tile7
    · exact tile8
    · exact tile9
    · exact tile10
    · exact tile11
    · exact tile12
    · exact tile13
    · exact tile14
    · exact tile15
    · exact tile16
    · exact tile17
    · exact tile18
    · exact tile19
    · exact tile20
    · exact tile21
    · exact tile22
    · exact tile23
    · exact tile24
    · exact tile25
    · exact tile26
    · exact tile27
    · exact tile28
    · exact tile29
    · exact tile30
    · exact tile31
    · exact tile32
    · exact tile33
    · exact tile34
    · exact tile35
    · exact tile36
    · exact tile37
    · exact tile38
    · exact tile39
    · exact tile40
    · exact tile41
    · exact tile42
    · exact tile43
    · exact tile44
    · exact tile45
    · exact tile46
    · exact tile47
    · exact tile48
    · exact tile49
    · exact tile50
    · exact tile51
    · exact tile52
    · exact tile53
    · exact tile54
    · exact tile55
    · exact tile56
    · exact tile57
    · exact tile58
    · exact tile59
    · exact tile60
    · exact tile61
    · exact tile62
    · exact tile63
  have pos : 64*(slot.val/64)+slot.val%64=slot.val := by omega
  simpa only [Fin.val_mk,pos] using group ⟨slot.val%64,by omega⟩ offset

private theorem packed_wide_fetch_decoded (state : MachineState) (index : Nat)
    (inCode : index < 233170) (pc : state.pc=BitVec.ofNat 64 (4096+4*index))
    (instruction : Instr)
    (decoded : Manifest.decodeBase (packed_wideCodeWord index)=some instruction) :
    fetch packedWideCommitImage state=some (.base instruction) := by
  have address : state.pc.toNat=4096+4*index := by
    rw [pc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have code : packedWideCommitImage.code=ArtifactEncoding.decode 32 CommitGolfCandidate.PackedCommitArtifact.commitCode := by
    simp only [packedWideCommitImage]
  have length : index<packedWideCommitImage.code.length := by
    rw [code,ArtifactEncoding.length_decode]
    exact inCode
  have atIndex : packedWideCommitImage.code[index]?=some (CommitGolfCandidate.PackedCommitArtifact.commitCode.get 32 ⟨index,inCode⟩) := by
    rw [List.getElem?_eq_getElem length,←List.getD_eq_getElem _ _ length,code,
      ArtifactEncoding.getD_decode _ _ _ inCode]
  rw [fetch,address,ite_eq_left (by omega),show (4096+4*index-4096)/4=index by omega,atIndex]
  have base : Manifest.decodeBase (CommitGolfCandidate.PackedCommitArtifact.commitCode.get 32 ⟨index,inCode⟩)=some instruction := by
    simpa only [packed_wideCodeWord,dite_eq_left inCode] using decoded
  unfold Manifest.decodeBase at base
  cases result : decodeInstruction (CommitGolfCandidate.PackedCommitArtifact.commitCode.get 32 ⟨index,inCode⟩) with
  | none => simp [result] at base
  | some ins => cases ins <;> simp_all

theorem packed_wide_fetch_leaf (slot : Fin 4096) (offset : Fin 11) (state : MachineState)
    (pc : state.pc=packed_wideLeafPC slot.val offset.val) :
    fetch packedWideCommitImage state=some (.base (packed_wideLeafOp slot.val offset.val)) := by
  have fits : packed_wideLeafIndex slot.val+offset.val<233170 := by
    have := slot.isLt
    have := offset.isLt
    simp only [packed_wideLeafIndex]
    omega
  exact packed_wide_fetch_decoded state _ fits pc _ (packed_wide_leaf_decode slot offset)

def packed_heapRebaseIndex (tile : Nat) := packed_wideLeafIndex (64*tile+63)+11
def packed_nonceRebaseIndex (segment : Nat) := packed_wideLeafIndex (128*segment+127)+12

private theorem heap_rebase_decoded : ∀ tile : Fin 64,
    Manifest.decodeBase (packed_wideCodeWord (packed_heapRebaseIndex tile.val))=
      some (.ADDI .x20 .x12 32) := by decide +kernel

private theorem nonce_rebase_decoded : ∀ segment : Fin 32,
    Manifest.decodeBase (packed_wideCodeWord (packed_nonceRebaseIndex segment.val))=
      some (.ADD .x22 .x22 .x7) := by decide +kernel

theorem packed_wide_fetch_heap_rebase (tile : Fin 64) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*packed_heapRebaseIndex tile.val)) :
    fetch packedWideCommitImage state=some (.base (.ADDI .x20 .x12 32)) := by
  have fits : packed_heapRebaseIndex tile.val < 233170 := by unfold packed_heapRebaseIndex packed_wideLeafIndex; have := tile.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (heap_rebase_decoded tile)

theorem packed_wide_fetch_nonce_rebase (segment : Fin 32) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*packed_nonceRebaseIndex segment.val)) :
    fetch packedWideCommitImage state=some (.base (.ADD .x22 .x22 .x7)) := by
  have fits : packed_nonceRebaseIndex segment.val < 233170 := by unfold packed_nonceRebaseIndex packed_wideLeafIndex; have := segment.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (nonce_rebase_decoded segment)

theorem packed_wide_fetch_leaf_branch (state : MachineState) (pc : state.pc=184776) :
    fetch packedWideCommitImage state=some (.base (.BEQ .x20 .x21 8)) :=
  packed_wide_fetch_decoded state 45170 (by decide) pc _ rfl

theorem packed_wide_fetch_leaf_loop (state : MachineState) (pc : state.pc=184780) :
    fetch packedWideCommitImage state=some (.base (.JAL .x0 1916540)) :=
  packed_wide_fetch_decoded state 45171 (by decide) pc _ rfl

def packed_wideInitialOps : List Instr :=
  initialInstructions ++ [.ECALL] ++ readyInstructions ++ [.SLLI .x7 .x13 11,.ADDI .x10 .x10 40]

private theorem packed_wide_prelude_decoded : ∀ i : Fin 18,
    Manifest.decodeBase (packed_wideCodeWord i.val)=
      some ((packed_wideInitialOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem packed_wide_fetch_initial (i : Fin 18) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*i.val)) :
    fetch packedWideCommitImage state=some (.base ((packed_wideInitialOps[i.val]?).getD .EBREAK)) := by
  have fits : i.val<233170 := by have := i.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (packed_wide_prelude_decoded i)

private theorem packed_wide_parent_setup_decoded : ∀ i : Fin 5,
    Manifest.decodeBase (packed_wideCodeWord (45172+i.val))=
      some ((parentSetupOps[i.val]?).getD .EBREAK) := by decide +kernel

theorem packed_wide_fetch_parent_setup (i : Fin 5) (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(45172+i.val))) :
    fetch packedWideCommitImage state=some (.base ((parentSetupOps[i.val]?).getD .EBREAK)) := by
  have fits : 45172+i.val<233170 := by have := i.isLt; omega
  exact packed_wide_fetch_decoded state _ fits pc _ (packed_wide_parent_setup_decoded i)

end TwoPermutationPrototype.RV64
