import CommitGolfCandidate.TwoPermutationPackedOpeningCapMoves
import CommitGolfCandidate.TwoPermutationPackedOpeningBytes
import CommitGolfCandidate.TwoPermutationPackedCopy
import CommitGolfCandidate.TwoPermutationPackedMemory
import RiscvZkvm.Rv64.Logic.ByteOps

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.Packed

def fieldCode (site : CopySite) : CopyCode where
  image := openingImage
  start := site.start
  count := site.halfwords
  source := .x7
  dest := .x21
  destOffset := 0
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by cases site <;> norm_num [CopySite.halfwords]
  load := fun offset inside state pc => fetch_copy_load site ⟨offset, inside⟩ state pc
  store := fun offset inside state pc => by
    simpa only [Nat.zero_add, copyStore] using fetch_copy_store site ⟨offset, inside⟩ state pc

def copyState (site : CopySite) (state : MachineState) : MachineState :=
  copyField (fieldCode site) state

structure FieldInputs (site : CopySite) (state : MachineState) (source target : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*site.start)
  sourceReg : state.getReg .x7 = BitVec.ofNat 64 source
  targetReg : state.getReg .x21 = BitVec.ofNat 64 target
  disjoint : source+2*site.halfwords ≤ target
  targetFit : target+2*site.halfwords ≤ MEMORY_BYTES
  sourceEven : source % 2 = 0
  targetEven : target % 2 = 0

private theorem FieldInputs.ready {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    CopyReady (fieldCode site) state source target 0 := by
  refine ⟨?_, input.sourceReg, ?_, ?_, input.targetFit, input.sourceEven, input.targetEven⟩
  · simpa [fieldCode] using input.pc
  · simpa [fieldCode] using input.targetReg
  · exact input.disjoint.trans (Nat.le_trans (Nat.le_add_right _ _) input.targetFit)

theorem FieldInputs.run {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    RunsOpeningBlock state (copyState site state) (2*site.halfwords) :=
  copy_field_execute (fieldCode site) state source target input.ready

theorem FieldInputs.final_pc {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    (copyState site state).pc = BitVec.ofNat 64 (4096+4*(site.start+2*site.halfwords)) :=
  copy_field_pc (fieldCode site) state source target input.ready

theorem copy_register (site : CopySite) (state : MachineState) (reg : Reg) (kept : reg ≠ .x31) :
    (copyState site state).getReg reg = state.getReg reg :=
  copy_field_register (fieldCode site) state reg kept

theorem FieldInputs.bytes {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) :
    ByteCopy state (copyState site state) source target (2*site.halfwords) := by
  have mem : (copyState site state).mem =
      (ProjectedHalfword.copyLoopMemory false site.halfwords state (BitVec.ofNat 64 source)
        (BitVec.ofNat 64 target)).mem :=
    copy_field_memory (fieldCode site) state source target input.ready
  have targetBound : target+2*site.halfwords ≤ 2^64 :=
    input.targetFit.trans (by decide)
  obtain ⟨copied, frame⟩ := forward_disjoint_memory site.halfwords state source target
    input.disjoint (input.disjoint.trans (Nat.le_trans (Nat.le_add_right _ _) targetBound)) targetBound input.sourceEven input.targetEven
  exact ⟨fun index inside => by
    simpa only [MachineState.getByte, MachineState.getMem, mem] using copied index inside,
    fun address outside => by
      simpa only [MachineState.getByte, MachineState.getMem, mem] using frame address outside⟩

theorem aligned_dword_above (base target : Nat) (baseAligned : base % 8 = 0)
    (above : base ≤ target) (fit : target+8 ≤ 2^64) :
    base ≤ (alignToDword (BitVec.ofNat 64 target)).toNat := by
  let word : Word := BitVec.ofNat 64 target
  let aligned := alignToDword word
  have wordAsNat : word.toNat = target := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : target < 2^64)]
  have alignedAtMost : aligned.toNat ≤ target := by
    rw [show aligned.toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word < 8 := byteOffset_lt_8
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  change (aligned+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : byteOffset word < 2^64),
    Nat.mod_eq_of_lt (by omega)] at whole
  have even := alignToDword_byteOffset_zero word
  change (aligned &&& 7#64).toNat = 0 at even
  rw [BitVec.toNat_and] at even
  change aligned.toNat &&& (2^3-1) = 0 at even
  rw [Nat.and_two_pow_sub_one_eq_mod] at even
  change base ≤ aligned.toNat
  omega

private theorem copyLoop_words_before (count : Nat) (state : MachineState) (source target base address : Nat)
    (below : address < base) (upper : base ≤ target) (baseAligned : base % 8 = 0)
    (fit : target+2*count ≤ MEMORY_BYTES) :
    (ProjectedHalfword.copyLoopMemory false count state (BitVec.ofNat 64 source)
      (BitVec.ofNat 64 target)).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  induction count generalizing state source target with
  | zero => rfl
  | succ count ih =>
    have shift (x : Nat) : ProjectedHalfword.advance false (BitVec.ofNat 64 x) =
        BitVec.ofNat 64 (x+2) := by
      rw [BitVec.ofNat_add]
      rfl
    simp only [ProjectedHalfword.copyLoopMemory, shift]
    rw [ih _ (source+2) (target+2) (by omega) (by omega)]
    unfold MachineState.setHalfword
    apply MachineState.getMem_setMem_ne
    intro equal
    have limit : MEMORY_BYTES+8 ≤ 2^64 := by decide
    have align := aligned_dword_above base target baseAligned upper (by omega)
    rw [← equal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : address < 2^64)] at align
    omega

theorem FieldInputs.words_before {site : CopySite} {state : MachineState} {source target : Nat}
    (input : FieldInputs site state source target) (base address : Nat)
    (below : address < base) (upper : base ≤ target) (aligned : base % 8 = 0) :
    (copyState site state).getMem (BitVec.ofNat 64 address) =
      state.getMem (BitVec.ofNat 64 address) := by
  have mem : (copyState site state).mem =
      (ProjectedHalfword.copyLoopMemory false site.halfwords state (BitVec.ofNat 64 source)
        (BitVec.ofNat 64 target)).mem :=
    copy_field_memory (fieldCode site) state source target input.ready
  simpa only [MachineState.getMem, mem] using
    copyLoop_words_before site.halfwords state source target base address below upper aligned
      input.targetFit

end TwoPermutationPrototype.PackedOpening
