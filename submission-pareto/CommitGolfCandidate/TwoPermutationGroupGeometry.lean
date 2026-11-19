import CommitGolfCandidate.TwoPermutationGroupCode
namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

structure GroupReady (node remaining : Nat) (s : MachineState) : Prop where
  pc : s.pc=0x11d8
  nodeReg : s.getReg .x6=BitVec.ofNat 64 node
  low : 256≤node
  high : node<512
  scratch : s.getReg .x23=12288
  rootBase : s.getReg .x25=16384
  markBase : s.getReg .x26=4096
  counter : s.getReg .x18=BitVec.ofNat 64 (remaining+1)
  small : remaining<2^64

def GroupAccepted (s : MachineState) (node : Nat) : Prop :=
  s.getMem (wordAddress (512+node))=0 ∨
    readBuffer s (8*(2048+4*node)) 32=readBuffer s 12288 32

instance (s : MachineState) (n : Nat) : Decidable (GroupAccepted s n) := inferInstanceAs (Decidable (_ ∨ _))

def groupMemory (s : MachineState) (node : Nat) :=
  if s.getMem (wordAddress (512+node))=0 then
    (Opening.fourWordStore s (wordAddress 1536) (wordAddress (2048+4*node))).setMem (wordAddress (512+node)) 1
  else s

private theorem shift3 (n : Nat) : (BitVec.ofNat 64 n <<< 3)=BitVec.ofNat 64 (8*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n*BitVec.ofNat 64 8=_
  rw [← BitVec.ofNat_mul,Nat.mul_comm]
private theorem shift5 (n : Nat) : (BitVec.ofNat 64 n <<< 5)=BitVec.ofNat 64 (32*n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 n*BitVec.ofNat 64 32=_
  rw [← BitVec.ofNat_mul,Nat.mul_comm]

theorem GroupReady.mark {n r : Nat} {s : MachineState} (h : GroupReady n r s) :
    groupMarkAddress s=wordAddress (512+n) := by
  rw [groupMarkAddress,h.markBase,h.nodeReg,shift3]
  change BitVec.ofNat 64 4096+BitVec.ofNat 64 (8*n)=BitVec.ofNat 64 (8*(512+n))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem GroupReady.root {n r : Nat} {s : MachineState} (h : GroupReady n r s) :
    groupRootAddress s=wordAddress (2048+4*n) := by
  rw [groupRootAddress,h.rootBase,h.nodeReg,shift5]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 (32*n)=BitVec.ofNat 64 (8*(2048+4*n))
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem group_memory_set {s t : MachineState} (equal : s.mem=t.mem) (addr value : Word) :
    (s.setMem addr value).mem=(t.setMem addr value).mem := by
  funext a
  simp [MachineState.setMem,equal]

theorem group_memory_four {s t : MachineState} (equal : s.mem=t.mem) (src dst : Word) :
    (Opening.fourWordStore s src dst).mem=(Opening.fourWordStore t src dst).mem := by
  simp only [Opening.fourWordStore,MachineState.getMem,equal]
  iterate 4 apply group_memory_set
  exact equal

private theorem stored_word_ne (state : MachineState) (src dst atWord : Word)
    (outside : ∀ j : Fin 4, atWord≠dst+BitVec.ofNat 64 (8*j.val)) :
    (Opening.fourWordStore state src dst).getMem atWord=state.getMem atWord := by
  have a : atWord≠dst := by simpa using outside 0
  have b : atWord≠dst+8#64 := outside 1
  have c : atWord≠dst+16#64 := outside 2
  have d : atWord≠dst+24#64 := outside 3
  rw [Opening.fourWordStore, MachineState.getMem_setMem_ne d,MachineState.getMem_setMem_ne c,
    MachineState.getMem_setMem_ne b,MachineState.getMem_setMem_ne a]

theorem group_memory_other (s : MachineState) (n w : Nat)
    (bounded : n<512) (wordFit : w<2^61) (markOutside : w≠512+n)
    (rootOutside : w<2048+4*n ∨ 2048+4*n+4≤w) :
    (groupMemory s n).getMem (wordAddress w)=s.getMem (wordAddress w) := by
  unfold groupMemory
  split
  · have mark : wordAddress w ≠ wordAddress (512+n) := fun eq =>
      markOutside (wordAddress_injective_of_bound wordFit (by omega) eq)
    rw [MachineState.getMem_setMem_ne mark]
    apply stored_word_ne
    intro j
    rw [word_offset]
    exact fun eq => (by have := wordAddress_injective_of_bound wordFit (by omega) eq; omega)
  · rfl

theorem group_memory_mark (s : MachineState) (n : Nat) :
    (groupMemory s n).getMem (wordAddress (512+n)) =
      if s.getMem (wordAddress (512+n))=0 then 1 else s.getMem (wordAddress (512+n)) := by
  unfold groupMemory
  split <;> simp_all [MachineState.getMem,MachineState.setMem]

theorem group_memory_root (s : MachineState) (n : Nat) (small : n<512)
    (accepted : GroupAccepted s n) :
    readBuffer (groupMemory s n) (8*(2048+4*n)) 32=readBuffer s 12288 32 := by
  unfold groupMemory
  split
  next fresh =>
    apply (read_digest_eq_iff _ _ _ _ (by omega) (by decide)).mpr
    intro j bound
    change (((Opening.fourWordStore s _ _).setMem _ _).getMem
      (BitVec.ofNat 64 (8*(2048+4*n)+8*j))) = _
    have neq : BitVec.ofNat 64 (8*(2048+4*n)+8*j) ≠ wordAddress (512+n) := by
      change BitVec.ofNat 64 _ ≠ BitVec.ofNat 64 _
      intro eq
      have numeric := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*(2048+4*n)+8*j < 2^64),
        Nat.mod_eq_of_lt (by omega : 8*(512+n)<2^64)] at numeric
      omega
    rw [MachineState.getMem_setMem_ne neq]
    have stored := four_word_store_word s (wordAddress 1536) (wordAddress (2048+4*n)) _ rfl (by omega) ⟨j,bound⟩
    simpa only [wordAddress,←BitVec.ofNat_add] using stored
  next used => exact accepted.resolve_left used

end TwoPermutationPrototype.Checker
