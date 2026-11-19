import CommitGolfCandidate.TwoPermutationPackedChildCopy
import CommitGolfCandidate.TwoPermutationPackedDecode
import CommitGolfCandidate.TwoPermutationPackedCapBytes

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 1300000

def slotWord (high : Bool) : Nat := if high then 1572 else 1568

structure OperandFacts (s t : MachineState) (steps next dest : Nat) (value : BitVec 256) : Prop where
  execute : GroupHop s t steps
  pc : t.pc=BitVec.ofNat 64 (4096+4*next)
  register : ∀ r, r≠.x31 → t.getReg r=s.getReg r
  digest : readBuffer t (8*dest) 32=value
  frame : ∀ w<2^61, (w<dest ∨ dest+4≤w) → memoryView t w=memoryView s w

def childSite (leaf even : Bool) : Nat :=
  if leaf then (if even then 192 else 183) else (if even then 108 else 99)

def siblingSite (leaf even : Bool) : FieldSite :=
  if leaf then (if even then .leftLeaf else .rightLeaf) else (if even then .leftInternal else .rightInternal)

def lowSite (even : Bool) : LowSite := if even then .left else .right

def siblingCost (leaf : Bool) : Nat := if leaf then 32 else 31

def siblingState (s : MachineState) (leaf even : Bool) : MachineState :=
  if leaf then copyField (fieldCode (siblingSite leaf even)) s
  else decode (lowSite even) s (8*slotWord even)

def wire (s : MachineState) (proof : Nat) (leaf : Bool) : BitVec 256 :=
  if leaf then readBuffer s proof 32 else 0#16 ++ readBuffer s proof 30

theorem child_operand (s : MachineState) (leaf even : Bool)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*childSite leaf even))
    (source : s.getReg .x23=12288) (dest : s.getReg .x24=12544) :
    OperandFacts s (childCopied s (childSite leaf even)) 8 (childSite leaf even+8)
      (slotWord (!even)) (readBuffer s 12288 32) := by
  let start := childSite leaf even
  let target := slotWord (!even)
  let prev := if childOffset start=32 then 86 else 95
  have site : ChildSite start := by unfold ChildSite; cases leaf <;> cases even <;> decide
  have old : TwoPermutationPrototype.Checker.CopyBlock prev := by unfold TwoPermutationPrototype.Checker.CopyBlock; cases leaf <;> cases even <;> decide
  have fromOld : s.getReg (TwoPermutationPrototype.Checker.copySource prev)=wordAddress 1536 := by
    cases leaf <;> cases even <;> exact source
  have toOld : s.getReg (TwoPermutationPrototype.Checker.copyTarget prev)+
      BitVec.ofNat 64 (TwoPermutationPrototype.Checker.copyOffset prev)=wordAddress target := by
    cases leaf <;> cases even <;> change s.getReg .x24+_=_
    all_goals rw [dest]; rfl
  have bound : target+4≤2^61 := by cases even <;> decide
  have apart : 1536+4≤target := by cases even <;> decide
  have readAccess (i : Fin 4) : accessValid (s.getReg .x23+BitVec.ofNat 64 (8*i.val)) 8=true := by
    rw [source]; fin_cases i <;> decide
  have writeAccess (i : Fin 4) : accessValid (s.getReg .x24+BitVec.ofNat 64 (childOffset start+8*i.val)) 8=true := by
    rw [dest]; cases leaf <;> cases even <;> fin_cases i <;> decide
  refine ⟨execute_child_copy s start site pc readAccess writeAccess,?_,childCopied_register _ _,?_,?_⟩
  · rw [childCopied_pc,pc]
    cases leaf <;> cases even <;> rfl
  · rw [child_as_old _ _ site]
    exact TwoPermutationPrototype.Checker.copied_digest s prev 1536 target old fromOld toOld
      (by decide) bound (Or.inl apart)
  · intro w hw outside
    rw [child_as_old _ _ site]
    exact TwoPermutationPrototype.Checker.copied_word_outside s prev 1536 target w old fromOld toOld
      (by decide) bound hw (Or.inl apart) outside

private theorem word_clear (dest w : Nat) (hw : w<2^61) (bd : dest+4≤2^61)
    (outside : w<dest ∨ dest+4≤w) (i : Nat) (hi : i<8) (j : Nat) (hj : j<32) :
    BitVec.ofNat 64 (8*w+i) ≠ BitVec.ofNat 64 (8*dest+j) := by
  intro eq
  have n := congrArg BitVec.toNat eq
  rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : 8*w+i<2^64),
    Nat.mod_eq_of_lt (by omega : 8*dest+j<2^64)] at n
  omega

theorem sibling_operand (s : MachineState) (leaf even : Bool) (proof : Nat)
    (pc : s.pc=BitVec.ofNat 64 (4096+4*(siblingSite leaf even).start)) (src : s.getReg .x21=BitVec.ofNat 64 proof)
    (dst : s.getReg .x24=12544) (above : 32768≤proof) (aligned : proof%2=0)
    (room : proof+(if leaf then 32 else 30)≤MEMORY_BYTES) :
    OperandFacts s (siblingState s leaf even) (siblingCost leaf)
      ((siblingSite leaf even).start+siblingCost leaf) (slotWord even) (wire s proof leaf) := by
  let site := siblingSite leaf even
  let target := 8*slotWord even
  have bounded : target+32≤MEMORY_BYTES := by cases even <;> decide
  have small : target+32≤32768 := by cases even <;> decide
  have targetWord : slotWord even+4≤2^61 := by cases even <;> decide
  have count : 2*site.count=(if leaf then 32 else 30) := by cases leaf <;> cases even <;> rfl
  have shape : (fieldCode site).count=site.count := rfl
  have ready : CopyReady (fieldCode site) s proof target 0 := by
    refine ⟨pc,src,?_,?_,?_,aligned,by cases even <;> decide⟩
    · cases leaf <;> cases even <;> change s.getReg .x24+_=_ <;> rw [dst] <;> rfl
    · rwa [shape,count]
    · rw [shape,count]; split <;> omega
  cases leaf with
  | false =>
    have low : (lowSite even).field=siblingSite false even := by cases even <;> rfl
    have r : CopyReady (fieldCode (lowSite even).field) s proof target 0 := by rwa [low]
    refine ⟨decode_execute _ _ _ _ r bounded, ?_,decode_register _ _ _, ?_, ?_⟩
    · change (decode (lowSite even) s target).pc=BitVec.ofNat 64 (4096+4*((siblingSite false even).start+31))
      simpa only [low] using decode_pc _ _ _ _ r
    · exact decode_read _ _ _ _ r bounded (by omega) (by cases even <;> decide)
    · intro w hw outside
      apply word_eq_of_byte_frame
      intro i hi
      apply decode_byte_frame _ _ _ _ r bounded (by omega)
      exact word_clear (slotWord even) w hw targetWord outside i hi
  | true =>
    have c32 : 2*site.count=32 := count
    constructor
    · intro fuel
      have x := copy_field_execute (fieldCode site) s proof target ready fuel false
      rw [shape,c32] at x
      exact x
    · have addr := copy_field_pc (fieldCode site) s proof target ready
      rw [shape,c32] at addr
      exact addr
    · exact copy_field_register _ _
    · have exactRead := field_read site s proof target ready (by omega)
      rw [c32] at exactRead
      exact exactRead
    · intro w hw outside
      apply word_eq_of_byte_frame
      intro i hi
      have framed := (field_bytes site s proof target ready (by omega)).2
      rw [c32] at framed
      exact framed _ (word_clear _ _ hw targetWord outside i hi)

end TwoPermutationPrototype.Packed.Checker
