import CommitGolfCandidate.TwoPermutationPackedCopy
import CommitGolfCandidate.TwoPermutationPackedImage
import CommitGolfCandidate.InputMemory
import RiscvZkvm.Rv64.Logic.ByteOps

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def fieldCode (site : FieldSite) : CopyCode :=
  ⟨packedImage, site.start, site.count, .x21, site.dest, site.offset, by decide,
   by cases site <;> decide, by cases site <;> decide,
   field_fetch_load site, field_fetch_store site⟩

inductive LowSite where | right | left | boundary
def LowSite.field : LowSite → FieldSite | .right => .rightInternal | .left => .leftInternal | .boundary => .boundary
theorem LowSite.count (site : LowSite) : (fieldCode site.field).count=15 := by cases site <;> rfl
theorem clear_fetch (site : LowSite) (s : MachineState) (pc : s.pc=BitVec.ofNat 64 (4096+4*(site.field.start+30))) :
    fetch packedImage s=some (.base (.SH site.field.dest .x0 (BitVec.ofNat 12 (site.field.offset+30)))) := by
  refine cap_image_fetch _ _ _ _ (by cases site <;> decide) pc ?_
  cases site <;> rfl

def decode (site : LowSite) (s : MachineState) (target : Nat) : MachineState :=
  let copied := copyField (fieldCode site.field) s
  (copied.setHalfword (BitVec.ofNat 64 (target+30)) 0).setPC (copied.pc+4)

theorem decode_register (site : LowSite) (s : MachineState) (target : Nat) (r : Reg) (keep : r≠.x31) :
    (decode site s target).getReg r=s.getReg r := copy_field_register _ _ _ keep

theorem decode_pc (site : LowSite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (fieldCode site.field) s source target 0) :
    (decode site s target).pc=BitVec.ofNat 64 (4096+4*(site.field.start+31)) := by
  have pc := copy_field_pc _ _ _ _ ready
  rw [site.count] at pc
  change (copyField (fieldCode site.field) s).pc+BitVec.ofNat 64 4=_
  rw [pc,← BitVec.ofNat_add]
  change BitVec.ofNat 64 (4096+4*(site.field.start+2*15)+4)=_
  congr 1

theorem decode_execute (site : LowSite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (fieldCode site.field) s source target 0) (room : target+32≤MEMORY_BYTES)
    (fuel : Nat) : execute packedImage (31+fuel) s false = do
      let result ← execute packedImage fuel (decode site s target) false
      return result.charge 31 0 := by
  let c := fieldCode site.field
  let t := copyField c s
  have base : t.getReg site.field.dest+BitVec.ofNat 64 site.field.offset=BitVec.ofNat 64 target :=
    (congrArg (· + BitVec.ofNat 64 site.field.offset)
      (copy_field_register c s site.field.dest (by cases site <;> decide))).trans ready.dst
  have imm : signExtend12 (BitVec.ofNat 12 (site.field.offset+30)) =
      BitVec.ofNat 64 site.field.offset+BitVec.ofNat 64 30 := by cases site <;> decide
  have addr : t.getReg site.field.dest+signExtend12 (BitVec.ofNat 12 (site.field.offset+30))=
      BitVec.ofNat 64 (target+30) := by rw [imm,←BitVec.add_assoc,base,←BitVec.ofNat_add]
  have lim : MEMORY_BYTES<2^64 := by decide
  have even := ready.dstAligned
  have valid : accessValid (t.getReg site.field.dest+signExtend12 (BitVec.ofNat 12 (site.field.offset+30))) 2=true := by
    rw [addr]
    simp only [accessValid,rangeValid,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target+30<2^64),
      Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨by omega,by omega⟩
  have pc := copy_field_pc c s _ _ ready
  rw [show c.count=15 from site.count] at pc
  have fetched := clear_fetch site t pc
  have step : ordinaryStep t (.base (.SH site.field.dest .x0 (BitVec.ofNat 12 (site.field.offset+30))))=
      some (decode site s target) := by
    rw [addr] at valid
    simp only [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,addr,valid,ite_true]
    rfl
  have copy := copy_field_execute c s _ _ ready (1+fuel) false
  rw [show c.count=15 from site.count] at copy
  change execute packedImage (30+(1+fuel)) s false = _ at copy
  rw [show 31+fuel=30+(1+fuel) by omega,copy]
  change (do let result ← execute packedImage (1+fuel) t false; pure (result.charge 30 0)) = _
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _ fetched step]
  simp only [bind_assoc,pure_bind,Execution.charge,instructionCycles,Nat.zero_add,←Nat.add_assoc]

theorem field_bytes (site : FieldSite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (fieldCode site) s source target 0) (order : target ≤ source) :
    let t := copyField (fieldCode site) s
    (∀ i<2*site.count, t.getByte (BitVec.ofNat 64 (target+i))=s.getByte (BitVec.ofNat 64 (source+i))) ∧
    (∀ q : Word, (∀ i<2*site.count, q≠BitVec.ofNat 64 (target+i)) → t.getByte q=s.getByte q) := by
  have sb : source+2*site.count≤MEMORY_BYTES := ready.srcBound
  have tb : target+2*site.count≤MEMORY_BYTES := ready.dstBound
  have lim : MEMORY_BYTES<2^64 := by decide
  have mem := copy_field_memory _ _ _ _ ready
  have bytes := ProjectedHalfword.forward_memory site.count s source target order (by omega) (by omega)
        ready.srcAligned ready.dstAligned
  change (copyField (fieldCode site) s).mem=(ProjectedHalfword.copyLoopMemory false site.count s _ _).mem at mem
  simpa only [MachineState.getByte, MachineState.getMem,mem] using bytes

theorem field_read (site : FieldSite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (fieldCode site) s source target 0) (order : target ≤ source) :
    readBuffer (copyField (fieldCode site) s) target (2*site.count)=readBuffer s source (2*site.count) := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat _)
  apply Finset.sum_congr rfl
  intro i hi
  rw [(field_bytes _ _ _ _ ready order).1 _ (Finset.mem_range.mp hi)]

private theorem byteOffset_aligned (word i : Nat) (small : i < 8) :
    byteOffset (BitVec.ofNat 64 (8*word+i)) = i := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  change ((8*word+i)%2^64) &&& (2^3-1) = i
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

private theorem align_word (word i : Nat) (small : i < 8) :
    alignToDword (BitVec.ofNat 64 (8*word+i)) = BitVec.ofNat 64 (8*word) := by
  have split := alignToDword_add_byteOffset (BitVec.ofNat 64 (8*word+i))
  rw [byteOffset_aligned word i small] at split
  have joined : BitVec.ofNat 64 (8*word) + BitVec.ofNat 64 i = BitVec.ofNat 64 (8*word+i) := by
    rw [← BitVec.ofNat_add]
  have eq := congrArg (fun v : Word => v-BitVec.ofNat 64 i) (split.trans joined.symm)
  simpa only [BitVec.add_sub_cancel] using eq

private theorem masked_upper_byte (s : MachineState) (target i : Nat) (aligned : target%8=0) (low : 30 ≤ i) (high : i < 32) :
    (s.setHalfword (BitVec.ofNat 64 (target+30)) 0).getByte
      (BitVec.ofNat 64 (target+i)) = 0 := by
  let w := target/8+3
  have base : target+30 = 8*w+6 := by unfold w; omega
  have offset : target+i = 8*w+(i-24) := by unfold w; omega
  rw [base, offset, ProjectedHalfword.store_byte, align_word w 6 (by decide), align_word w (i-24) (by omega),
    byteOffset_aligned w 6 (by decide), byteOffset_aligned w (i-24) (by omega)]
  have slot : (i-24)/2=3 := by omega
  simp [slot]

private theorem projected_byte (x : BitVec 240) (i : Nat) (fits : i < 32) :
    (0#16 ++ x).extractLsb' (8*i) 8 =
      if i < 30 then x.extractLsb' (8*i) 8 else 0 := by
  by_cases low : i < 30
  · rw [ite_eq_left low]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have lowPart : 8*i+j < 240 := by omega
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append (x := (0#16)) (y := x) (i := 8*i+j), ite_eq_left lowPart]
  · rw [ite_eq_right low]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have highPart : ¬8*i+j < 240 := by omega
    simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
    rw [BitVec.getLsbD_append (x := (0#16)) (y := x) (i := 8*i+j), ite_eq_right highPart]
    simp

private theorem mask_outside (s : MachineState) (target : Nat) (q : Word) (even : target%2=0)
    (away₀ : q≠BitVec.ofNat 64 (target+30)) (away₁ : q≠BitVec.ofNat 64 (target+31)) :
    (s.setHalfword (BitVec.ofNat 64 (target+30)) 0).getByte q=s.getByte q := by
  apply ProjectedHalfword.store_outside
  · rw [BitVec.toNat_ofNat]; omega
  · refine ⟨away₀,?_⟩
    change q≠BitVec.ofNat 64 (target+30)+BitVec.ofNat 64 1
    rwa [←BitVec.ofNat_add]

theorem decode_byte_frame (site : LowSite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (fieldCode site.field) s source target 0) (_room : target+32≤MEMORY_BYTES)
    (order : target ≤ source) (q : Word) (outside : ∀ i<32, q≠BitVec.ofNat 64 (target+i)) :
    (decode site s target).getByte q=s.getByte q := by
  have count : site.field.count=15 := site.count
  exact (mask_outside _ target q ready.dstAligned (outside 30 (by decide)) (outside 31 (by decide))).trans
    ((field_bytes _ _ _ _ ready order).2 _ (fun i h => outside i (by rw [count] at h; omega)))

theorem decode_read (site : LowSite) (s : MachineState) (source target : Nat)
    (ready : CopyReady (fieldCode site.field) s source target 0) (room : target+32≤MEMORY_BYTES)
    (order : target ≤ source) (align : target%8=0) :
    readBuffer (decode site s target) target 32=0#16 ++ readBuffer s source 30 := by
  have lim : MEMORY_BYTES<2^64 := by decide
  have count : site.field.count=15 := site.count
  let value := (0#16 ++ readBuffer s source 30)
  have ans : readBuffer (decode site s target) target 32=value.extractLsb' (8*0) (8*32) := by
    apply read_serialized_slice
    intro i inside
    simp only [Nat.zero_add,value]
    rw [projected_byte _ i inside]
    by_cases low : i<30
    · rw [ite_eq_left low,read_buffer_byte _ _ _ _ low]
      have unequal (j : Nat) (l : 30≤j) (h : j<32) : BitVec.ofNat 64 (target+i)≠BitVec.ofNat 64 (target+j) := by
        intro eq
        have n := congrArg BitVec.toNat eq
        rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : target+i<2^64),
          Nat.mod_eq_of_lt (by omega : target+j<2^64)] at n
        omega
      exact (mask_outside _ _ _ ready.dstAligned (unequal 30 (by decide) (by decide))
        (unequal 31 (by decide) (by decide))).trans ((field_bytes _ _ _ _ ready order).1 i (by rw [count]; omega))
    · rw [ite_eq_right low]
      exact masked_upper_byte _ target i align (by omega) inside
  simpa only [Nat.mul_zero,BitVec.extractLsb'_eq_self,value] using ans

end TwoPermutationPrototype.Packed.Checker
