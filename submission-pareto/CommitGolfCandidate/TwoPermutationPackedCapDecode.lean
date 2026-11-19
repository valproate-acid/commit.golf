import CommitGolfCandidate.TwoPermutationPackedCapFrontier
import CommitGolfCandidate.TwoPermutationPackedCopy
import RiscvZkvm.Rv64.Logic.ByteOps

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Packed ProjectedHalfword
open TwoPermutationPrototype.Checker (capRootAt)
set_option maxRecDepth 4096

private def boundaryCode : CopyCode where
  image := packedImage
  start := 298
  count := 15
  source := .x21
  dest := .x7
  destOffset := 0
  sourceTemp := by decide
  destTemp := by decide
  offsetBound := by decide
  load := fun i hi s pc => field_fetch_load .boundary i hi s pc
  store := fun i hi s pc => field_fetch_store .boundary i hi s pc

private def maskFooter (s : MachineState) := execInstrBr s (.SH .x7 .x0 30)

def frontierRead (s : MachineState) :=
  frontierFinish (maskFooter (copyField boundaryCode (frontierPrefix s 4)))

private def slotAddress (node : Nat) : Nat := 8*(2048+4*node)

private theorem copy_registers {s : MachineState} {node proof : Nat} (ready : FrontierReady s node proof) :
    (frontierPrefix s 4).getReg .x21 = BitVec.ofNat 64 proof ∧
    (frontierPrefix s 4).getReg .x7 = BitVec.ofNat 64 (slotAddress node) := by
  refine ⟨(frontier_prefix_register s _ (by decide) (by decide)).trans ready.proofReg, ?_⟩
  rw [(frontier_prefix_post s ready.pc).2.1, ready.nodeReg, ready.capReg, BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 16384+BitVec.ofNat 64 node*BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  unfold slotAddress
  omega

private theorem copy_ready {s : MachineState} {node proof : Nat}
    (ready : FrontierReady s node proof) (fits : ¬ s.getReg .x22 < s.getReg .x21+30#64) :
    CopyReady boundaryCode (frontierPrefix s 4) proof (slotAddress node) 0 := by
  have regs := copy_registers ready
  have bounded := ready.below
  have room : 32768 ≤ MEMORY_BYTES := by decide
  refine ⟨?_, regs.1, ?_, ready.room, ?_, ready.even, ?_⟩
  · exact (frontier_prefix_post s ready.pc).1.trans (ite_eq_right fits)
  · change (frontierPrefix s 4).getReg .x7 + 0#64 = _
    exact (BitVec.add_zero _).trans regs.2
  · change slotAddress node+30 ≤ MEMORY_BYTES
    unfold slotAddress
    omega
  · change slotAddress node%2=0
    unfold slotAddress
    omega

private theorem maskFooter_word (s : MachineState) (target : Nat)
    (reg : s.getReg .x7 = BitVec.ofNat 64 target) :
    (maskFooter s).mem = (s.setHalfword (BitVec.ofNat 64 (target+30)) 0).mem := by
  simp only [maskFooter, execInstrBr, reg, show signExtend12 30 = 30#64 by decide,
    show s.getReg .x0 = 0#64 from rfl, BitVec.ofNat_add]
  rfl

private theorem maskFooter_register (s : MachineState) (r : Reg) :
    (maskFooter s).getReg r = s.getReg r := rfl

private theorem maskFooter_pc (s : MachineState) : (maskFooter s).pc = s.pc+4#64 := rfl

private theorem execute_mask_footer (s : MachineState) (pc : s.pc = 0x1520)
    (target : Nat) (reg : s.getReg .x7 = BitVec.ofNat 64 target)
    (bounds : target+32 ≤ MEMORY_BYTES) (even : target%2=0) (fuel : Nat) :
    execute packedImage (1+fuel) s false =
      (do let result ← execute packedImage fuel (maskFooter s) false
          return result.charge 1 0) := by
  have fetchMask := cap_fetch s 328 (.SH .x7 .x0 30) (by decide) pc rfl
  have maxMemory : MEMORY_BYTES < 2^64 := by decide
  have safe : accessValid (s.getReg .x7 + signExtend12 30) 2 = true := by
    rw [reg, show signExtend12 30 = BitVec.ofNat 64 30 by decide, ← BitVec.ofNat_add]
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : target+30 < 2^64), Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨bounds, by omega⟩
  have actual : ordinaryStep s (.base (.SH .x7 .x0 30)) = some (maskFooter s) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, safe, ite_true, maskFooter]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetchMask actual]
  rfl

private theorem copied_pc {s : MachineState} {node proof : Nat}
    (ready : FrontierReady s node proof) (fits : ¬ s.getReg .x22 < s.getReg .x21+30#64) :
    (copyField boundaryCode (frontierPrefix s 4)).pc = 0x1520 :=
  copy_field_pc boundaryCode _ _ _ (copy_ready ready fits)

private theorem frontier_execution {s : MachineState} {node proof : Nat}
    (ready : FrontierReady s node proof) (fits : ¬ s.getReg .x22 < s.getReg .x21+30#64) (fuel : Nat) :
    execute packedImage (36+fuel) s false = do
      let result ← execute packedImage fuel (frontierRead s) false
      return result.charge 36 0 := by
  let prepared := frontierPrefix s 4
  let copied := copyField boundaryCode prepared
  have dst : copied.getReg .x7 = BitVec.ofNat 64 (slotAddress node) :=
    (copy_field_register boundaryCode prepared .x7 (by decide)).trans (copy_registers ready).2
  have pc : copied.pc = 0x1520 := copied_pc ready fits
  have room : slotAddress node+32 ≤ MEMORY_BYTES := by
    have small := ready.below
    have limit : 32768 ≤ MEMORY_BYTES := by decide
    unfold slotAddress
    omega
  have maskedPC : (maskFooter copied).pc = 0x1524 := by rw [maskFooter_pc, pc]; rfl
  have copy : execute packedImage (30+(1+(1+fuel))) prepared false =
      (do let result ← execute packedImage (1+(1+fuel)) copied false
          return result.charge 30 0) :=
    copy_field_execute boundaryCode prepared proof (slotAddress node)
      (copy_ready ready fits) (1+(1+fuel)) false
  rw [show 36+fuel = 4+(30+(1+(1+fuel))) by omega, execute_frontier_prefix _ ready.pc,
    copy, execute_mask_footer copied pc _ dst room (by unfold slotAddress; omega), execute_frontier_finish _ maskedPC]
  simp [frontierRead, Execution.charge, ← Nat.add_assoc]
  rfl

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

private theorem masked_upper_byte (s : MachineState) (node i : Nat) (low : 30 ≤ i) (high : i < 32) :
    (s.setHalfword (BitVec.ofNat 64 (slotAddress node+30)) 0).getByte
      (BitVec.ofNat 64 (slotAddress node+i)) = 0 := by
  let w := 2048+4*node+3
  have base : slotAddress node+30 = 8*w+6 := by unfold w slotAddress; omega
  have offset : slotAddress node+i = 8*w+(i-24) := by unfold w slotAddress; omega
  rw [base, offset, store_byte, align_word w 6 (by decide), align_word w (i-24) (by omega),
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

private theorem frontier_memory {s : MachineState} {node proof : Nat}
    (ready : FrontierReady s node proof) (fits : ¬ s.getReg .x22 < s.getReg .x21+30#64) :
    let target := slotAddress node
    (∀ i < 30, (frontierRead s).getByte (BitVec.ofNat 64 (target+i)) =
      s.getByte (BitVec.ofNat 64 (proof+i))) ∧
    (∀ i, 30 ≤ i → i < 32 → (frontierRead s).getByte (BitVec.ofNat 64 (target+i)) = 0) ∧
    (∀ address < 2^64, address < target ∨ target+32 ≤ address →
      (frontierRead s).getByte (BitVec.ofNat 64 address) = s.getByte (BitVec.ofNat 64 address)) := by
  let target := slotAddress node
  let prepared := frontierPrefix s 4
  let copied := copyField boundaryCode prepared
  let done := frontierRead s
  have same : prepared.mem = s.mem := (frontier_prefix_post s ready.pc).2.2.2
  have memory64 : MEMORY_BYTES < 2^64 := by decide
  have targetRoom : target+32 ≤ MEMORY_BYTES := by
    have bound := ready.below
    have memory : 32768 ≤ MEMORY_BYTES := by decide
    unfold target slotAddress
    omega
  have sourceRoom := ready.room
  have above := ready.above
  have separate : target ≤ proof := by
    have bound := ready.below
    unfold target slotAddress
    omega
  have even : target%2=0 := by unfold target slotAddress; omega
  let loop := copyLoopMemory false 15 prepared (BitVec.ofNat 64 proof) (BitVec.ofNat 64 target)
  have copiedMem : copied.mem = loop.mem := copy_field_memory boundaryCode _ _ _ (copy_ready ready fits)
  have dst : copied.getReg .x7 = BitVec.ofNat 64 target :=
    (copy_field_register boundaryCode prepared .x7 (by decide)).trans (copy_registers ready).2
  have stored : done.mem = (copied.setHalfword (BitVec.ofNat 64 (target+30)) 0).mem :=
    maskFooter_word copied target dst
  obtain ⟨bytes, frame⟩ := forward_memory 15 prepared proof target separate
    (by omega) (by omega) ready.even even
  have maskFrame (address : Nat) (fit : address < 2^64) (outside : address < target+30 ∨ target+32 ≤ address) :
      done.getByte (BitVec.ofNat 64 address) = copied.getByte (BitVec.ofNat 64 address) := by
    have exactMem : done.getByte (BitVec.ofNat 64 address) =
        (copied.setHalfword (BitVec.ofNat 64 (target+30)) 0).getByte (BitVec.ofNat 64 address) := by
      simp only [MachineState.getByte, MachineState.getMem, stored]
    rw [exactMem]
    apply store_outside
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : target+30 < 2^64)]
      omega
    · have next : BitVec.ofNat 64 (target+30)+1 = BitVec.ofNat 64 (target+31) := by
        change BitVec.ofNat 64 (target+30)+BitVec.ofNat 64 1 = _
        rw [← BitVec.ofNat_add]
      rw [next]
      constructor <;> intro hit
      all_goals
        have eq := Opening.nat_address_injective fit (by omega) hit
        omega
  refine ⟨?_, ?_, ?_⟩
  · intro i inside
    have written : copied.getByte (BitVec.ofNat 64 (target+i)) = s.getByte (BitVec.ofNat 64 (proof+i)) := by
      simpa only [MachineState.getByte, MachineState.getMem, copiedMem, same] using bytes i inside
    exact (maskFrame _ (by omega) (Or.inl (by omega))).trans written
  · intro i low high
    have padded := masked_upper_byte copied node i low high
    change done.getByte (BitVec.ofNat 64 (target+i)) = 0
    simpa only [MachineState.getByte, MachineState.getMem, stored] using padded
  · intro addr fit outside
    have retained : copied.getByte (BitVec.ofNat 64 addr) = s.getByte (BitVec.ofNat 64 addr) := by
      have harmless : ∀ i < 30, BitVec.ofNat 64 addr ≠ BitVec.ofNat 64 (target+i) := by
        intro i small eq
        have same := Opening.nat_address_injective fit (by omega) eq
        omega
      simpa only [MachineState.getByte, MachineState.getMem, copiedMem, same] using frame _ harmless
    exact (maskFrame _ fit (outside.imp (by omega) id)).trans retained

noncomputable def actualFrontier : FrontierKernel where
  after := frontierRead
  run := fun _ _ _ ready fits => frontier_execution ready fits
  digest := by
    intro s n p ready fits
    have ⟨bytes, zero, _⟩ := frontier_memory ready fits
    let value := (0#16 ++ readBuffer s p 30)
    have loaded : readBuffer (frontierRead s) (slotAddress n) 32 = value.extractLsb' (8*0) (8*32) := by
      apply read_serialized_slice
      intro i inside
      simp only [Nat.zero_add, value]
      rw [projected_byte _ i inside]
      by_cases low : i<30
      · rw [ite_eq_left low, read_buffer_byte _ _ _ _ low]
        exact bytes i low
      · rw [ite_eq_right low]
        exact zero i (by omega) inside
    simpa only [capRootAt, slotAddress, Nat.mul_zero, BitVec.extractLsb'_eq_self, value] using loaded
  register := by
    intro s r a b c d
    unfold frontierRead frontierFinish
    rw [MachineState.getReg_setPC, Opening.getReg_setReg, ite_eq_right (by simp [Ne.symm b]),
      maskFooter_register, copy_field_register _ _ _ d]
    exact frontier_prefix_register s r a c
  pointer := by
    intro s n p ready
    refine ⟨rfl, ?_⟩
    unfold frontierRead frontierFinish
    rw [MachineState.getReg_setPC, Opening.getReg_setReg,
      ite_eq_left (by decide : Reg.x21 = .x21 ∧ Reg.x21 ≠ .x0),
      maskFooter_register, copy_field_register _ _ _ (by decide), (copy_registers ready).1, BitVec.ofNat_add]
  frame := by
    intro s n p ready fits w bounded outside
    have frame := (frontier_memory ready fits).2.2
    apply word_eq_of_byte_frame
    intro i inside
    unfold slotAddress at frame
    exact frame _ (by omega) (outside.imp (by omega) (by omega))

end TwoPermutationPrototype.Packed.Checker
