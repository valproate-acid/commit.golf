import CommitGolfCandidate.CapCountedLoop
import CommitGolfCandidate.WriteMemory

namespace CommitGolfCandidate.ProjectedHalfword
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private theorem byteOffset_bound (address : Word) : byteOffset address < 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem byte_address_parts (address : Word) :
    alignToDword address + BitVec.ofNat 64 (byteOffset address) = address := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have disjoint : (address &&& ~~~7#64) &&& (address &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  have combined : (address &&& ~~~7#64) ||| (address &&& 7#64) = address := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases h : (7#64)[i] <;> simp
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ disjoint, combined]

private theorem byteOffset_mod (address : Word) : byteOffset address = address.toNat % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and]
  change address.toNat &&& 7 = address.toNat % 8
  rw [show (7 : Nat) = 2^3 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

private theorem successor_slot (address : Word) (even : address.toNat % 2 = 0) :
    alignToDword (address+1) = alignToDword address ∧
      byteOffset (address+1) = byteOffset address + 1 := by
  have bounded := address.isLt
  have addValue : (address+1).toNat = address.toNat + 1 := by
    rw [BitVec.toNat_add]
    change (address.toNat+1) % 2^64 = address.toNat+1
    exact Nat.mod_eq_of_lt (by omega)
  have offsets : byteOffset (address+1) = byteOffset address + 1 := by
    rw [byteOffset_mod, byteOffset_mod, addValue]
    omega
  have split := byte_address_parts (address+1)
  rw [offsets, BitVec.ofNat_add, ← BitVec.add_assoc] at split
  have sum :
      alignToDword (address+1) + BitVec.ofNat 64 (byteOffset address) + 1 =
        alignToDword address + BitVec.ofNat 64 (byteOffset address) + 1 :=
    split.trans (congrArg (· + 1) (byte_address_parts address)).symm
  have common := congrArg (fun x : Word => x - 1 - BitVec.ofNat 64 (byteOffset address)) sum
  exact ⟨by simpa only [BitVec.add_sub_cancel] using common, offsets⟩

private theorem same_slot_addresses (destination query : Word)
    (even : destination.toNat % 2 = 0)
    (aligned : alignToDword query = alignToDword destination)
    (slot : byteOffset query / 2 = byteOffset destination / 2) :
    query = destination ∨ query = destination+1 := by
  have parity : byteOffset destination % 2 = 0 := by rw [byteOffset_mod]; omega
  have offsets : byteOffset query = byteOffset destination ∨
      byteOffset query = byteOffset destination + 1 := by omega
  have address := byte_address_parts query
  rcases offsets with same | following
  · left
    rw [aligned, same, byte_address_parts] at address
    exact address.symm
  · right
    rw [aligned, following, BitVec.ofNat_add, ← BitVec.add_assoc, byte_address_parts] at address
    exact address.symm

private theorem replace_read_byte (word : Word) (half : BitVec 16) (slot index : Nat)
    (slotBound : slot < 4) (indexBound : index < 8) :
    extractByte (replaceHalfword word slot half) index =
      if index / 2 = slot then (half >>> ((index % 2) * 8)).truncate 8
      else extractByte word index := by
  interval_cases slot <;> interval_cases index <;>
    simp (config := {decide := true}) [extractByte, replaceHalfword] <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;> interval_cases bit <;>
    simp

/-- A halfword store changes both bytes of a single slot in one doubleword. -/
theorem store_byte (state : MachineState) (destination query : Word) (value : BitVec 16) :
    (state.setHalfword destination value).getByte query =
      if alignToDword query = alignToDword destination ∧
          byteOffset query / 2 = byteOffset destination / 2 then
        (value >>> ((byteOffset query % 2) * 8)).truncate 8
      else state.getByte query := by
  by_cases aligned : alignToDword query = alignToDword destination
  · simp only [MachineState.setHalfword, MachineState.getByte, aligned,
      MachineState.getMem_setMem_eq, true_and]
    exact replace_read_byte _ _ _ _ (by have := byteOffset_bound destination; omega)
      (byteOffset_bound query)
  · simp only [MachineState.setHalfword, MachineState.getByte,
      MachineState.getMem_setMem_ne aligned, aligned, false_and, ite_false]

/-- A halfword load recovers the original byte at either position of the slot. -/
theorem load_byte (state : MachineState) (address : Word) (query : Word)
    (aligned : alignToDword query = alignToDword address)
    (slot : byteOffset query / 2 = byteOffset address / 2) :
    ((state.getHalfword address) >>> ((byteOffset query % 2) * 8)).truncate 8 =
      state.getByte query := by
  simp only [MachineState.getHalfword, MachineState.getByte, ← slot, ← aligned]
  have indexBound := byteOffset_bound query
  generalize byteOffset query = index at indexBound ⊢
  interval_cases index <;>
    apply BitVec.eq_of_getLsbD_eq <;>
    intro bit bitBound <;> interval_cases bit <;>
    simp [extractByte, extractHalfword]

/-- All bytes outside the addressed two-byte slice retain their old contents. -/
theorem store_outside (state : MachineState) (destination query : Word) (value : BitVec 16)
    (even : destination.toNat % 2 = 0) (outside : query ≠ destination ∧ query ≠ destination+1) :
    (state.setHalfword destination value).getByte query = state.getByte query := by
  rw [store_byte, ite_eq_right]
  intro sameSlot
  exact (same_slot_addresses destination query even sameSlot.1 sameSlot.2).elim outside.1 outside.2

/-- An aligned halfword copy transports both constituent bytes in little-endian order. -/
theorem copy_bytes (state : MachineState) (source target : Word)
    (sourceEven : source.toNat % 2 = 0) (targetEven : target.toNat % 2 = 0) :
    let next := state.setHalfword target (state.getHalfword source)
    next.getByte target = state.getByte source ∧ next.getByte (target+1) = state.getByte (source+1) := by
  have sourceParity : byteOffset source % 2 = 0 := by rw [byteOffset_mod]; omega
  have targetParity : byteOffset target % 2 = 0 := by rw [byteOffset_mod]; omega
  obtain ⟨sourceAligned, sourceOffset⟩ := successor_slot source sourceEven
  obtain ⟨targetAligned, targetOffset⟩ := successor_slot target targetEven
  have sourceSlot : byteOffset (source+1) / 2 = byteOffset source / 2 := by omega
  have targetSlot : byteOffset (target+1) / 2 = byteOffset target / 2 := by omega
  constructor
  · rw [store_byte, ite_eq_left ⟨rfl,rfl⟩, targetParity, ← sourceParity]
    exact load_byte state source source rfl rfl
  · rw [store_byte, ite_eq_left ⟨targetAligned,targetSlot⟩]
    have sameParity : byteOffset (target+1) % 2 = byteOffset (source+1) % 2 := by omega
    rw [sameParity]
    exact load_byte state source (source+1) sourceAligned sourceSlot

def loadState (state : MachineState) : MachineState :=
  (state.setReg .x6 ((state.getHalfword (state.getReg .x23)).zeroExtend 64)).setPC (state.pc+4)

def storeState (state : MachineState) : MachineState :=
  (state.setHalfword (state.getReg .x25) ((state.getReg .x6).truncate 16)).setPC (state.pc+4)

/-- The exact aligned load emitted in both codec copy loops. -/
theorem load_execute (image : Image) (state : MachineState) (fuel : Nat) (coins : Bool)
    (fetched : fetch image state = some (.base (.LHU .x6 .x23 0)))
    (valid : accessValid (state.getReg .x23) 2 = true) :
    execute image (1+fuel) state coins = do
      let result ← execute image fuel (loadState state) coins
      return result.charge 1 0 := by
  have stepped : ordinaryStep state (.base (.LHU .x6 .x23 0)) = some (loadState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, valid, loadState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- The exact aligned store emitted in both codec copy loops. -/
theorem store_execute (image : Image) (state : MachineState) (fuel : Nat) (coins : Bool)
    (fetched : fetch image state = some (.base (.SH .x25 .x6 0)))
    (valid : accessValid (state.getReg .x25) 2 = true) :
    execute image (1+fuel) state coins = do
      let result ← execute image fuel (storeState state) coins
      return result.charge 1 0 := by
  have stepped : ordinaryStep state (.base (.SH .x25 .x6 0)) = some (storeState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, valid, storeState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem copy_memory (state : MachineState) :
    (storeState (loadState state)).mem =
      (state.setHalfword (state.getReg .x25) (state.getHalfword (state.getReg .x23))).mem := by
  simp [storeState, loadState, MachineState.setPC, MachineState.setReg, MachineState.getReg,
    MachineState.setHalfword, MachineState.getMem, MachineState.setMem]

def copyInstructions (backward : Bool) : List Instr :=
  [.LHU .x6 .x23 0, .SH .x25 .x6 0,
   .ADDI .x23 .x23 (if backward then 4094 else 2),
   .ADDI .x25 .x25 (if backward then 4094 else 2),
   .ADDI .x28 .x28 4095, .BNE .x28 .x0 8172]

def copyPrefix (backward : Bool) (state : MachineState) (count : Nat) : MachineState :=
  ((copyInstructions backward).take count).foldl execInstrBr state

theorem copy_prefix_next (backward : Bool) (state : MachineState) (count : Nat)
    (bounded : count < 6) :
    copyPrefix backward state (count+1) =
      execInstrBr (copyPrefix backward state count)
        (((copyInstructions backward)[count]?).getD .EBREAK) := by
  have inside : count < (copyInstructions backward).length := by simpa [copyInstructions] using bounded
  unfold copyPrefix
  rw [List.take_succ_eq_append_getElem inside, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos (copyInstructions backward) count inside, Option.getD_some]

theorem copy_iteration_execute (image : Image) (backward : Bool) (state : MachineState)
    (fuel : Nat) (coins : Bool)
    (fetched : ∀ count < 6, fetch image (copyPrefix backward state count) =
      some (.base (((copyInstructions backward)[count]?).getD .EBREAK)))
    (sourceValid : accessValid (state.getReg .x23) 2 = true)
    (targetValid : accessValid (state.getReg .x25) 2 = true) :
    execute image (6+fuel) state coins =
      (do let result ← execute image fuel (copyPrefix backward state 6) coins
          return result.charge 6 0) := by
  have source : accessValid (state.regs .x23) 2 = true := sourceValid
  have target : accessValid (state.regs .x25) 2 = true := targetValid
  apply execute_unit_steps (states := copyPrefix backward state)
  intro count bounded
  refine ⟨.base (((copyInstructions backward)[count]?).getD .EBREAK), fetched count bounded, ?_, ?_⟩
  · rw [copy_prefix_next backward state count bounded]
    interval_cases count <;> cases backward <;>
      simp [copyInstructions, copyPrefix, ordinaryStep, memoryArgumentsValid, memAccess,
        execInstrBr, signExtend12, source, target, MachineState.getReg,
        MachineState.setReg, MachineState.setPC]
  · interval_cases count <;> cases backward <;> rfl

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x28 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x28 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem iteration_memory (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).mem =
      (state.setHalfword (state.getReg .x25) (state.getHalfword (state.getReg .x23))).mem := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).mem = _
  rw [branch_memory]
  simp [copyPrefix, copyInstructions, execInstrBr, signExtend12, MachineState.setPC,
    MachineState.setReg, MachineState.setHalfword, MachineState.setMem, MachineState.getReg, MachineState.getMem]

theorem iteration_source (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).getReg .x23 = state.getReg .x23 +
      signExtend12 (if backward then 4094 else 2) := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x23 = _
  rw [branch_register]
  rfl

theorem iteration_target (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).getReg .x25 = state.getReg .x25 +
      signExtend12 (if backward then 4094 else 2) := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x25 = _
  rw [branch_register]
  rfl

theorem iteration_counter (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).getReg .x28 = state.getReg .x28 + signExtend12 4095 := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x28 = _
  rw [branch_register]
  rfl

theorem prefix_pc (backward : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 5) :
    (copyPrefix backward state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> cases backward <;>
    simp [copyPrefix, copyInstructions, execInstrBr, MachineState.setPC,
      MachineState.setReg, BitVec.add_assoc]

theorem decrement (count : Nat) (positive : 0<count) :
    BitVec.ofNat 64 count + signExtend12 (4095 : BitVec 12) =
      BitVec.ofNat 64 (count-1) := by
  rw [show signExtend12 (4095 : BitVec 12) = -(1 : Word) by decide]
  have equation : count=count-1+1 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

theorem iteration_pc (backward : Bool) (state : MachineState) (count : Nat)
    (positive : 0<count) (bounded : count<2^64)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) :
    (copyPrefix backward state 6).pc = if count=1 then state.pc+24 else state.pc := by
  have nextCounter := iteration_counter backward state
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)] at nextCounter
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x28 = _ at nextCounter
  rw [branch_register, counter, decrement count positive] at nextCounter
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).pc = _
  simp only [execInstrBr, nextCounter, prefix_pc backward state 5 (by decide)]
  have zero : (copyPrefix backward state 5).getReg .x0 = 0 := rfl
  rw [zero]
  have back : state.pc+20+signExtend13 (8172 : BitVec 13)=state.pc := by
    rw [show signExtend13 (8172 : BitVec 13) = -(20 : Word) by decide]
    simp [BitVec.add_assoc]
  have exit : state.pc+20+4=state.pc+24 := by rw [BitVec.add_assoc]; rfl
  by_cases last : count=1
  · subst count
    simp only [Nat.sub_self, show BitVec.ofNat 64 0=(0:Word) by rfl,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, MachineState.setPC]
    exact exit
  · have nonzero : BitVec.ofNat 64 (count-1) ≠ (0:Word) := by
      intro equal
      have numeric := congrArg BitVec.toNat equal
      change (count-1)%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt (by omega)] at numeric
      omega
    simp only [ite_eq_right last, bne_iff_ne, ne_eq, nonzero, not_false_eq_true,
      ite_true, MachineState.setPC]
    exact back

def advance (backward : Bool) (address : Word) : Word :=
  address + signExtend12 (if backward then 4094 else 2)

def cursorAt (backward : Bool) : Nat → Word → Word
  | 0, address => address
  | count+1, address => cursorAt backward count (advance backward address)

structure CopyReady (backward : Bool) (entry : Word) (remaining : Nat)
    (state : MachineState) : Prop where
  bound : remaining < 2^64
  counter : state.getReg .x28 = BitVec.ofNat 64 remaining
  atEntry : 0 < remaining → state.pc = entry
  atExit : remaining = 0 → state.pc = entry+24
  source : ∀ i < remaining, accessValid (cursorAt backward i (state.getReg .x23)) 2 = true
  target : ∀ i < remaining, accessValid (cursorAt backward i (state.getReg .x25)) 2 = true

theorem copy_ready_next (backward : Bool) (entry : Word) (remaining : Nat) (state : MachineState)
    (ready : CopyReady backward entry (remaining+1) state) :
    CopyReady backward entry remaining (copyPrefix backward state 6) := by
  refine ⟨by have := ready.bound; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [iteration_counter, ready.counter, decrement _ (by omega), Nat.add_sub_cancel]
  · intro positive
    rw [iteration_pc backward state (remaining+1) (by omega) ready.bound ready.counter,
      ite_eq_right (by omega : remaining+1 ≠ 1), ready.atEntry (by omega)]
  · intro empty
    subst remaining
    have last := iteration_pc backward state 1 (by decide) ready.bound ready.counter
    simpa [ready.atEntry (by decide)] using last
  · intro index inside
    rw [iteration_source]
    exact ready.source (index+1) (by omega)
  · intro index inside
    rw [iteration_target]
    exact ready.target (index+1) (by omega)

private theorem fetch_copy_iteration (image : Image) (backward : Bool) (entry : Word)
    (fetched : ∀ i < 6, fetch image (initialMachine.setPC (entry + BitVec.ofNat 64 (4*i))) =
      some (.base (((copyInstructions backward)[i]?).getD .EBREAK)))
    (state : MachineState) (atEntry : state.pc = entry) :
    ∀ i < 6, fetch image (copyPrefix backward state i) =
      some (.base (((copyInstructions backward)[i]?).getD .EBREAK)) := by
  intro index inside
  have samePC : (copyPrefix backward state index).pc =
      (initialMachine.setPC (entry + BitVec.ofNat 64 (4*index))).pc := by
    rw [prefix_pc backward state index (by omega), atEntry]
    rfl
  simpa only [fetch, samePC] using fetched index inside

/-- Run either six-instruction copy body any admitted number of iterations. -/
theorem copy_run_execute (image : Image) (backward : Bool) (entry : Word)
    (fetched : ∀ i < 6, fetch image (initialMachine.setPC (entry + BitVec.ofNat 64 (4*i))) =
      some (.base (((copyInstructions backward)[i]?).getD .EBREAK)))
    (remaining : Nat) (state : MachineState) (ready : CopyReady backward entry remaining state)
    (fuel : Nat) (coins : Bool) :
    execute image (6*remaining+fuel) state coins = do
      let result ← execute image fuel (capCountedRun (fun current => copyPrefix backward current 6)
        remaining state) coins
      return result.charge (6*remaining) 0 := by
  refine cap_counted_run_execute image 6 _ (CopyReady backward entry)
    (copy_ready_next backward entry) ?_ remaining state ready fuel coins
  intro index current prepared nextFuel nextCoins
  exact copy_iteration_execute image backward current nextFuel nextCoins
    (fetch_copy_iteration image backward entry fetched current (prepared.atEntry (by omega)))
    (prepared.source 0 (by omega)) (prepared.target 0 (by omega))

/-- The loop changes memory exactly as the sequence of interleaved halfword copies. -/
def copyLoopMemory (backward : Bool) : Nat → MachineState → Word → Word → MachineState
  | 0, state, _, _ => state
  | count+1, state, source, target =>
    copyLoopMemory backward count (state.setHalfword target (state.getHalfword source))
      (advance backward source) (advance backward target)

theorem copyLoopMemory_congr (backward : Bool) (count : Nat)
    (left right : MachineState) (source target : Word) (same : left.mem = right.mem) :
    (copyLoopMemory backward count left source target).mem =
      (copyLoopMemory backward count right source target).mem := by
  induction count generalizing left right source target with
  | zero => exact same
  | succ count ih =>
    simp only [copyLoopMemory]
    apply ih
    simp only [MachineState.setHalfword, MachineState.getHalfword, MachineState.getMem,
      MachineState.setMem, same]

theorem copy_run_memory (backward : Bool) (count : Nat) (state : MachineState) :
    (capCountedRun (fun current => copyPrefix backward current 6) count state).mem =
      (copyLoopMemory backward count state (state.getReg .x23) (state.getReg .x25)).mem := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [capCountedRun, ih, copyLoopMemory, iteration_source, iteration_target]
    apply copyLoopMemory_congr
    exact iteration_memory backward state

#print axioms copy_run_execute
#print axioms copy_bytes

end CommitGolfCandidate.ProjectedHalfword
