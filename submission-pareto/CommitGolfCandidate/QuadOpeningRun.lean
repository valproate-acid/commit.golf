import CommitGolfCandidate.QuadOpeningImage
import CommitGolfCandidate.QOpeningFootprint

/-! Straight-line execution of the penta opening image: blocks of ordinary instructions with
their step (fuel) and cycle counts (multiply/divide instructions cost 4 cycles but one step),
and the doubleword copy blocks together with the output invariant `Inv`. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open QOpening (trapdoorBase proofBase)

/-- `before` runs to `after` in `steps` machine steps charging `cycles` cycles. -/
def Runs (before after : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel allowCoins, execute openingImage (steps + fuel) before allowCoins =
    (do let result ← execute openingImage fuel after allowCoins
        return result.charge cycles 0)

private theorem charge_zero (result : Execution) : result.charge 0 0 = result := by
  cases result
  simp [Execution.charge]

theorem Runs.zero (state : MachineState) : Runs state state 0 0 := by
  intro fuel coins
  simp [charge_zero]

theorem Runs.trans {first middle last : MachineState} {s₁ c₁ s₂ c₂ : Nat}
    (head : Runs first middle s₁ c₁) (tail : Runs middle last s₂ c₂) :
    Runs first last (s₁+s₂) (c₁+c₂) := by
  intro fuel coins
  rw [Nat.add_assoc, head (s₂+fuel) coins, tail fuel coins]
  simp [Execution.charge, Nat.add_assoc]

theorem Runs.cast {before after : MachineState} {s c s' c' : Nat} (run : Runs before after s c)
    (hs : s = s') (hc : c = c') : Runs before after s' c' := by
  subst hs hc
  exact run

/-- Instructions without a memory access, branch, jump or system call. -/
def pureOp : Instr → Bool
  | .ADDI .. | .SLLI .. | .ADD .. | .SUB .. | .LUI .. | .MUL .. | .DIVU .. | .REMU .. => true
  | _ => false

/-- Straight-line instructions: the pure ones and doubleword loads/stores. -/
def straight : Instr → Bool
  | .LD .. | .SD .. => true
  | instruction => pureOp instruction

theorem straight_pc (state : MachineState) (instruction : Instr) (line : straight instruction = true) :
    (execInstrBr state instruction).pc = state.pc + 4 := by
  cases instruction <;> simp [straight, pureOp] at line <;> rfl

theorem straight_step (state : MachineState) (instruction : Instr) (line : straight instruction = true)
    (valid : memoryArgumentsValid state instruction = true) :
    ordinaryStep state (.base instruction) = some (execInstrBr state instruction) := by
  cases instruction <;> simp [straight, pureOp] at line <;> simp [ordinaryStep, valid]

theorem pure_valid (state : MachineState) (instruction : Instr) (pure : pureOp instruction = true) :
    memoryArgumentsValid state instruction = true := by
  cases instruction <;> simp [pureOp] at pure <;> rfl

theorem runs_one (state : MachineState) (instruction : Instr) (index : Nat)
    (code : program[index]? = some instruction) (pc : state.pc = BitVec.ofNat 64 (4096+4*index))
    (line : straight instruction = true) (valid : memoryArgumentsValid state instruction = true) :
    Runs state (execInstrBr state instruction) 1 (instructionCycles (.base instruction)) := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program state index instruction code pc)
    (straight_step state instruction line valid)]

def cost (code : List Instr) : Nat := (code.map fun instruction => instructionCycles (.base instruction)).sum

/-- `code` sits in the program from word `start`. -/
def CodeAt (start : Nat) (code : List Instr) : Prop := ∀ i < code.length, program[start+i]? = code[i]?

instance (start : Nat) (code : List Instr) : Decidable (CodeAt start code) := by
  unfold CodeAt
  infer_instance

theorem pc_next (pc : Word) (start : Nat) (at_ : pc = BitVec.ofNat 64 (4096+4*start)) :
    pc + 4 = BitVec.ofNat 64 (4096+4*(start+1)) := by
  rw [at_, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
  congr 1

theorem runs_code : ∀ (code : List Instr) (start : Nat) (state : MachineState), CodeAt start code →
    state.pc = BitVec.ofNat 64 (4096+4*start) → code.all straight = true →
    (∀ i (h : i < code.length), memoryArgumentsValid ((code.take i).foldl execInstrBr state) code[i] = true) →
    Runs state (code.foldl execInstrBr state) code.length (cost code)
  | [], _, state, _, _, _, _ => Runs.zero state
  | first :: rest, start, state, code, pc, line, valid => by
    have lines : straight first = true ∧ rest.all straight = true := by simpa using line
    have head := runs_one state first start (by simpa using code 0 (by simp)) pc lines.1
      (valid 0 (by simp))
    have tail := runs_code rest (start+1) (execInstrBr state first)
      (fun i h => by
        have := code (i+1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      ((straight_pc state first lines.1).trans (pc_next _ _ pc)) lines.2
      (fun i h => valid (i+1) (by simp; omega))
    have joined := head.trans tail
    refine joined.cast (by simp [Nat.add_comm]) ?_
    simp [cost]

theorem runs_pure (code : List Instr) (start : Nat) (state : MachineState) (at_ : CodeAt start code)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*start)) (pure : code.all pureOp = true) :
    Runs state (code.foldl execInstrBr state) code.length (cost code) := by
  apply runs_code code start state at_ pc
  · simp only [List.all_eq_true] at pure ⊢
    intro x member
    have := pure x member
    cases x <;> simp_all [straight, pureOp]
  · intro i h
    apply pure_valid
    simp only [List.all_eq_true] at pure
    exact pure _ (List.getElem_mem h)

theorem pure_pc : ∀ (code : List Instr) (state : MachineState), code.all pureOp = true →
    (code.foldl execInstrBr state).pc = state.pc + BitVec.ofNat 64 (4*code.length)
  | [], state, _ => by simp
  | first :: rest, state, pure => by
    have lines : pureOp first = true ∧ rest.all pureOp = true := by simpa using pure
    have step : (execInstrBr state first).pc = state.pc + 4 :=
      straight_pc state first (by cases first <;> simp_all [straight, pureOp])
    rw [List.foldl_cons, pure_pc rest _ lines.2, step, BitVec.add_assoc]
    congr 1
    rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]
    congr 1
    simp
    omega

theorem mem_set_reg (state : MachineState) (reg : Reg) (value : Word) :
    (state.setReg reg value).mem = state.mem := by cases reg <;> rfl

theorem pure_mem : ∀ (code : List Instr) (state : MachineState), code.all pureOp = true →
    (code.foldl execInstrBr state).mem = state.mem
  | [], state, _ => rfl
  | first :: rest, state, pure => by
    have lines : pureOp first = true ∧ rest.all pureOp = true := by simpa using pure
    rw [List.foldl_cons, pure_mem rest _ lines.2]
    cases first <;> simp [pureOp] at lines <;> simp [execInstrBr, mem_set_reg, MachineState.setPC]

/-! ### The output invariant -/

/-- Every input word (between the trapdoor and the proof) is unchanged, and the first `count`
output doublewords hold the initial words named by `source`. -/
structure Inv (init state : MachineState) (source : Nat → Nat) (count : Nat) : Prop where
  input : ∀ address, trapdoorBase ≤ address → address < proofBase →
    state.getMem (BitVec.ofNat 64 address) = init.getMem (BitVec.ofNat 64 address)
  output : ∀ u < count, state.getMem (BitVec.ofNat 64 (proofBase+8*u)) =
    init.getMem (BitVec.ofNat 64 (source u))

theorem Inv.of_mem {init before after : MachineState} {source : Nat → Nat} {count : Nat}
    (inv : Inv init before source count) (same : after.mem = before.mem) : Inv init after source count :=
  ⟨fun a l h => by simpa only [MachineState.getMem, same] using inv.input a l h,
   fun u h => by simpa only [MachineState.getMem, same] using inv.output u h⟩

theorem Inv.cast_count {init state : MachineState} {source : Nat → Nat} {count count' : Nat}
    (inv : Inv init state source count) (same : count = count') : Inv init state source count' := by
  subst same
  exact inv

theorem Inv.store {init state : MachineState} {source : Nat → Nat} {count : Nat}
    (inv : Inv init state source count) (fits : proofBase+8*count+8 ≤ MEMORY_BYTES) (value : Word)
    (correct : value = init.getMem (BitVec.ofNat 64 (source count))) :
    Inv init (state.setMem (BitVec.ofNat 64 (proofBase+8*count)) value) source (count+1) := by
  have room : MEMORY_BYTES < 2^64 := by decide
  refine ⟨fun a low high => ?_, fun u h => ?_⟩
  · have different : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 (proofBase+8*count) := by
      intro same
      have := QOpening.nat_address_injective (by omega) (by omega) same
      omega
    rw [MachineState.getMem_setMem_ne different]
    exact inv.input a low high
  · by_cases last : u = count
    · subst u
      rw [MachineState.getMem_setMem_eq, correct]
    · have different : BitVec.ofNat 64 (proofBase+8*u) ≠ BitVec.ofNat 64 (proofBase+8*count) := by
        intro same
        have := QOpening.nat_address_injective (by omega) (by omega) same
        omega
      rw [MachineState.getMem_setMem_ne different]
      exact inv.output u (by omega)

/-! ### Doubleword copy blocks -/

theorem pair_code_load : ∀ n ≤ 4, ∀ w < n,
    (pairCode n)[2*w]? = some (.LD .x31 .x7 (BitVec.ofNat 12 (8*w))) := by decide

theorem pair_code_store : ∀ n ≤ 4, ∀ w < n,
    (pairCode n)[2*w+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) := by decide

theorem pair_code_length (n : Nat) : (pairCode n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairCode, List.range_succ, List.flatMap_append] at ih ⊢
    simp [ih]
    omega

theorem pair_code_succ (n : Nat) : pairCode (n+1) =
    pairCode n ++ [.LD .x31 .x7 (BitVec.ofNat 12 (8*n)), .SD .x21 .x31 (BitVec.ofNat 12 (8*n))] := by
  simp [pairCode, List.range_succ, List.flatMap_append]

private theorem offset_value : ∀ w < 4, signExtend12 (BitVec.ofNat 12 (8*w)) = BitVec.ofNat 64 (8*w) := by
  decide

/-- One load/store pair of a copy block: word `count` of the output is the source word `w`. -/
theorem pair_step (init state : MachineState) (source : Nat → Nat) (start m w count S D : Nat)
    (small : m ≤ 4) (live : w < m) (code : CodeAt start (pairCode m))
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(start+2*w)))
    (from_ : state.getReg .x7 = BitVec.ofNat 64 S) (to_ : state.getReg .x21 = BitVec.ofNat 64 D)
    (target : D+8*w = proofBase+8*count) (aligned : S % 8 = 0) (low : trapdoorBase ≤ S)
    (high : S+8*w+8 ≤ proofBase) (fits : proofBase+8*count+8 ≤ MEMORY_BYTES)
    (named : source count = S+8*w) (inv : Inv init state source count) :
    let after := execInstrBr (execInstrBr state (.LD .x31 .x7 (BitVec.ofNat 12 (8*w))))
      (.SD .x21 .x31 (BitVec.ofNat 12 (8*w)))
    Runs state after 2 2 ∧ Inv init after source (count+1) ∧ after.pc = state.pc+8 ∧
      ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  have offset := offset_value w (by omega)
  have room : MEMORY_BYTES < 2^64 := by decide
  have heap : trapdoorBase % 8 = 0 := by decide
  have proofAligned : proofBase % 8 = 0 := by decide
  have below : proofBase ≤ MEMORY_BYTES := by decide
  let loaded := execInstrBr state (.LD .x31 .x7 (BitVec.ofNat 12 (8*w)))
  have loadAddress : state.getReg .x7 + signExtend12 (BitVec.ofNat 12 (8*w)) = BitVec.ofNat 64 (S+8*w) := by
    rw [from_, offset, ← BitVec.ofNat_add]
  have storeAddress : loaded.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*w)) =
      BitVec.ofNat 64 (proofBase+8*count) := by
    have keep : loaded.getReg .x21 = state.getReg .x21 := by
      simp [loaded, execInstrBr, QOpening.getReg_setReg]
    rw [keep, to_, offset, ← BitVec.ofNat_add, target]
  have loadCode : program[start+2*w]? = some (.LD .x31 .x7 (BitVec.ofNat 12 (8*w))) := by
    have := code (2*w) (by rw [pair_code_length]; omega)
    rw [this, pair_code_load m small w live]
  have storeCode : program[start+2*w+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) := by
    have := code (2*w+1) (by rw [pair_code_length]; omega)
    rw [Nat.add_assoc, this, pair_code_store m small w live]
  have loadValid : memoryArgumentsValid state (.LD .x31 .x7 (BitVec.ofNat 12 (8*w))) = true := by
    simp only [memoryArgumentsValid, memAccess, loadAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have storeValid : memoryArgumentsValid loaded (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) = true := by
    simp only [memoryArgumentsValid, memAccess, storeAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have loadPC : loaded.pc = BitVec.ofNat 64 (4096+4*(start+2*w+1)) :=
    (straight_pc state _ rfl).trans (pc_next _ _ pc)
  have run₁ := runs_one state _ (start+2*w) loadCode pc rfl loadValid
  have run₂ := runs_one loaded _ (start+2*w+1) storeCode loadPC rfl storeValid
  have value : loaded.getReg .x31 = init.getMem (BitVec.ofNat 64 (source count)) := by
    simp only [loaded, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp only [loadAddress, ite_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, named]
    exact inv.input _ (by omega) (by omega)
  have memory : after.mem = (state.setMem (BitVec.ofNat 64 (proofBase+8*count))
      (init.getMem (BitVec.ofNat 64 (source count)))).mem := by
    show (execInstrBr loaded _).mem = _
    simp only [execInstrBr, storeAddress, value]
    rfl
  refine ⟨run₁.trans run₂, ?_, ?_, ?_⟩
  · exact (inv.store fits _ rfl).of_mem memory
  · show (execInstrBr loaded _).pc = _
    rw [straight_pc loaded _ rfl, straight_pc state _ rfl, BitVec.add_assoc]
    rfl
  · intro r other
    show (execInstrBr loaded _).getReg r = _
    simp [loaded, execInstrBr, QOpening.getReg_setReg, QOpening.getReg_setMem, Ne.symm other]

/-- A block of `n ≤ m ≤ 4` load/store pairs copies `n` source words to output words `count …`. -/
theorem pair_block (init : MachineState) (source : Nat → Nat) (start m S D count : Nat) (small : m ≤ 4)
    (code : CodeAt start (pairCode m)) (aligned : S % 8 = 0) (low : trapdoorBase ≤ S)
    (high : S+8*m ≤ proofBase) (target : D = proofBase+8*count)
    (fits : proofBase+8*(count+m) ≤ MEMORY_BYTES)
    (named : ∀ w < m, source (count+w) = S+8*w) :
    ∀ n ≤ m, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*start) →
      state.getReg .x7 = BitVec.ofNat 64 S → state.getReg .x21 = BitVec.ofNat 64 D →
      Inv init state source count →
      let after := (pairCode n).foldl execInstrBr state
      Runs state after (2*n) (2*n) ∧ Inv init after source (count+n) ∧
        after.pc = BitVec.ofNat 64 (4096+4*(start+2*n)) ∧
        ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro n
  induction n with
  | zero =>
    intro _ state pc _ _ inv
    exact ⟨Runs.zero state, inv, pc, fun _ _ => rfl⟩
  | succ n ih =>
    intro le state pc from_ to_ inv
    obtain ⟨run, inv', pc', regs⟩ := ih (by omega) state pc from_ to_ inv
    let middle := (pairCode n).foldl execInstrBr state
    have step := pair_step init middle source start m n (count+n) S D small (by omega) code pc'
      ((regs .x7 (by decide)).trans from_) ((regs .x21 (by decide)).trans to_)
      (by omega) aligned low (by omega) (by omega) (named n (by omega)) inv'
    obtain ⟨run₂, inv₂, pc₂, regs₂⟩ := step
    intro after
    have shape : after = execInstrBr (execInstrBr middle (.LD .x31 .x7 (BitVec.ofNat 12 (8*n))))
        (.SD .x21 .x31 (BitVec.ofNat 12 (8*n))) := by
      simp [after, middle, pair_code_succ, List.foldl_append]
    rw [shape]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), by simpa [Nat.add_assoc] using inv₂, ?_, ?_⟩
    · rw [pc₂, pc', show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 1
    · intro r other
      exact (regs₂ r other).trans (regs r other)

set_option maxRecDepth 100000 in
private theorem variant_offset_value : ∀ v < 5, ∀ m < 16,
    signExtend12 (BitVec.ofNat 12 (variantOffset v m)) = BitVec.ofNat 64 (variantOffset v m) := by
  decide

private theorem store_offset_value : ∀ m < 16, signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) := by
  decide

theorem variant_offset_bound (v m : Nat) : variantOffset v m+8 ≤ 160 ∧ variantOffset v m % 8 = 0 := by
  unfold variantOffset
  have := Nat.mod_lt (v+m/4+1) (show 0 < 5 by decide)
  have := Nat.mod_lt m (show 0 < 4 by decide)
  omega

set_option maxRecDepth 100000 in
theorem variant_code_load : ∀ v < 5, ∀ m < 16,
    (variantPairs v 16)[2*m]? = some (.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v m))) := by decide

set_option maxRecDepth 100000 in
theorem variant_code_store : ∀ v < 5, ∀ m < 16,
    (variantPairs v 16)[2*m+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (8*m))) := by decide

theorem variant_pairs_length (v n : Nat) : (variantPairs v n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [variantPairs, List.range_succ, List.flatMap_append] at ih ⊢
    simp [ih]
    omega

theorem variant_pairs_succ (v n : Nat) : variantPairs v (n+1) =
    variantPairs v n ++ [.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v n)), .SD .x21 .x31 (BitVec.ofNat 12 (8*n))] := by
  simp [variantPairs, List.range_succ, List.flatMap_append]

/-- One load/store pair of a copy block: word `count` of the output is the source word `w`. -/
theorem variant_step (init state : MachineState) (source : Nat → Nat) (start v w count S D : Nat)
    (hv : v < 5) (live : w < 16) (code : CodeAt start (variantPairs v 16))
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(start+2*w)))
    (from_ : state.getReg .x30 = BitVec.ofNat 64 S) (to_ : state.getReg .x21 = BitVec.ofNat 64 D)
    (target : D+8*w = proofBase+8*count) (aligned : S % 8 = 0) (low : trapdoorBase ≤ S)
    (high : S+160 ≤ proofBase) (fits : proofBase+8*count+8 ≤ MEMORY_BYTES)
    (named : source count = S+variantOffset v w) (inv : Inv init state source count) :
    let after := execInstrBr (execInstrBr state (.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v w))))
      (.SD .x21 .x31 (BitVec.ofNat 12 (8*w)))
    Runs state after 2 2 ∧ Inv init after source (count+1) ∧ after.pc = state.pc+8 ∧
      ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro after
  have offset := variant_offset_value v hv w live
  have offsetS := store_offset_value w live
  have bound := variant_offset_bound v w
  have room : MEMORY_BYTES < 2^64 := by decide
  have heap : trapdoorBase % 8 = 0 := by decide
  have proofAligned : proofBase % 8 = 0 := by decide
  have below : proofBase ≤ MEMORY_BYTES := by decide
  let loaded := execInstrBr state (.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v w)))
  have loadAddress : state.getReg .x30 + signExtend12 (BitVec.ofNat 12 (variantOffset v w)) =
      BitVec.ofNat 64 (S+variantOffset v w) := by
    rw [from_, offset, ← BitVec.ofNat_add]
  have storeAddress : loaded.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*w)) =
      BitVec.ofNat 64 (proofBase+8*count) := by
    have keep : loaded.getReg .x21 = state.getReg .x21 := by
      simp [loaded, execInstrBr, QOpening.getReg_setReg]
    rw [keep, to_, offsetS, ← BitVec.ofNat_add, target]
  have loadCode : program[start+2*w]? = some (.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v w))) := by
    have := code (2*w) (by rw [variant_pairs_length]; omega)
    rw [this, variant_code_load v hv w live]
  have storeCode : program[start+2*w+1]? = some (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) := by
    have := code (2*w+1) (by rw [variant_pairs_length]; omega)
    rw [Nat.add_assoc, this, variant_code_store v hv w live]
  have loadValid : memoryArgumentsValid state (.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v w))) = true := by
    simp only [memoryArgumentsValid, memAccess, loadAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have storeValid : memoryArgumentsValid loaded (.SD .x21 .x31 (BitVec.ofNat 12 (8*w))) = true := by
    simp only [memoryArgumentsValid, memAccess, storeAddress]
    exact QOpening.aligned_access _ (by omega) (by omega)
  have loadPC : loaded.pc = BitVec.ofNat 64 (4096+4*(start+2*w+1)) :=
    (straight_pc state _ rfl).trans (pc_next _ _ pc)
  have run₁ := runs_one state _ (start+2*w) loadCode pc rfl loadValid
  have run₂ := runs_one loaded _ (start+2*w+1) storeCode loadPC rfl storeValid
  have value : loaded.getReg .x31 = init.getMem (BitVec.ofNat 64 (source count)) := by
    simp only [loaded, execInstrBr, QOpening.getReg_setReg, MachineState.getReg_setPC]
    simp only [loadAddress, ite_true, ne_eq, reduceCtorEq, not_false_eq_true, and_self, named]
    exact inv.input _ (by omega) (by omega)
  have memory : after.mem = (state.setMem (BitVec.ofNat 64 (proofBase+8*count))
      (init.getMem (BitVec.ofNat 64 (source count)))).mem := by
    show (execInstrBr loaded _).mem = _
    simp only [execInstrBr, storeAddress, value]
    rfl
  refine ⟨run₁.trans run₂, ?_, ?_, ?_⟩
  · exact (inv.store fits _ rfl).of_mem memory
  · show (execInstrBr loaded _).pc = _
    rw [straight_pc loaded _ rfl, straight_pc state _ rfl, BitVec.add_assoc]
    rfl
  · intro r other
    show (execInstrBr loaded _).getReg r = _
    simp [loaded, execInstrBr, QOpening.getReg_setReg, QOpening.getReg_setMem, Ne.symm other]

/-- The first `n ≤ 16` load/store pairs of copy variant `v` copy output words `count …`. -/
theorem variant_block (init : MachineState) (source : Nat → Nat) (start v S D count : Nat) (hv : v < 5)
    (code : CodeAt start (variantPairs v 16)) (aligned : S % 8 = 0) (low : trapdoorBase ≤ S)
    (high : S+160 ≤ proofBase) (target : D = proofBase+8*count)
    (fits : proofBase+8*(count+16) ≤ MEMORY_BYTES)
    (named : ∀ m < 16, source (count+m) = S+variantOffset v m) :
    ∀ n ≤ 16, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*start) →
      state.getReg .x30 = BitVec.ofNat 64 S → state.getReg .x21 = BitVec.ofNat 64 D →
      Inv init state source count →
      let after := (variantPairs v n).foldl execInstrBr state
      Runs state after (2*n) (2*n) ∧ Inv init after source (count+n) ∧
        after.pc = BitVec.ofNat 64 (4096+4*(start+2*n)) ∧
        ∀ r, r ≠ .x31 → after.getReg r = state.getReg r := by
  intro n
  induction n with
  | zero =>
    intro _ state pc _ _ inv
    exact ⟨Runs.zero state, inv, pc, fun _ _ => rfl⟩
  | succ n ih =>
    intro le state pc from_ to_ inv
    obtain ⟨run, inv', pc', regs⟩ := ih (by omega) state pc from_ to_ inv
    let middle := (variantPairs v n).foldl execInstrBr state
    have step := variant_step init middle source start v n (count+n) S D hv (by omega) code pc'
      ((regs .x30 (by decide)).trans from_) ((regs .x21 (by decide)).trans to_)
      (by omega) aligned low high (by omega) (named n (by omega)) inv'
    obtain ⟨run₂, inv₂, pc₂, regs₂⟩ := step
    intro after
    have shape : after = execInstrBr (execInstrBr middle (.LD .x31 .x30 (BitVec.ofNat 12 (variantOffset v n))))
        (.SD .x21 .x31 (BitVec.ofNat 12 (8*n))) := by
      simp [after, middle, variant_pairs_succ, List.foldl_append]
    rw [shape]
    refine ⟨(run.trans run₂).cast (by omega) (by omega), by simpa [Nat.add_assoc] using inv₂, ?_, ?_⟩
    · rw [pc₂, pc', show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 1
    · intro r other
      exact (regs₂ r other).trans (regs r other)

end TwoPermutationPrototype.QuadOpening
