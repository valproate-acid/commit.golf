import CommitGolfCandidate.QuadOpeningLevels

/-! Setup, one record (salt + eleven levels + loop latch), all records, and the exit. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (OpeningLayout trapdoorBase proofBase nonceBase indicesBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

@[local simp] private theorem reg_zero (state : MachineState) : state.getReg .x0 = 0#64 := rfl

/-- State at a record boundary: about to start record `o` (or at the exit when `o = card`). -/
structure RecordAt (init state : MachineState) (positions : Positions) (o : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*(if o = positions.card then 148 else 11))
  index : state.getReg .x8 = BitVec.ofNat 64 (indicesBase+8*o)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  left : state.getReg .x18 = BitVec.ofNat 64 (positions.card-o)
  five : state.getReg .x19 = BitVec.ofNat 64 5
  begin : state.getReg .x15 = BitVec.ofNat 64 proofBase
  dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*(178*o))
  salts : state.getReg .x22 = BitVec.ofNat 64 nonceBase
  width : state.getReg .x23 = BitVec.ofNat 64 368
  table : state.getReg .x26 = BitVec.ofNat 64 tableBase
  inv : Inv init state (wordSource positions) (178*o)

theorem card_le (positions : Positions) : positions.card ≤ LENGTH := by
  simpa [Index] using Finset.card_le_univ positions

theorem ordinal_index (positions : Positions) (o : Nat) (present : o < positions.card) :
    ordinalIndex positions o = ((positions.sort (· ≤ ·))[o]'(by simpa using present)).val := by
  unfold ordinalIndex
  rw [List.getElem?_eq_getElem (by simpa using present)]
  rfl

theorem ordinal_index_lt (positions : Positions) (o : Nat) : ordinalIndex positions o < LENGTH := by
  unfold ordinalIndex
  cases h : (positions.sort (· ≤ ·))[o]? with
  | none => simp <;> decide
  | some x => simpa using x.isLt

set_option maxRecDepth 100000 in
theorem record_codes :
    CodeAt 11 [.LD .x6 .x8 0] ∧ CodeAt 12 [.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] ∧ CodeAt 14 (pairCode 2) ∧
    CodeAt 18 [.ADDI .x21 .x21 16] ∧ CodeAt 145 [.ADDI .x8 .x8 8, .ADDI .x18 .x18 4095] ∧
    program[147]? = some (.BNE .x18 .x0 7648) := by
  decide +kernel

theorem set_pc_pc (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl
theorem set_pc_mem (state : MachineState) (pc : Word) : (state.setPC pc).mem = state.mem := rfl

theorem bne_shape (state : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr state (.BNE r₁ r₂ imm) =
      state.setPC (if state.getReg r₁ != state.getReg r₂ then state.pc + signExtend13 imm else state.pc + 4) := by
  simp only [execInstrBr]
  split <;> rfl

theorem decrement (n : Nat) (positive : 1 ≤ n) (small : n < 2^64) :
    BitVec.ofNat 64 n + signExtend12 4095 = BitVec.ofNat 64 (n-1) := by
  rw [show signExtend12 4095 = BitVec.ofNat 64 (2^64-1) by decide, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

private theorem shift_salt (i : Nat) (small : i < 2^40) :
    BitVec.ofNat 64 i <<< (4 : Nat) = BitVec.ofNat 64 (16*i) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show i*2^4 % 2^64 = _
  omega

def recordRun (state : MachineState) : MachineState :=
  execInstrBr ([.ADDI .x8 .x8 8, .ADDI .x18 .x18 4095].foldl execInstrBr
    (levelsRun 11 (([.ADDI .x21 .x21 16] : List Instr).foldl execInstrBr ((pairCode 2).foldl execInstrBr
      (([.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] : List Instr).foldl execInstrBr
        (execInstrBr state (.LD .x6 .x8 0)))))))
    (.BNE .x18 .x0 7648)

theorem record_step (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (state : MachineState) (o : Nat) (present : o < positions.card)
    (at_ : RecordAt (s.initialState .opening (trapdoor, positions)) state positions o) :
    Runs state (recordRun state) 511 571 ∧
      RecordAt (s.initialState .opening (trapdoor, positions)) (recordRun state) positions (o+1) := by
  let init := s.initialState .opening (trapdoor, positions)
  let i := ordinalIndex positions o
  have inside : i < LENGTH := ordinal_index_lt positions o
  have card := card_le positions
  have hL : LENGTH = 16777216 := rfl
  have ordinal : o < LENGTH := by omega
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := record_codes
  have notLast : o ≠ positions.card := by omega
  have pc₀ : state.pc = BitVec.ofNat 64 (4096+4*11) := by simpa [notLast] using at_.pc
  have fitsAll : proofBase+8*(178*(o+1)) ≤ MEMORY_BYTES := by
    have : proofBase = 10804535392 := rfl
    have : MEMORY_BYTES = 68719476736 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  -- load the index
  have indexAddress : state.getReg .x8 + signExtend12 0 = BitVec.ofNat 64 (indicesBase+8*o) := by
    rw [at_.index, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]
  have loaded : state.getMem (BitVec.ofNat 64 (indicesBase+8*o)) = BitVec.ofNat 64 i := by
    have below : indicesBase+8*o < proofBase := by
      have : indicesBase = 6375350304 := rfl
      have : proofBase = 10804535392 := rfl
      have : LENGTH = 16777216 := rfl
      omega
    rw [at_.inv.input _ (by unfold indicesBase; omega) below,
      QOpening.input_index s layout trapdoor positions o present]
    show _ = BitVec.ofNat 64 (ordinalIndex positions o)
    rw [ordinal_index positions o present]
  have loadValid : memoryArgumentsValid state (.LD .x6 .x8 0) = true := by
    simp only [memoryArgumentsValid, memAccess, indexAddress]
    apply QOpening.aligned_access
    · have : indicesBase % 8 = 0 := by decide
      omega
    · have : indicesBase = 6375350304 := rfl
      have : LENGTH = 16777216 := rfl
      have : MEMORY_BYTES = 68719476736 := rfl
      omega
  have run₀ := runs_one state (.LD .x6 .x8 0) 11 (by simpa using c₁ 0 (by simp)) pc₀ rfl loadValid
  let s₀ := execInstrBr state (.LD .x6 .x8 0)
  have node₀ : s₀.getReg .x6 = BitVec.ofNat 64 i := by
    have e : s₀.getReg .x6 = state.getMem (state.getReg .x8 + signExtend12 0) := by simp [s₀, execInstrBr]
    rw [e, indexAddress, loaded]
  have keep₀ (r : Reg) (a : r ≠ .x6) : s₀.getReg r = state.getReg r := by simp [s₀, execInstrBr, Ne.symm a]
  have mem₀ : s₀.mem = state.mem := mem_set_reg _ _ _
  have pc₀' : s₀.pc = BitVec.ofNat 64 (4096+4*12) := (straight_pc state _ rfl).trans (pc_next _ _ pc₀)
  -- salt address
  let s₁ := ([.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] : List Instr).foldl execInstrBr s₀
  have pure₁ : ([.SLLI .x7 .x6 4, .ADD .x7 .x22 .x7] : List Instr).all pureOp = true := rfl
  have run₁ := runs_pure _ 12 s₀ c₂ pc₀' pure₁
  have source₁ : s₁.getReg .x7 = BitVec.ofNat 64 (nonceBase+16*i) := by
    simp [s₁, execInstrBr, node₀, keep₀ .x22 (by decide), at_.salts]
    rw [shift_salt i (by have : i < 2^24 := inside; omega), ← BitVec.ofNat_add]
  have keep₁ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) : s₁.getReg r = state.getReg r := by
    simp [s₁, execInstrBr, Ne.symm b]
    exact keep₀ r a
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*14) := by
    rw [pure_pc _ _ pure₁, pc₀', pc_offset]
    rfl
  have inv₁ : Inv init s₁ (wordSource positions) (178*o) := (at_.inv.of_mem (pure_mem _ _ pure₁)).of_mem mem₀
  -- salt copy
  have nonceAligned : (nonceBase+16*i) % 8 = 0 := by
    have : nonceBase % 8 = 0 := by decide
    omega
  have nonceRange : nonceBase+16*i+16 ≤ proofBase := by
    have : nonceBase = 4294971424 + 1811943424 := rfl
    have : proofBase = 10804535392 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  have block := pair_block init (wordSource positions) 14 2 (nonceBase+16*i) (proofBase+8*(178*o)) (178*o)
    (by decide) c₃ nonceAligned (by unfold nonceBase; omega) (by omega) rfl (by omega)
    (fun w hw => word_source_salt positions o w hw) 2 le_rfl s₁ pc₁ source₁
    ((keep₁ .x21 (by decide) (by decide)).trans at_.dest) inv₁
  obtain ⟨run₂, inv₂, pc₂, regs₂⟩ := block
  let s₂ := (pairCode 2).foldl execInstrBr s₁
  have pure₃ : ([.ADDI .x21 .x21 16] : List Instr).all pureOp = true := rfl
  have run₃ := runs_pure _ 18 s₂ c₄ pc₂ pure₃
  let s₃ := ([.ADDI .x21 .x21 16] : List Instr).foldl execInstrBr s₂
  have keep₃ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x21) (d : r ≠ .x31) :
      s₃.getReg r = state.getReg r := by
    simp [s₃, execInstrBr, Ne.symm c]
    rw [regs₂ r d, keep₁ r a b]
  have level₀ : LevelAt init s₃ positions o 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pure_pc _ _ pure₃, pc₂, pc_offset]; rfl
    · simp [s₃, execInstrBr]
      rw [regs₂ .x6 (by decide)]
      simpa [s₁, execInstrBr] using node₀
    · simp [s₃, execInstrBr, signExtend12]
      rw [regs₂ .x21 (by decide), keep₁ .x21 (by decide) (by decide), at_.dest, ← BitVec.ofNat_add]
      unfold levelWord
      congr 1
    · exact (keep₃ .x9 (by decide) (by decide) (by decide) (by decide)).trans at_.heap
    · exact (keep₃ .x19 (by decide) (by decide) (by decide) (by decide)).trans at_.five
    · exact (keep₃ .x23 (by decide) (by decide) (by decide) (by decide)).trans at_.width
    · exact (keep₃ .x26 (by decide) (by decide) (by decide) (by decide)).trans at_.table
    · exact (inv₂.of_mem (pure_mem _ _ pure₃)).cast_count (by unfold levelWord; omega)
  -- the eleven levels
  obtain ⟨run₄, level₁₁, regs₄⟩ := levels_run init positions o inside ordinal s₃ level₀ 11 le_rfl
  let s₄ := levelsRun 11 s₃
  have keep₄ (r : Reg) (z : r ≠ .x1) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x11) (e : r ≠ .x21)
      (f : r ≠ .x24) (g : r ≠ .x25) (h : r ≠ .x30) (l : r ≠ .x31) : s₄.getReg r = state.getReg r :=
    (regs₄ r z a b c d e f g h l).trans (keep₃ r a b e l)
  -- loop latch
  have pure₅ : ([.ADDI .x8 .x8 8, .ADDI .x18 .x18 4095] : List Instr).all pureOp = true := rfl
  have run₅ := runs_pure _ 145 s₄ c₅ level₁₁.pc pure₅
  let s₅ := ([.ADDI .x8 .x8 8, .ADDI .x18 .x18 4095] : List Instr).foldl execInstrBr s₄
  have keep₅ (r : Reg) (z : r ≠ .x1) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x11) (e : r ≠ .x21)
      (f : r ≠ .x24) (g : r ≠ .x25) (h : r ≠ .x30) (l : r ≠ .x31) (m : r ≠ .x8) (n : r ≠ .x18) :
      s₅.getReg r = state.getReg r := by
    simp [s₅, execInstrBr, Ne.symm m, Ne.symm n]
    exact keep₄ r z a b c d e f g h l
  have left₅ : s₅.getReg .x18 = BitVec.ofNat 64 (positions.card-(o+1)) := by
    have h : s₅.getReg .x18 = s₄.getReg .x18 + signExtend12 4095 := by simp [s₅, execInstrBr]
    rw [h, keep₄ .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), at_.left, decrement _ (by omega) (by omega)]
    congr 1
  have pc₅ : s₅.pc = BitVec.ofNat 64 (4096+4*147) := by
    rw [pure_pc _ _ pure₅, level₁₁.pc, pc_offset]; rfl
  have branchStep : ordinaryStep s₅ (.base (.BNE .x18 .x0 7648)) = some (execInstrBr s₅ (.BNE .x18 .x0 7648)) := rfl
  have run₆ : Runs s₅ (recordRun state) 1 1 := by
    intro fuel coins
    rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program s₅ 147 _ c₆ pc₅) branchStep]
    rfl
  have shape : recordRun state = s₅.setPC
      (if s₅.getReg .x18 != s₅.getReg .x0 then s₅.pc + signExtend13 7648 else s₅.pc + 4) := bne_shape _ _ _ _
  have keep (r : Reg) (z : r ≠ .x1) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x10) (d : r ≠ .x11) (e : r ≠ .x21)
      (f : r ≠ .x24) (g : r ≠ .x25) (h : r ≠ .x30) (l : r ≠ .x31) (m : r ≠ .x8) (n : r ≠ .x18) :
      (recordRun state).getReg r = state.getReg r := by
    rw [shape, MachineState.getReg_setPC]
    exact keep₅ r z a b c d e f g h l m n
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (run₀.trans (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆)))))).cast
      (by simp) (by simp [cost, instructionCycles])
  · rw [shape, set_pc_pc]
    have limit : positions.card-(o+1) < 2^64 := by omega
    rw [pc₅, left₅, reg_zero]
    by_cases last : o+1 = positions.card
    · rw [show positions.card-(o+1) = 0 by omega, if_pos last]
      decide
    · have nonzero : BitVec.ofNat 64 (positions.card-(o+1)) ≠ 0#64 := by
        intro same
        have := QOpening.nat_address_injective limit (by decide) same
        omega
      rw [if_neg last]
      simp [nonzero]
      decide
  · rw [shape, MachineState.getReg_setPC]
    have h : s₅.getReg .x8 = s₄.getReg .x8 + signExtend12 8 := by simp [s₅, execInstrBr]
    rw [h, keep₄ .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), at_.index, show signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 by decide,
      ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · exact (keep .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans at_.heap
  · rw [shape, MachineState.getReg_setPC]
    exact left₅
  · exact (keep .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans at_.five
  · exact (keep .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans at_.begin
  · rw [shape, MachineState.getReg_setPC]
    have h : s₅.getReg .x21 = s₄.getReg .x21 := by simp [s₅, execInstrBr]
    rw [h, level₁₁.dest]
    unfold levelWord
    congr 2
  · exact (keep .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans at_.salts
  · exact (keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans at_.width
  · exact (keep .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans at_.table
  · have mem₆ : (recordRun state).mem = s₄.mem :=
      (congrArg MachineState.mem shape).trans ((set_pc_mem _ _).trans (pure_mem _ _ pure₅))
    exact (level₁₁.inv.of_mem mem₆).cast_count (by unfold levelWord; omega)

/-- `n` records from `state`. -/
def recordsRun (n : Nat) (state : MachineState) : MachineState := recordRun^[n] state

theorem records_run_zero (state : MachineState) : recordsRun 0 state = state :=
  Function.iterate_zero_apply recordRun state

theorem records_run_succ (n : Nat) (state : MachineState) :
    recordsRun (n+1) state = recordsRun n (recordRun state) :=
  Function.iterate_succ_apply recordRun n state

theorem records_run (s : Submission) (layout : OpeningLayout s) (trapdoor : BitVec (8*s.sizes.trapdoor))
    (positions : Positions) (n : Nat) :
    ∀ o (state : MachineState), o+n = positions.card →
      RecordAt (s.initialState .opening (trapdoor, positions)) state positions o →
      Runs state (recordsRun n state) (511*n) (571*n) ∧
        RecordAt (s.initialState .opening (trapdoor, positions)) (recordsRun n state) positions positions.card := by
  induction n with
  | zero =>
    intro o state total at_
    rw [records_run_zero]
    refine ⟨Runs.zero state, ?_⟩
    rw [← total]
    exact at_
  | succ n ih =>
    intro o state total at_
    obtain ⟨run, at'⟩ := record_step s layout trapdoor positions state o (by omega) at_
    obtain ⟨run₂, at₂⟩ := ih (o+1) (recordRun state) (by omega) at'
    rw [records_run_succ]
    exact ⟨(run.trans run₂).cast (by ring) (by ring), at₂⟩

end TwoPermutationPrototype.QuadOpening
