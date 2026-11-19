import CommitGolfCandidate.QuadOpeningRun

/-! One level of a penta record: `x6 = index / 5^k` gives the group base of the four other
children in the trapdoor; they are appended to the output as 16 doublewords. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Record layout -/

/-- Level-`k` node index of the `j`-th other child (Nat version of `pentaNeighbour`). -/
def neighbourNat (i k j : Nat) : Nat := 5*(i/5^(k+1)) + (i/5^k%5+j+1)%5

theorem neighbour_nat (index : Index) (k j : Nat) : pentaNeighbour index k j = neighbourNat index.val k j := rfl

/-- Initial address of doubleword `d < 178` of the record of position `i`. -/
def recordSource (i d : Nat) : Nat :=
  if d < 2 then nonceBase+16*i+8*d
  else trapdoorBase+pentaSlotOffset ((d-2)/16) (neighbourNat i ((d-2)/16) ((d-2)%16/4))+8*((d-2)%4)

/-- The position written by record `o` (0 past the end). -/
def ordinalIndex (positions : Positions) (o : Nat) : Nat :=
  (((positions.sort (· ≤ ·))[o]?).map Fin.val).getD 0

def wordSource (positions : Positions) (u : Nat) : Nat := recordSource (ordinalIndex positions (u/178)) (u%178)

theorem word_source_level (positions : Positions) (o k j w : Nat) (hk : k < 11) (hj : j < 4) (hw : w < 4) :
    wordSource positions (178*o+2+16*k+4*j+w) =
      trapdoorBase+pentaSlotOffset k (neighbourNat (ordinalIndex positions o) k j)+8*w := by
  unfold wordSource recordSource
  have q : (178*o+2+16*k+4*j+w)/178 = o := by omega
  have r : (178*o+2+16*k+4*j+w)%178 = 2+16*k+4*j+w := by omega
  rw [q, r, if_neg (by omega)]
  have a : (2+16*k+4*j+w-2)/16 = k := by omega
  have b : (2+16*k+4*j+w-2)%16/4 = j := by omega
  have c : (2+16*k+4*j+w-2)%4 = w := by omega
  rw [a, b, c]

theorem word_source_salt (positions : Positions) (o w : Nat) (hw : w < 2) :
    wordSource positions (178*o+w) = nonceBase+16*ordinalIndex positions o+8*w := by
  unfold wordSource recordSource
  have q : (178*o+w)/178 = o := by omega
  have r : (178*o+w)%178 = w := by omega
  rw [q, r, if_pos hw]

theorem div_lt_count (i : Nat) (inside : i < LENGTH) : ∀ k, i/5^k < pentaCount k
  | 0 => by simpa [pentaCount] using inside
  | k+1 => by
    have ih := div_lt_count i inside k
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    show i/5^k/5 < (pentaCount k+4)/5
    omega

theorem group_room : ∀ k < 11, pentaGroupBase k+368*pentaCount (k+1) ≤ 1543577600 := by decide
private theorem group_aligned : ∀ k < 11, (pentaGroupBase k+40) % 8 = 0 := by decide

theorem neighbour_source (i k j : Nat) (inside : i < LENGTH) (hk : k < 11) (hj : j < 4) :
    trapdoorBase+pentaSlotOffset k (neighbourNat i k j) =
      trapdoorBase+pentaGroupBase k+40+368*(i/5^k/5)+32*((i/5^k%5+j+1)%5) ∧
    (trapdoorBase+pentaSlotOffset k (neighbourNat i k j)) % 8 = 0 ∧
    trapdoorBase+pentaSlotOffset k (neighbourNat i k j)+32 ≤ proofBase ∧
    pentaSlotOffset k (neighbourNat i k j)+32 ≤ 1543577600 := by
  have split : i/5^(k+1) = i/5^k/5 := by rw [pow_succ, Nat.div_div_eq_div_mul]
  have count := div_lt_count i inside (k+1)
  rw [split] at count
  have room := group_room k hk
  have aligned := group_aligned k hk
  have slot := Nat.mod_lt (i/5^k%5+j+1) (show 0 < 5 by decide)
  have heap : trapdoorBase = 4294971424 := rfl
  have proof : proofBase = 10804535392 := rfl
  unfold pentaSlotOffset neighbourNat
  rw [split]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-! ### Register arithmetic -/

theorem word_lt (n : Nat) (small : n < 2^64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem divu_five (n : Nat) (small : n < 2^40) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (n/5) := by
  unfold rv64_divu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, word_lt n (by omega), word_lt 5 (by decide), word_lt _ (by omega)]

theorem remu_five (n : Nat) (small : n < 2^40) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (n%5) := by
  unfold rv64_remu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, word_lt n (by omega), word_lt 5 (by decide), word_lt _ (by omega)]

theorem rem_by_shift (n : Nat) (small : n < 2^40) :
    BitVec.ofNat 64 n - ((BitVec.ofNat 64 (n/5) <<< 2) + BitVec.ofNat 64 (n/5)) = BitVec.ofNat 64 (n%5) := by
  apply BitVec.eq_of_toNat_eq
  have five : (BitVec.ofNat 64 (n/5) <<< 2) + BitVec.ofNat 64 (n/5) = BitVec.ofNat 64 (5*(n/5)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
    omega
  rw [five, BitVec.toNat_sub, word_lt _ (by omega), word_lt _ (by omega), word_lt _ (by omega)]
  omega

theorem mul_width (q : Nat) (small : q < 2^40) :
    BitVec.ofNat 64 q * BitVec.ofNat 64 368 = BitVec.ofNat 64 (368*q) := by
  rw [← BitVec.ofNat_mul]
  congr 1
  omega

theorem lui_page : ∀ k < 11,
    ((BitVec.ofNat 20 (groupPage k)).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (pentaGroupBase k+40) := by
  decide

theorem shift_slot (m : Nat) (small : m < 2^40) : BitVec.ofNat 64 m <<< (5 : Nat) = BitVec.ofNat 64 (32*m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show m*2^5 % 2^64 = _
  omega

theorem addi_small : ∀ j < 4, signExtend12 (BitVec.ofNat 12 (j+1)) = BitVec.ofNat 64 (j+1) := by decide

/-! ### Level head -/

theorem level_head_post (state : MachineState) (k n : Nat) (hk : k < 11) (small : n < 2^30) (top : k = 10 → n < 5)
    (node : state.getReg .x6 = BitVec.ofNat 64 n) (five : state.getReg .x19 = BitVec.ofNat 64 5)
    (width : state.getReg .x23 = BitVec.ofNat 64 368) (heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase) :
    let after := (levelHead k).foldl execInstrBr state
    after.getReg .x24 = (if k = 10 then state.getReg .x24 else BitVec.ofNat 64 (n/5)) ∧ after.getReg .x25 = BitVec.ofNat 64 (n%5) ∧
      after.getReg .x30 = BitVec.ofNat 64 (trapdoorBase+pentaGroupBase k+40+368*(n/5)) ∧
      ∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x24 → r ≠ .x25 → r ≠ .x30 → after.getReg r = state.getReg r := by
  intro after
  by_cases last : k = 10
  · have smallTop := top last
    have q : n/5 = 0 := Nat.div_eq_of_lt smallTop
    have rem : n%5 = n := Nat.mod_eq_of_lt smallTop
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [after, levelHead, last, execInstrBr]
    · simp [after, levelHead, last, execInstrBr, node, rem, signExtend12]
    · simp [after, levelHead, last, execInstrBr, heap, lui_page 10 (by decide), q]
      rw [← BitVec.ofNat_add]
      congr 1
    · intro r a b c d e
      simp [after, levelHead, last, execInstrBr, Ne.symm b, Ne.symm d, Ne.symm e]
  · have quotient := divu_five n (by omega)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [after, levelHead, last, execInstrBr, node, five, quotient]
    · simp [after, levelHead, last, execInstrBr, node, five, quotient]
      exact rem_by_shift n (by omega)
    · simp [after, levelHead, last, execInstrBr, node, five, quotient, width, heap, lui_page k hk]
      rw [mul_width _ (by omega), ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega
    · intro r a b c d e
      simp [after, levelHead, last, execInstrBr, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e]

/-! ### One level -/

def levelStart (k : Nat) : Nat := if k = 11 then 145 else 19+12*k

def levelSteps (k : Nat) : Nat := if k = 10 then 40 else 46
def levelCycles (k : Nat) : Nat := if k = 10 then 40 else 52

/-- Word index of copy variant `v`; `x26` holds the address of variant 0. -/
def variantStart (v : Nat) : Nat := 159+64*v

def tableBase : Nat := 4096+4*159

/-- Output doubleword index at which level `k` of record `o` starts. -/
def levelWord (o k : Nat) : Nat := 178*o+2+16*k

set_option maxRecDepth 100000 in
theorem level_codes : ∀ k < 11, CodeAt (levelStart k) (levelHead k) ∧ CodeAt (levelStart k+(levelHead k).length) dispatchCode ∧
    program[levelStart k+(levelHead k).length+2]? = some (.JALR .x1 .x7 0) ∧
    CodeAt (levelStart k+(levelHead k).length+3) (finalCode k) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem variant_codes : ∀ v < 5, CodeAt (variantStart v) (variantPairs v 16) ∧
    CodeAt (variantStart v+32) [.ADDI .x21 .x21 128] ∧ program[variantStart v+33]? = some (.JALR .x0 .x1 0) := by
  decide +kernel

theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem dispatch_target : ∀ r < 5,
    (BitVec.ofNat 64 r <<< (8 : Nat) + BitVec.ofNat 64 tableBase + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*variantStart r) := by decide

theorem return_target : ∀ k < 11,
    (BitVec.ofNat 64 (4096+4*(levelStart k+(levelHead k).length+2)) + 4 + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096+4*(levelStart k+(levelHead k).length+3)) := by decide

/-- One jump-and-link step. -/
theorem runs_jalr (state : MachineState) (rd rs : Reg) (index : Nat)
    (code : program[index]? = some (.JALR rd rs 0)) (pc : state.pc = BitVec.ofNat 64 (4096+4*index)) :
    Runs state (execInstrBr state (.JALR rd rs 0)) 1 1 := by
  intro fuel coins
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (fetch_program state index _ code pc) rfl]
  rfl

theorem jalr_post (state : MachineState) (rd rs : Reg) :
    (execInstrBr state (.JALR rd rs 0)).pc = (state.getReg rs + signExtend12 0) &&& ~~~1#64 ∧
    (execInstrBr state (.JALR rd rs 0)).mem = state.mem ∧
    (rd ≠ .x0 → (execInstrBr state (.JALR rd rs 0)).getReg rd = state.pc + 4) ∧
    ∀ r, r ≠ rd → (execInstrBr state (.JALR rd rs 0)).getReg r = state.getReg r := by
  refine ⟨rfl, mem_set_reg _ _ _, ?_, ?_⟩
  · intro nonzero
    simp [execInstrBr, nonzero]
  · intro r other
    simp [execInstrBr, Ne.symm other]

structure LevelAt (init state : MachineState) (positions : Positions) (o k : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*levelStart k)
  -- The final quotient is dead; retain the level-10 node after returning.
  node : state.getReg .x6 = BitVec.ofNat 64 (ordinalIndex positions o / 5^(min k 10))
  dest : state.getReg .x21 = BitVec.ofNat 64 (proofBase+8*levelWord o k)
  heap : state.getReg .x9 = BitVec.ofNat 64 trapdoorBase
  five : state.getReg .x19 = BitVec.ofNat 64 5
  width : state.getReg .x23 = BitVec.ofNat 64 368
  table : state.getReg .x26 = BitVec.ofNat 64 tableBase
  inv : Inv init state (wordSource positions) (levelWord o k)

/-- One level: head, dispatch into variant `x25`, copy, return, `x6 := x24`. -/
def levelRun (k : Nat) (state : MachineState) : MachineState :=
  let s₁ := (levelHead k ++ dispatchCode).foldl execInstrBr state
  let s₂ := execInstrBr s₁ (.JALR .x1 .x7 0)
  let s₃ := (variantPairs (s₁.getReg .x25).toNat 16).foldl execInstrBr s₂
  let s₄ := ([.ADDI .x21 .x21 128] : List Instr).foldl execInstrBr s₃
  (finalCode k).foldl execInstrBr (execInstrBr s₄ (.JALR .x0 .x1 0))

theorem level_step (init state : MachineState) (positions : Positions) (o k : Nat) (hk : k < 11)
    (inside : ordinalIndex positions o < LENGTH) (ordinal : o < LENGTH)
    (at_ : LevelAt init state positions o k) :
    Runs state (levelRun k state) (levelSteps k) (levelCycles k) ∧ LevelAt init (levelRun k state) positions o (k+1) ∧
      ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x21 → r ≠ .x24 → r ≠ .x25 →
        r ≠ .x30 → r ≠ .x31 → (levelRun k state).getReg r = state.getReg r := by
  let i := ordinalIndex positions o
  let n := i/5^k
  let rr := n%5
  let G := trapdoorBase+pentaGroupBase k+40+368*(n/5)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := level_codes k hk
  have hr : rr < 5 := Nat.mod_lt _ (by decide)
  obtain ⟨v₁, v₂, v₃⟩ := variant_codes rr hr
  have small : n < 2^30 := by
    have := Nat.div_le_self i (5^k); have : i < 2^24 := inside; omega
  -- head
  let s₀ := (levelHead k).foldl execInstrBr state
  have headPure : (levelHead k).all pureOp = true := by
    by_cases last : k = 10 <;> simp [levelHead, last, pureOp]
  have run₀ := runs_pure _ _ state c₁ at_.pc headPure
  have top : k = 10 → n < 5 := by
    intro last
    subst k
    have count := div_lt_count i inside 10
    have : pentaCount 10 = 2 := by decide
    omega
  have node : state.getReg .x6 = BitVec.ofNat 64 n := by
    simpa [n, i, Nat.min_eq_left (by omega : k ≤ 10)] using at_.node
  have post₀ := level_head_post state k n hk small top node at_.five at_.width at_.heap
  have pc₀ : s₀.pc = BitVec.ofNat 64 (4096+4*(levelStart k+(levelHead k).length)) := by
    rw [pure_pc _ _ headPure, at_.pc, pc_offset]
  have keep₀ (r : Reg) (a : r ≠ .x10) (b : r ≠ .x11) (c : r ≠ .x24) (d : r ≠ .x25) (e : r ≠ .x30) :
      s₀.getReg r = state.getReg r := post₀.2.2.2 r a b c d e
  -- dispatch address
  let s₁ := dispatchCode.foldl execInstrBr s₀
  have dispatchPure : dispatchCode.all pureOp = true := rfl
  have run₁ := runs_pure _ _ s₀ c₂ pc₀ dispatchPure
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(levelStart k+(levelHead k).length+2)) := by
    rw [pure_pc _ _ dispatchPure, pc₀, pc_offset]
    rfl
  have keep₁ (r : Reg) (a : r ≠ .x7) : s₁.getReg r = s₀.getReg r := by
    simp [s₁, dispatchCode, execInstrBr, Ne.symm a]
  have x7₁ : s₁.getReg .x7 = BitVec.ofNat 64 rr <<< (8 : Nat) + BitVec.ofNat 64 tableBase := by
    simp [s₁, dispatchCode, execInstrBr]
    rw [post₀.2.1, keep₀ .x26 (by decide) (by decide) (by decide) (by decide) (by decide), at_.table]
  have x25₁ : s₁.getReg .x25 = BitVec.ofNat 64 rr := (keep₁ .x25 (by decide)).trans post₀.2.1
  have split₁ : (levelHead k ++ dispatchCode).foldl execInstrBr state = s₁ := by
    simp only [s₁, s₀, List.foldl_append]
  -- jump into the variant
  let s₂ := execInstrBr s₁ (.JALR .x1 .x7 0)
  have run₂ := runs_jalr s₁ .x1 .x7 _ c₃ pc₁
  obtain ⟨jpc₂, jmem₂, jlink₂, jkeep₂⟩ := jalr_post s₁ .x1 .x7
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*variantStart rr) := by
    rw [jpc₂, x7₁]
    exact dispatch_target rr hr
  have link₂ : s₂.getReg .x1 = BitVec.ofNat 64 (4096+4*(levelStart k+(levelHead k).length+2)) + 4 := by
    rw [jlink₂ (by decide), pc₁]
  have keep₂ (r : Reg) (a : r ≠ .x1) (b : r ≠ .x7) : s₂.getReg r = s₀.getReg r :=
    (jkeep₂ r a).trans (keep₁ r b)
  -- the copy
  have source (m : Nat) (hm : m < 16) :
      wordSource positions (levelWord o k+m) = G+variantOffset rr m := by
    have level := word_source_level positions o k (m/4) (m%4) hk (by omega) (Nat.mod_lt _ (by decide))
    have neighbour := (neighbour_source i k (m/4) inside hk (by omega)).1
    unfold levelWord
    rw [show 178*o+2+16*k+m = 178*o+2+16*k+4*(m/4)+m%4 by omega, level, neighbour]
    unfold variantOffset
    simp only [G, rr, n]
    omega
  have bounds := neighbour_source i k 3 inside hk (by decide)
  have Galigned : G % 8 = 0 := by
    have := (neighbour_source i k 0 inside hk (by decide)).2.1
    rw [(neighbour_source i k 0 inside hk (by decide)).1] at this
    simp only [G, n]
    omega
  have Ghigh : G+160 ≤ proofBase := by
    have count := div_lt_count i inside (k+1)
    have room := group_room k hk
    have split : i/5^(k+1) = i/5^k/5 := by rw [pow_succ, Nat.div_div_eq_div_mul]
    have : trapdoorBase = 4294971424 := rfl
    have : proofBase = 10804535392 := rfl
    simp only [G, n]
    rw [split] at count
    omega
  have fitsAll : proofBase+8*(178*(o+1)) ≤ MEMORY_BYTES := by
    have : proofBase = 10804535392 := rfl
    have : MEMORY_BYTES = 68719476736 := rfl
    have : LENGTH = 16777216 := rfl
    omega
  have x30₂ : s₂.getReg .x30 = BitVec.ofNat 64 G := (keep₂ .x30 (by decide) (by decide)).trans post₀.2.2.1
  have x21₂ : s₂.getReg .x21 = BitVec.ofNat 64 (proofBase+8*levelWord o k) :=
    (keep₂ .x21 (by decide) (by decide)).trans
      ((keep₀ .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans at_.dest)
  have inv₂ : Inv init s₂ (wordSource positions) (levelWord o k) := by
    refine (at_.inv.of_mem (pure_mem _ _ headPure)).of_mem ?_
    rw [jmem₂]
    exact pure_mem _ _ dispatchPure
  obtain ⟨run₃, inv₃, pc₃, regs₃⟩ := variant_block init (wordSource positions) (variantStart rr) rr G
    (proofBase+8*levelWord o k) (levelWord o k) hr v₁ Galigned (by have : trapdoorBase = 4294971424 := rfl; omega)
    Ghigh rfl (by unfold levelWord; omega) source 16 le_rfl s₂ pc₂ x30₂ x21₂ inv₂
  let s₃ := (variantPairs rr 16).foldl execInstrBr s₂
  -- advance the cursor and return
  have tailPure : ([.ADDI .x21 .x21 128] : List Instr).all pureOp = true := rfl
  have run₄ := runs_pure _ _ s₃ v₂ pc₃ tailPure
  let s₄ := ([.ADDI .x21 .x21 128] : List Instr).foldl execInstrBr s₃
  have pc₄ : s₄.pc = BitVec.ofNat 64 (4096+4*(variantStart rr+33)) := by
    rw [pure_pc _ _ tailPure, pc₃, pc_offset]
    rfl
  have keep₄ (r : Reg) (a : r ≠ .x21) (b : r ≠ .x31) : s₄.getReg r = s₂.getReg r := by
    simp [s₄, execInstrBr, Ne.symm a]
    exact regs₃ r b
  have x21₄ : s₄.getReg .x21 = BitVec.ofNat 64 (proofBase+8*levelWord o (k+1)) := by
    simp [s₄, execInstrBr, signExtend12]
    rw [regs₃ .x21 (by decide), x21₂, ← BitVec.ofNat_add]
    unfold levelWord
    congr 1
  have run₅ := runs_jalr s₄ .x0 .x1 _ v₃ pc₄
  let s₅ := execInstrBr s₄ (.JALR .x0 .x1 0)
  obtain ⟨jpc₅, jmem₅, _, _⟩ := jalr_post s₄ .x0 .x1
  have keep₅ (r : Reg) : s₅.getReg r = s₄.getReg r := by
    simp [s₅, execInstrBr]
  have pc₅ : s₅.pc = BitVec.ofNat 64 (4096+4*(levelStart k+(levelHead k).length+3)) := by
    rw [jpc₅, keep₄ .x1 (by decide) (by decide), link₂]
    exact return_target k hk
  have finalPure : (finalCode k).all pureOp = true := by
    by_cases last : k = 10 <;> simp [finalCode, last, pureOp]
  have run₆ := runs_pure _ _ s₅ c₄ pc₅ finalPure
  have shape : levelRun k state = (finalCode k).foldl execInstrBr s₅ := by
    simp only [levelRun, split₁, x25₁, word_lt rr (by omega)]
    rfl
  have keep (r : Reg) (a : r ≠ .x1) (b : r ≠ .x6) (c : r ≠ .x7) (d : r ≠ .x10) (e : r ≠ .x11)
      (f : r ≠ .x21) (g : r ≠ .x24) (h : r ≠ .x25) (l : r ≠ .x30) (m : r ≠ .x31) :
      (levelRun k state).getReg r = state.getReg r := by
    rw [shape]
    by_cases last : k = 10 <;> simp [finalCode, last, execInstrBr, Ne.symm b] <;>
      rw [keep₅, keep₄ r f m, keep₂ r a c, keep₀ r d e g h l]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, keep⟩
  · rw [shape]
    exact (run₀.trans (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆)))))).cast
      (by by_cases last : k = 10 <;> simp [levelSteps, levelHead, dispatchCode, finalCode, last])
      (by by_cases last : k = 10 <;> simp [levelCycles, cost, levelHead, dispatchCode, finalCode, last, instructionCycles])
  · rw [shape, pure_pc _ _ finalPure, pc₅, pc_offset]
    have offsets : ∀ j < 11, levelStart j+(levelHead j).length+3+(finalCode j).length = levelStart (j+1) := by decide
    rw [offsets k hk]
  · rw [shape]
    by_cases last : k = 10
    · simp only [finalCode, if_pos last, List.foldl_nil]
      rw [keep₅, keep₄ .x6 (by decide) (by decide), keep₂ .x6 (by decide) (by decide),
        keep₀ .x6 (by decide) (by decide) (by decide) (by decide) (by decide), node]
      simp [n, i, last]
    · simp [finalCode, last, execInstrBr, signExtend12]
      rw [keep₅, keep₄ .x24 (by decide) (by decide), keep₂ .x24 (by decide) (by decide), post₀.1, if_neg last]
      have next : min (k+1) 10 = k+1 := Nat.min_eq_left (by omega)
      rw [next]
      congr 1
      rw [pow_succ, Nat.div_div_eq_div_mul]
  · rw [shape]
    by_cases last : k = 10 <;> simp [finalCode, last, execInstrBr] <;> rw [keep₅] <;>
      simpa [last] using x21₄
  · exact (keep .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans at_.heap
  · exact (keep .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans at_.five
  · exact (keep .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans at_.width
  · exact (keep .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans at_.table
  · rw [shape]
    have mem : ((finalCode k).foldl execInstrBr s₅).mem = s₃.mem := by
      rw [pure_mem _ _ finalPure, show s₅.mem = s₄.mem from jmem₅, pure_mem _ _ tailPure]
    exact (inv₃.of_mem mem).cast_count (by unfold levelWord; omega)

end TwoPermutationPrototype.QuadOpening
