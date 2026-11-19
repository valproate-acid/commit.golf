import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.QuadCommitImage

/-! Word addresses and the non-overlap obligations for the penta commit trace.
These facts account for the complete 200-byte writes of every leaf and node. -/
namespace TwoPermutationPrototype.Quad.Commit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling

/-- Word offset (from the trapdoor word 536871428) of the level-`k` group region. -/
def pentaBaseWord : Nat → Nat
  | 0 => 507 | 1 => 154351611 | 2 => 185222651 | 3 => 191397371 | 4 => 192632827
  | 5 => 192880635 | 6 => 192930811 | 7 => 192941563 | 8 => 192944123 | 9 => 192945147
  | 10 => 192946171 | _ => 192947195

/-- Absolute memory word addresses; the common trapdoor starts at word 536871428. -/
def pentaGroupWord (k g : Nat) : Nat := 536871428 + pentaBaseWord k + 46*g
def pentaSlotWord (k j : Nat) : Nat := pentaGroupWord k (j/5) + 5 + 4*(j%5)
def groupWord (g : Nat) : Nat := 536871935 + 46*g
def leafWord (i : Nat) : Nat := groupWord (i/5) + 5 + 4*(i%5)
def saltWord (i : Nat) : Nat := 536871428 + 226492928 + 2*i
def heapWord (k : Nat) : Nat := 536871428 + 4*k
/-- Centered output window: reset after every 45 leaves (9 groups). -/
def windowWord (body pos : Nat) : Nat := leafWord (4095*body + 45*(pos/45)) + 192

private theorem penta_base_table : ∀ k : Fin 12, 8 * pentaBaseWord k.val = pentaGroupBase k.val ∧
    507 ≤ pentaBaseWord k.val := by decide

theorem penta_base_word (k : Nat) (bound : k ≤ 11) : 8 * pentaBaseWord k = pentaGroupBase k :=
  (penta_base_table ⟨k,by omega⟩).1

theorem group_word_level (g : Nat) : groupWord g = pentaGroupWord 0 g := by
  change 536871935 + 46*g = 536871428 + 507 + 46*g
  omega

theorem leaf_word_level (i : Nat) : leafWord i = pentaSlotWord 0 i := by
  unfold leafWord pentaSlotWord
  rw [group_word_level]

theorem penta_slot_byte_address (k j : Nat) (bound : k ≤ 11) :
    8 * pentaSlotWord k j = 4294971424 + pentaSlotOffset k j := by
  unfold pentaSlotWord pentaGroupWord pentaSlotOffset
  have := penta_base_word k bound
  omega

theorem leaf_byte_address (i : Nat) :
    8 * leafWord i = 4294971424 + pentaSlotOffset 0 i := by
  rw [leaf_word_level]
  exact penta_slot_byte_address 0 i (by decide)

theorem salt_byte_address (i : Nat) :
    8 * saltWord i = 4294971424 + QUAD_SALT_BASE + 16*i := by
  unfold saltWord QUAD_SALT_BASE
  omega

theorem heap_byte_address (k : Nat) : 8 * heapWord k = 4294971424 + 32*k := by
  unfold heapWord
  omega

/-- A leaf reply ends by the next group's zero prefix. -/
theorem leaf_write_end (i : Nat) : leafWord i + 25 ≤ groupWord (i/5+1) := by
  unfold leafWord groupWord
  omega

theorem leaf_after_zero_prefix (i : Nat) : groupWord (i/5)+5 ≤ leafWord i := by
  unfold leafWord
  omega

/-- Earlier digest slots survive later leaves, despite the 200-byte replies. -/
theorem leaf_digest_separate (i j : Nat) (ordered : i < j) : leafWord i+4 ≤ leafWord j := by
  unfold leafWord groupWord
  omega

/-- No leaf reply writes any group's 40-byte zero prefix. -/
theorem leaf_zero_prefix_separate (i g : Nat) :
    leafWord i+25 ≤ groupWord g ∨ groupWord g+5 ≤ leafWord i := by
  by_cases earlier : i/5 < g
  · left
    have := leaf_write_end i
    unfold groupWord at *
    omega
  · right
    have := leaf_after_zero_prefix i
    unfold groupWord at *
    omega

theorem leaf_salt_separate (i j : Nat) (inside : i < LENGTH) : leafWord i+25 ≤ saltWord j := by
  have endWrite := leaf_write_end i
  unfold groupWord saltWord at *
  rw [length_value] at inside
  omega

/-! ### General levels -/

/-- A node reply (200 bytes from its slot) ends by the next group. -/
theorem slot_write_end (k j : Nat) : pentaSlotWord k j + 25 ≤ pentaGroupWord k (j/5+1) := by
  unfold pentaSlotWord pentaGroupWord
  omega

theorem slot_after_zero_prefix (k j : Nat) : pentaGroupWord k (j/5)+5 ≤ pentaSlotWord k j := by
  unfold pentaSlotWord
  omega

theorem slot_separate (k i j : Nat) (ordered : i < j) : pentaSlotWord k i+4 ≤ pentaSlotWord k j := by
  unfold pentaSlotWord pentaGroupWord
  omega

theorem slot_zero_prefix_separate (k j g : Nat) :
    pentaSlotWord k j+25 ≤ pentaGroupWord k g ∨ pentaGroupWord k g+5 ≤ pentaSlotWord k j := by
  by_cases earlier : j/5 < g
  · left
    have := slot_write_end k j
    unfold pentaGroupWord at *
    omega
  · right
    have := slot_after_zero_prefix k j
    unfold pentaGroupWord at *
    omega

theorem slot_advance (k j : Nat) :
    pentaSlotWord k j + (if j%5=4 then 30 else 4) = pentaSlotWord k (j+1) := by
  unfold pentaSlotWord pentaGroupWord
  split <;> omega

/-- The used part of level `k`: its groups `0 … pentaCount (k+1) - 1`. -/
def levelEnd (k : Nat) : Nat := pentaGroupWord k (pentaCount (k+1))

private theorem level_ends : ∀ k : Fin 11, levelEnd k.val ≤ pentaGroupWord (k.val+1) 0 := by
  decide

theorem level_end_next (k : Nat) (inside : k < 11) : levelEnd k ≤ pentaGroupWord (k+1) 0 :=
  level_ends ⟨k,inside⟩

theorem levels_below_salts : pentaGroupWord 11 1 + 22 ≤ saltWord 0 := by decide

theorem trapdoor_below_levels (k g : Nat) (bound : k ≤ 11) : 536871428 + 507 ≤ pentaGroupWord k g := by
  have : 507 ≤ pentaBaseWord k := (penta_base_table ⟨k,by omega⟩).2
  unfold pentaGroupWord
  omega

private theorem base_mono_table : ∀ k : Fin 11, ∀ l : Fin 12, k.val < l.val →
    levelEnd k.val ≤ pentaGroupWord l.val 0 := by
  decide

/-- Groups of a lower level lie below every group of a higher level. -/
theorem level_order (k l g : Nat) (lower : k < l) (bound : l ≤ 11) (inside : g < pentaCount (k+1)) (h : Nat) :
    pentaGroupWord k g + 46 ≤ pentaGroupWord l h := by
  have table := base_mono_table ⟨k,by omega⟩ ⟨l,by omega⟩ lower
  change pentaGroupWord k (pentaCount (k+1)) ≤ pentaGroupWord l 0 at table
  have a : pentaGroupWord k g + 46 ≤ pentaGroupWord k (pentaCount (k+1)) := by
    unfold pentaGroupWord; omega
  have b : pentaGroupWord l 0 ≤ pentaGroupWord l h := by
    unfold pentaGroupWord; omega
  omega

theorem group_below_salts (k g : Nat) (bound : k ≤ 11) (inside : g < pentaCount (k+1)) (i : Nat) :
    pentaGroupWord k g + 46 ≤ saltWord i := by
  by_cases top : k = 11
  · subst k
    have : g = 0 := by
      change g < pentaCount 12 at inside
      have : pentaCount 12 = 1 := by decide
      omega
    subst g
    have := levels_below_salts
    have : pentaGroupWord 11 0 + 46 = pentaGroupWord 11 1 := by unfold pentaGroupWord; omega
    unfold saltWord at *
    omega
  · have := level_order k 11 g (by omega) le_rfl inside 1
    have := levels_below_salts
    unfold saltWord at *
    omega

theorem layout_trapdoor_size (opening checker : Image) :
    (submission opening checker).sizes.trapdoor = QUAD_TRAPDOOR_BYTES := rfl

theorem layout_proof_capacity (opening checker : Image) :
    (submission opening checker).sizes.proof = PENTA_PROOF_CAPACITY := rfl

/-- The destination range fits a signed twelve-bit immediate. -/
theorem slot_immediate_range (u : Nat) :
    -2048 ≤ (-1536 + 368 * Int.ofNat ((u%45)/5) + 32 * Int.ofNat (u%5)) ∧
    (-1536 + 368 * Int.ofNat ((u%45)/5) + 32 * Int.ofNat (u%5)) ≤ 2047 := by
  change -2048 ≤ (-1536 + 368 * (((u%45)/5 : Nat) : Int) + 32 * ((u%5 : Nat) : Int)) ∧
    (-1536 + 368 * (((u%45)/5 : Nat) : Int) + 32 * ((u%5 : Nat) : Int)) ≤ 2047
  have h45 := Nat.mod_lt u (by decide : 0 < 45)
  have h5 := Nat.mod_lt u (by decide : 0 < 5)
  omega

/-- Number of output-window rebases in one unrolled leaf body. -/
theorem leaf_rebase_count :
    ((List.range 4096).filter (fun u => u%45=44)).length = 91 := by decide +kernel

theorem salt_rebase_count :
    ((List.range 4096).filter (fun u => u%256=127)).length = 16 := by decide +kernel

end TwoPermutationPrototype.Quad.Commit
