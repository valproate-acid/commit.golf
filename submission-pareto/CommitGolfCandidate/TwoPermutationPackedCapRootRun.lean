import CommitGolfCandidate.TwoPermutationPackedCapRoot
import CommitGolfCandidate.TwoPermutationCheckerRootRun

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt word_offset aligned_access)

structure RootScanReady (state : MachineState) (claim left : Nat) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096+4*(345+3*(4-left)))
  roots : state.getReg .x25 = wordAddress 2048
  commitment : state.getReg .x9 = wordAddress claim
  claimBound : claim+4 ≤ 2^33

theorem root_word_unchanged (before after : MachineState)
    (mem : after.mem = before.mem) (r25 : after.getReg .x25 = before.getReg .x25)
    (r9 : after.getReg .x9 = before.getReg .x9) (i : Fin 4) :
    rootWordMatches after i ↔ rootWordMatches before i := by
  simp [rootWordMatches, MachineState.getMem, mem, r25, r9]

private theorem root_scan_addresses {state : MachineState} {claim left : Nat}
    (ready : RootScanReady state claim left) (i : Fin 4) :
    accessValid (state.getReg .x25+BitVec.ofNat 64 (32+8*i.val)) 8 = true ∧
      accessValid (state.getReg .x9+BitVec.ofNat 64 (8*i.val)) 8 = true := by
  rw [ready.roots, ready.commitment, show 32+8*i.val = 8*(4+i.val) by omega, word_offset, word_offset]
  exact ⟨aligned_access _ (by omega), aligned_access _ (by have := ready.claimBound; omega)⟩

attribute [local irreducible] execute

theorem execute_root_scan {state : MachineState} {claim left : Nat}
    (ready : RootScanReady state claim left) (bounded : left ≤ 4) (fuel : Nat) :
    ∃ result : Execution,
      (result.exit = .success ↔ ∀ i : Fin 4, 4-left ≤ i.val → rootWordMatches state i) ∧
      result.oracleCalls = 0 ∧ result.exit ≠ .unfinished ∧
      execute packedImage (3*left+3+fuel) state false = pure result := by
  induction left generalizing state fuel with
  | zero =>
    have pc : state.pc = 0x1594 := ready.pc
    refine ⟨⟨.success, acceptState state,3,0⟩, ?_, rfl, (show Exit.success ≠ Exit.unfinished by decide), execute_accept state pc fuel⟩
    simp only [Nat.sub_zero, true_iff]
    intro i impossible
    omega
  | succ left ih =>
    let i : Fin 4 := ⟨4-(left+1), by omega⟩
    let next := rootCompare state i
    have pc : state.pc = BitVec.ofNat 64 (4096+4*(345+3*i.val)) := ready.pc
    obtain ⟨cap, claimAccess⟩ := root_scan_addresses ready i
    obtain ⟨nextPC, mem, regs⟩ := root_compare_post state i pc
    have executed := execute_root_compare state i (3*left+3+fuel) pc cap claimAccess
    have stable := root_word_unchanged state next mem (regs .x25 (by decide) (by decide))
      (regs .x9 (by decide) (by decide))
    have splitFuel : 3*(left+1)+3+fuel = 3+(3*left+3+fuel) := by omega
    rw [splitFuel, executed]
    by_cases same : rootWordMatches state i
    · have nextReady : RootScanReady next claim left := by
        refine ⟨?_, (regs .x25 (by decide) (by decide)).trans ready.roots,
          (regs .x9 (by decide) (by decide)).trans ready.commitment, ready.claimBound⟩
        change next.pc = _ at nextPC
        rw [nextPC, ite_eq_left same]
        congr 1
        have : i.val = 4-(left+1) := rfl
        omega
      obtain ⟨result, accepted, calls, ended, continuation⟩ := ih nextReady (by omega) fuel
      refine ⟨result.charge 3 0, ?_, by simpa [Execution.charge] using calls, ended, ?_⟩
      · change result.exit = .success ↔ _
        rw [accepted]
        constructor
        · intro tail j valid
          by_cases first : j = i
          · rwa [first]
          · have jAfter : 4-left ≤ j.val := by
              have : j.val ≠ i.val := fun eq => first (Fin.ext eq)
              have : i.val = 4-(left+1) := rfl
              omega
            exact (stable j).mp (tail j jAfter)
        · intro all j valid
          exact (stable j).mpr (all j (by omega))
      · erw [continuation]
        simp
    · have reject : next.pc = 0x15b0 := by
        change next.pc = _ at nextPC
        rw [nextPC, ite_eq_right same]
      refine ⟨⟨.failure,rejectState next,6,0⟩, ?_, rfl, (show Exit.failure ≠ Exit.unfinished by decide), ?_⟩
      · constructor
        · intro impossible
          cases impossible
        · intro all
          exact False.elim (same (all i (by rfl)))
      · have terminal := execute_reject next reject (3*left+fuel)
        erw [show 3*left+3+fuel = 3+(3*left+fuel) by omega, terminal]
        simp [Execution.charge]

theorem root_words_iff (state : MachineState) (claim : Nat)
    (roots : state.getReg .x25 = wordAddress 2048)
    (claimReg : state.getReg .x9 = wordAddress claim) :
    (∀ i : Fin 4, rootWordMatches state i) ↔ capRootAt state 1 = readBuffer state (8*claim) 32 := by
  unfold capRootAt
  rw [read_digest_eq_iff _ _ _ _ (by omega) (by omega)]
  constructor
  · intro words j bounded
    have same := words ⟨j,bounded⟩
    unfold rootWordMatches at same
    rw [roots, claimReg, show 32+8*j = 8*(4+j) by omega, word_offset, word_offset] at same
    simpa only [← Nat.mul_add, wordAddress, Nat.add_assoc] using same
  · intro digest i
    unfold rootWordMatches
    rw [roots, claimReg, show 32+8*i.val = 8*(4+i.val) by omega, word_offset, word_offset]
    simpa only [← Nat.mul_add, wordAddress, Nat.add_assoc] using digest i.val i.isLt

theorem execute_root_check (state : MachineState) (claim fuel : Nat) (pc : state.pc = 0x1560)
    (roots : state.getReg .x25 = wordAddress 2048) (claimReg : state.getReg .x9 = wordAddress claim)
    (claimBound : claim+4 ≤ 2^33) :
    ∃ result : Execution,
      (result.exit = .success ↔ state.getReg .x21 = state.getReg .x22 ∧
        capRootAt state 1 = readBuffer state (8*claim) 32) ∧ result.oracleCalls = 0 ∧ result.exit ≠ .unfinished ∧
      execute packedImage (16+fuel) state false = pure result := by
  obtain ⟨target, mem, stable⟩ := root_length_post state pc
  let next := rootLength state
  have entry : next.getReg .x9 = wordAddress claim := (stable _).trans claimReg
  have endRoots : next.getReg .x25 = wordAddress 2048 := (stable _).trans roots
  have paired (i : Fin 4) := root_word_unchanged state next mem (stable .x25) (stable .x9) i
  rw [show 16+fuel = 1+(15+fuel) by omega, execute_root_length state pc]
  by_cases length : state.getReg .x21 = state.getReg .x22
  · have entered : RootScanReady next claim 4 := by
      refine ⟨?_, endRoots, entry, claimBound⟩
      change next.pc = _
      rw [target, ite_eq_left length]
      rfl
    obtain ⟨result, good, calls, ended, execution⟩ := execute_root_scan entered (by decide) fuel
    have run : execute packedImage (15+fuel) (rootLength state) false = pure result := execution
    refine ⟨result.charge 1 0, ?_, by simpa [Execution.charge] using calls, ended, ?_⟩
    · rw [show (result.charge 1 0).exit = result.exit from rfl, good,
        ← root_words_iff state claim roots claimReg]
      simp only [length, true_and, Nat.sub_self, Nat.zero_le, forall_const]
      exact ⟨fun matched i => (paired i).mp (matched i), fun matched i => (paired i).mpr (matched i)⟩
    · rw [run]
      simp
  · have fail : next.pc = 0x15b0 := by rw [target, ite_eq_right length]
    have run : execute packedImage (15+fuel) (rootLength state) false =
        pure ⟨.failure, rejectState next, 3, 0⟩ := by
      rw [show 15+fuel = 3+(12+fuel) by omega]
      exact execute_reject next fail _
    refine ⟨⟨.failure,rejectState next,4,0⟩, by simp [length], rfl, (show Exit.failure ≠ Exit.unfinished by decide), ?_⟩
    rw [run]
    simp [Execution.charge]

end TwoPermutationPrototype.Packed.Checker
