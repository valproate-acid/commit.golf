import CommitGolfCandidate.TwoPermutationPackedCapFinish
import CommitGolfCandidate.TwoPermutationPackedCapPrepare

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (capRootAt cap_hash_count_tree cap_hash_count_root)

structure CapSuffixReady (groups : List Nat) (state : MachineState) (pointer claim : Nat) : Prop where
  pc : state.pc = 0x1444
  proof : state.getReg .x21 = BitVec.ofNat 64 pointer
  roots : state.getReg .x25 = 16384#64
  markBase : state.getReg .x26 = BitVec.ofNat 64 Opening.markBase
  capLeaves : state.getReg .x27 = 256#64
  selector : state.getReg .x5 = 0
  claimReg : state.getReg .x9 = wordAddress claim
  leafMarks : ∀ node, 256 ≤ node → node < 512 → machineMarks state node = Opening.markWord groups node
  proofAbove : 32768 ≤ pointer
  proofEven : pointer%2 = 0
  proofRoom : pointer+30*(capFrontierNodes groups 1 8).length ≤ MEMORY_BYTES
  claimAbove : 4096 ≤ claim
  claimRoom : claim+4 ≤ 2^33

private theorem prep_digest (state : MachineState) (base : state.getReg .x26 = BitVec.ofNat 64 Opening.markBase)
    (word : Nat) (above : 768 ≤ word) (bounded : word+4 ≤ 2^61) :
    readBuffer (startedCap state) (8*word) 32 = readBuffer state (8*word) 32 := by
  apply read_digest_congr _ _ _ (by omega)
  intro digit inside
  simp only [← Nat.mul_add]
  exact started_cap_word state base (word+digit) (by omega) (Or.inr (by omega))

attribute [local irreducible] startedCap execute readBuffer capRootAt

theorem execute_cap_suffix_with (codec : FrontierKernel) (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (pointer claim fuel : Nat) (ready : CapSuffixReady groups before pointer claim)
    (fuelBound : 25056 ≤ fuel) : CapFinished oracle groups before pointer claim fuel := by
  let prepared := startedCap before
  obtain ⟨pc, node, len, kind⟩ := started_cap_fixed before
  have preserved (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x7) (c : reg ≠ .x28) (d : reg ≠ .x29)
      (s : reg ≠ .x11) (k : reg ≠ .x13) : prepared.getReg reg = before.getReg reg :=
    started_cap_register before reg a b c d s k
  have rootReg : prepared.getReg .x25 = 16384#64 :=
    (preserved .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.roots
  have markReg : prepared.getReg .x26 = 4096#64 :=
    (preserved .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.markBase
  have leavesReg : prepared.getReg .x27 = 256#64 :=
    (preserved .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.capLeaves
  have oracleReg : prepared.getReg .x5 = 0 :=
    (preserved .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.selector
  have proofReg : prepared.getReg .x21 = BitVec.ofNat 64 pointer :=
    (preserved .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.proof
  have claimReg : prepared.getReg .x9 = wordAddress claim :=
    (preserved .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ready.claimReg
  have endReg : prepared.getReg .x22 = before.getReg .x22 :=
    preserved .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have marks (n : Nat) (positive : 0 < n) (bounded : n < 512) :
      memoryView prepared (512+n) = Opening.markWord groups n := by
    have observed := started_cap_mark before groups ready.markBase ready.leafMarks n positive bounded
    change prepared.getMem (BitVec.ofNat 64 (Opening.markBase+8*n)) = _ at observed
    change prepared.getMem (BitVec.ofNat 64 (8*(512+n))) = _
    simpa only [show Opening.markBase+8*n = 8*(512+n) by unfold Opening.markBase; omega] using observed
  have position : CapPosition groups prepared 1 pointer :=
    ⟨⟨⟨oracleReg, len, kind, rootReg, markReg, leavesReg⟩, marks⟩, node, proofReg, ready.proofAbove, ready.proofEven⟩
  have ran := execute_prepared_cap_suffix codec oracle groups prepared pointer claim (fuel-2554) position pc claimReg
    ready.claimAbove ready.claimRoom ready.proofRoom (by omega)
  let start : Segment oracle before prepared :=
    Segment.ordinary oracle 2554 2554 (execute_started_cap before ready.pc · ready.markBase)
  have trace := start.checked (fuel-2554)
  change checkEvaluation oracle (recordRows (execute packedImage (2554+(fuel-2554)) before false)) = _ at trace
  rw [show 2554+(fuel-2554) = fuel by omega] at trace
  let observed := checkEvaluation oracle (recordRows (execute packedImage (fuel-2554) prepared false))
  have projection : checkEvaluation oracle (recordRows (execute packedImage fuel before false)) =
      ((observed.1.1.charge 2554 0, observed.1.2), observed.2) := by
    change _ = ((observed.1.1.charge 2554 0, [] ++ observed.1.2), 0+observed.2) at trace
    simpa only [List.nil_append, Nat.zero_add] using trace
  have claimDigest := prep_digest before ready.markBase claim (by have := ready.claimAbove; omega)
    (by have := ready.claimRoom; omega)
  have leafDigest (leaf : Nat) (bound : leaf < 512) :
      capRootAt prepared leaf = capRootAt before leaf := by
    unfold capRootAt
    exact prep_digest before ready.markBase _ (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [projection]
    exact ran.calls
  · rw [projection]
    exact ran.honestCalls
  · dsimp only
    rw [projection]
    intro success leaf listed low high
    have path := ran.paths success leaf listed low high
    rw [leafDigest leaf high, claimDigest] at path
    exact path
  · rw [projection]
    exact ran.terminates
  · intro heap model contents expected finish
    have input : CapContents groups prepared 1 8 pointer heap := by
      constructor
      · intro leaf member low high under
        rw [leafDigest leaf high]
        exact contents.leaves leaf member low high under
      · intro i inside
        have room := ready.proofRoom
        have range : MEMORY_BYTES < 2^64 := by decide
        have start := ready.proofAbove
        have unchanged : readBuffer prepared (pointer+30*i) 30 = readBuffer before (pointer+30*i) 30 := by
          apply read_buffer_above before prepared _ _ 4096 (by omega) (by omega)
          intro word above bounded
          exact started_cap_word before ready.markBase word bounded (Or.inr (by omega))
        rw [unchanged]
        exact contents.frontier i inside
    have good := ran.honest heap model input (claimDigest.trans expected) (endReg.trans finish)
    rw [projection]
    exact good

end TwoPermutationPrototype.Packed.Checker
