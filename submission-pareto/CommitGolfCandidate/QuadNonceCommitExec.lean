import CommitGolfCandidate.QuadNonceCommitLoop

/-! Execution of the overlapped permutation expansion for every possible reply. -/
namespace TwoPermutationPrototype.Quad.Commit.Chain
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 14000
set_option maxHeartbeats 650000
attribute [local irreducible] execute chainAdvance writeBits chainPermReply image

/-- Exact one-call execution, accounting for the group branch when it is fetched. -/
theorem nonce_chain_step (s : MachineState) (j : Nat) (hj : j < nonceChainCount)
    (h : NonceChainFrame s j) (fuel : Nat) :
    execute image (3+(if j%288=287 then 1 else 0)+fuel) s true =
      (do let y ← World.query (.inr (.inr (.inl (chainPermInput s))))
          let r ← execute image fuel (chainAdvance s j y) true
          return r.charge (10+(if j%288=287 then 1 else 0)) 1) := by
  let tail := if j%288=287 then 1 else 0
  have pc : s.pc = BitVec.ofNat 64 (950308 + 12*(j%288)) := by
    simpa [nonceChainPC,Nat.ne_of_lt hj] using h.pc
  have slot := Nat.mod_lt j (by decide : 0 < 288)
  have fetchCall := nonce_chain_triple (j%288) 0 slot (by decide) s (by simpa using pc)
  have source : (s.getReg .x10).toNat=nonceChainSource j := by
    rw [h.input,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold nonceChainSource nonceChainBase;dsimp [nonceChainCount] at hj;omega)]
  have dest : (s.getReg .x12).toNat=nonceChainDest j := by
    rw [h.output,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by unfold nonceChainDest nonceChainBase;dsimp [nonceChainCount] at hj;omega)]
  have call := chain_perm_call _ s (2+(tail+fuel)) true fetchCall h.ready
    (by rw [source]; unfold nonceChainSource nonceChainBase;omega)
    (by rw [dest]; unfold nonceChainDest nonceChainBase;omega)
    (by rw [source]; unfold nonceChainSource nonceChainBase MEMORY_BYTES;dsimp [nonceChainCount] at hj;omega)
    (by rw [dest]; unfold nonceChainDest nonceChainBase MEMORY_BYTES;dsimp [nonceChainCount] at hj;omega)
  rw [show 3+(if j%288=287 then 1 else 0)+fuel = 1+(2+(tail+fuel)) by dsimp [tail];omega, call]
  apply bind_congr
  intro y
  let w := chainPermReply s y
  have wpc : w.pc = BitVec.ofNat 64 (950308+12*(j%288)+4) := by
    rw [show w.pc=s.pc+4 from nonce_reply_pc s y,pc]
    simp only [BitVec.ofNat_add]
    rfl
  let advance := nonceIncrements w
  have next := chain_advance_frame s j y h
  have apc : advance.pc = BitVec.ofNat 64 (950308+12*(j%288)+12) := by
    rw [show advance.pc=w.pc+4+4 from nonce_increments_pc w,wpc, show 950308+12*(j%288)+12 = ((950308+12*(j%288)+4)+4)+4 by omega]
    simp only [BitVec.ofNat_add,BitVec.add_assoc]
    rfl
  have key : chainAdvance s j y = advance.setPC (BitVec.ofNat 64 (nonceChainPC (j+1))) := chain_advance_eq s j y
  rw [nonce_increments_execute (j%288) slot w wpc]
  simp only [bind_assoc,pure_bind]
  by_cases edge : j%288=287
  · have atBranch : advance.pc=953764 := by rw [apc,edge]; rfl
    have output := next.output
    have limit := next.limit
    rw [key, MachineState.getReg_setPC] at output limit
    have latch := nonce_latch_pc advance j edge hj atBranch output limit
    have br := execute_ordinary_step image (.base (.BLTU .x12 .x7 4736))
      advance (chainAdvance s j y) fuel true (nonce_chain_latch _ atBranch) (by
        change some (execInstrBr advance (.BLTU .x12 .x7 4736)) = _
        rw [latch,key])
    simp only [tail,edge,ite_true,Nat.add_comm 1 fuel]
    rw [br]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro r
    simp [Execution.charge,instructionCycles,Nat.add_assoc] <;> omega
  · have nextPc : advance.pc = BitVec.ofNat 64 (nonceChainPC (j+1)) := by
      have notLast : j+1 ≠ nonceChainCount := by dsimp [nonceChainCount] at hj ⊢;omega
      rw [apc,nonceChainPC,if_neg notLast]
      congr 1
      omega
    have eq : advance = chainAdvance s j y := by
      rw [key,← nextPc]
      cases advance
      rfl
    simp only [tail,edge,ite_false,Nat.zero_add]
    rw [←eq]
    apply bind_congr
    intro r
    simp [Execution.charge,Nat.add_assoc] <;> omega

theorem nonce_chain_run (s : MachineState) (j n : Nat) (limit : j+n ≤ nonceChainCount)
    (h : NonceChainFrame s j) (fuel : Nat) :
    execute image (nonceChainSteps (j+n)-nonceChainSteps j+fuel) s true =
      (do let next ← chainRun j s n
          let result ← execute image fuel next true
          return result.charge (nonceChainCycles (j+n)-nonceChainCycles j) n) := by
  induction n generalizing j s with
  | zero => simp [chainRun,Execution.charge]
  | succ n ih =>
    have steps : nonceChainSteps (j+(n+1))-nonceChainSteps j+fuel =
        3+(if j%288=287 then 1 else 0)+(nonceChainSteps ((j+1)+n)-nonceChainSteps (j+1)+fuel) := by
      simp only [nonceChainSteps]
      split <;> omega
    rw [steps,nonce_chain_step s j (by omega) h]
    simp only [chainRun,bind_assoc]
    apply bind_congr
    intro y
    rw [ih _ _ (by omega) (chain_advance_frame s j y h)]
    simp only [bind_assoc,pure_bind]
    apply bind_congr
    intro last
    apply bind_congr
    intro r
    simp only [Execution.charge]
    congr 2 <;> first | omega | (unfold nonceChainCycles; split <;> omega)

end TwoPermutationPrototype.Quad.Commit.Chain
