import CommitGolfCandidate.TwoPermutationPackedCheckerMeasure
import CommitGolfCandidate.TwoPermutationPackedCheckerSetup
import CommitGolfCandidate.TwoPermutationPackedCheckerExit
import CommitGolfCandidate.TwoPermutationPackedCheckCursor

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Checker (check_initial_registers checker_positions_bound)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] execute

private abbrev headerInput (input : CheckInput) := Assembly.submission.initialState .check input
private abbrev measured (input : CheckInput) := measureState (headerInput input)
private abbrev shortChecked (input : CheckInput) := CheckGuard.short.next (measured input)
private abbrev emptyChecked (input : CheckInput) := CheckGuard.empty.next (shortChecked input)

private abbrev measured_view (input : CheckInput) := measure_post (headerInput input) (check_initial_registers input).1

private theorem measure_hop (input : CheckInput) : Hop (headerInput input) (measured input) 2 5 :=
  execute_measure (headerInput input) (check_initial_registers input).1

private theorem short_hop (input : CheckInput) : Hop (headerInput input) (shortChecked input) 3 6 :=
  (measure_hop input).thenDo (check_guard_hop .short (measured input) (measured_view input).1)

private theorem short_pc (input : CheckInput) (fits : input.proof.length ≤ 8355061248) :
    (shortChecked input).pc = if input.proof.length < 498*input.positions.card then 0x15b0 else 4108 := by
  obtain ⟨_,_,_,_,_,count,length⟩ := check_initial_registers input
  obtain ⟨pc,required,_,kept⟩ := measured_view input
  have requiredEq : (measured input).getReg .x6 = BitVec.ofNat 64 (498*input.positions.card) := by
    rw [required, count]
    change BitVec.ofNat 64 input.positions.card * BitVec.ofNat 64 498 = _
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have lengthEq : (measured input).getReg .x17 = BitVec.ofNat 64 input.proof.length :=
    (kept .x17 (by decide)).trans length
  have maximum := checker_positions_bound input
  have size : input.proof.length < 2^64 := by omega
  have countSize : 498*input.positions.card < 2^64 := by omega
  rw [check_short_guard _ pc,requiredEq,lengthEq]
  have same : BitVec.ofNat 64 input.proof.length < BitVec.ofNat 64 (498*input.positions.card) ↔
      input.proof.length < 498*input.positions.card := by
    change (BitVec.ofNat 64 input.proof.length).toNat < (BitVec.ofNat 64 (498*input.positions.card)).toNat ↔ _
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt size,Nat.mod_eq_of_lt countSize]
  simp only [same]

private theorem empty_hop (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (long : 498*input.positions.card ≤ input.proof.length) :
    Hop (headerInput input) (emptyChecked input) 4 7 := by
  have pc := (short_pc input fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  exact (short_hop input).thenDo (check_guard_hop .empty _ pc)

private theorem empty_pc (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (long : 498*input.positions.card ≤ input.proof.length) :
    (emptyChecked input).pc = if input.positions.card = 0 then 0x15a0 else 0x1010 := by
  have start := (short_pc input fits).trans (ite_eq_right (Nat.not_lt.mpr long))
  have count := (check_guard_register .short (measured input) .x16).trans
    (((measured_view input).2.2.2 .x16 (by decide)).trans (check_initial_registers input).2.2.2.2.2.1)
  have cardinal := checker_positions_bound input
  have same : BitVec.ofNat 64 input.positions.card = (0 : Word) ↔ input.positions.card = 0 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : input.positions.card < 2^64)]
    rfl
  rw [check_empty_guard _ start,count]
  simp only [same]

private theorem empty_keeps (input : CheckInput) (reg : Reg) (a : reg ≠ .x6) :
    (emptyChecked input).getReg reg = (headerInput input).getReg reg :=
  (check_guard_register .empty (shortChecked input) reg).trans
    ((check_guard_register .short (measured input) reg).trans ((measured_view input).2.2.2 reg a))

theorem header_empty (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (empty : input.positions.card = 0) :
    ∃ result : Execution,
      execute packedImage 34359803904 (headerInput input) false = pure result ∧
      result.exit ≠ .unfinished ∧ (input.proof.length = 0 → result.exit = .success) := by
  have long : 498*input.positions.card ≤ input.proof.length := by omega
  have pc := (empty_pc input fits long).trans (ite_eq_left empty)
  obtain ⟨result,accepts,ends,_,finished⟩ := execute_empty_check _ pc (34359803904-8)
  have run := empty_hop input fits long (4+(34359803904-8))
  rw [finished] at run
  refine ⟨result.charge 7 0, ?_, ends, ?_⟩
  · simpa only [pure_bind] using run
  · intro noProof
    apply accepts.mpr
    rw [empty_keeps input .x17 (by decide),
      (check_initial_registers input).2.2.2.2.2.2,noProof]

theorem header_short (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (short : input.proof.length < 498*input.positions.card) :
    ∃ result : Execution,
      execute packedImage 34359803904 (headerInput input) false = pure result ∧ result.exit = .failure := by
  have failed := (short_pc input fits).trans (ite_eq_left short)
  have abort := execute_header_reject _ failed (34359803904-6)
  have run := short_hop input (3+(34359803904-6))
  rw [abort] at run
  exact ⟨_,by simpa only [pure_bind] using run,rfl⟩

theorem header_positive (input : CheckInput) (fits : input.proof.length ≤ 8355061248)
    (nonempty : input.positions.card ≠ 0) (long : 498*input.positions.card ≤ input.proof.length) :
    ∃ state : MachineState,
      RecordCursor input 0 state ∧ state.mem = (headerInput input).mem ∧ Hop (headerInput input) state 22 25 := by
  let state := checkPreparePrefix (emptyChecked input) 18
  have here := (empty_pc input fits long).trans (ite_eq_right nonempty)
  have usable := check_prepare_view _ here
  have code := (empty_hop input fits long).thenDo (check_prepare_hop _ here)
  obtain ⟨_,root,indices,values,proof,count,length⟩ := check_initial_registers input
  have keep (r : Reg) (a : r ≠ .x6) := empty_keeps input r a
  refine ⟨state,⟨?_,?_,?_,?_,?_,usable.tag,?_,usable.length,?_,usable.digest,
    usable.pair,usable.capRoots,usable.marks,usable.capCount,usable.selector,usable.nonceScratch⟩,?_,code⟩
  · exact usable.pc.trans (ite_eq_right (Ne.symm nonempty)).symm
  · exact usable.index.trans ((keep .x13 (by decide)).trans indices)
  · rw [usable.value,keep .x14 (by decide),values]
    rfl
  · exact usable.proof.trans ((keep .x15 (by decide)).trans proof)
  · exact usable.count.trans ((keep .x16 (by decide)).trans count)
  · exact usable.root.trans ((keep .x11 (by decide)).trans root)
  · rw [usable.proofEnd,keep .x15 (by decide),keep .x17 (by decide),proof,length]
    change BitVec.ofNat 64 10334769248+BitVec.ofNat 64 input.proof.length = _
    rw [← BitVec.ofNat_add]
  · exact usable.memory.trans ((check_guard_memory .empty (shortChecked input)).trans
      ((check_guard_memory .short (measured input)).trans (measured_view input).2.2.1))

end TwoPermutationPrototype.Packed.Checker
