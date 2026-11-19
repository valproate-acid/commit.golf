import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.Execution

/-! Instruction fetch and ordinary-step execution for the straight-line part of
each concrete commitment leaf. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def commitImage : Image := ⟨Manifest.commitWords, []⟩

def leafPC (slot : Fin 16) (offset : Nat) : Word :=
  BitVec.ofNat 64 (4160 + 60 * slot.val + 4 * offset)

def leafInstr (slot : Fin 16) (offset : Nat) : Instr :=
  ((leafInstructions slot)[offset]?).getD .EBREAK

private theorem decode_slot : ∀ slot : Fin 16, ∀ i : Fin 15,
    (Manifest.commitWords[16 + 15*slot.val + i.val]?).bind Manifest.decodeBase =
      some (leafInstr slot i.val) := by decide +kernel

theorem fetch_leaf (slot : Fin 16) (i : Nat) (inside : i < 15) (s : MachineState)
    (pc : s.pc = leafPC slot i) :
    fetch commitImage s = some (.base (leafInstr slot i)) := by
  have decoded := decode_slot slot ⟨i, inside⟩
  have address : s.pc.toNat = 4160 + 60 * slot.val + 4*i := by
    rw [pc, leafPC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := slot.isLt
    omega
  rw [fetch, address, if_pos (by omega)]
  change (match Manifest.commitWords[(4160 + 60*slot.val + 4*i - 4096)/4]? with
          | some w => decodeInstruction w | none => none) = _
  rw [show (4160 + 60*slot.val + 4*i - 4096)/4 = 16 + 15*slot.val+i by omega]
  cases word : Manifest.commitWords[16+15*slot.val+i]? with
  | none => simp [word] at decoded
  | some w =>
    simp only [word, Option.bind_some, Manifest.decodeBase] at decoded
    cases instruction : decodeInstruction w with
    | none => simp [instruction] at decoded
    | some ins => cases ins <;> simp_all

theorem leaf_pc_add (slot : Fin 16) (i j : Nat) :
    leafPC slot i + BitVec.ofNat 64 (4*j) = leafPC slot (i+j) := by
  unfold leafPC
  rw [← BitVec.ofNat_add]
  congr 1
  omega

def firstPrefix (s : MachineState) (slot : Fin 16) (i : Nat) : MachineState :=
  ((firstInstructions slot).take i).foldl execInstrBr s

def secondPrefix (s : MachineState) (slot : Fin 16) (i : Nat) : MachineState :=
  ((secondInstructions slot).take i).foldl execInstrBr s

theorem first_ordinary_run (s : MachineState) (slot : Fin 16) (fuel : Nat) (allowCoins : Bool)
    (pc : s.pc = leafPC slot 0)
    (valid : ∀ i < 8, memoryArgumentsValid (firstPrefix s slot i) (leafInstr slot i) = true) :
    execute commitImage (8+fuel) s allowCoins =
      (do let r ← execute commitImage fuel ((firstInstructions slot).foldl execInstrBr s) allowCoins
          return r.charge 8 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := firstPrefix s slot)
  intro i hi
  refine ⟨.base (leafInstr slot i), fetch_leaf slot i (by omega) _ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [firstPrefix,firstInstructions,execInstrBr,MachineState.setPC,pc,
      leafPC,BitVec.add_assoc,BitVec.ofNat_add, Nat.add_assoc]
  · have v := valid i hi
    interval_cases i <;>
      simp only [leafInstr,leafInstructions,firstInstructions,List.cons_append,List.nil_append,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] at v ⊢ <;>
      simp only [ordinaryStep,v,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem second_ordinary_run (s : MachineState) (slot : Fin 16) (fuel : Nat) (allowCoins : Bool)
    (pc : s.pc = leafPC slot 9)
    (valid : ∀ i < 4, memoryArgumentsValid (secondPrefix s slot i) (leafInstr slot (9+i)) = true) :
    execute commitImage (4+fuel) s allowCoins =
      (do let r ← execute commitImage fuel ((secondInstructions slot).foldl execInstrBr s) allowCoins
          return r.charge 4 0) := by
  apply CommitGolfCandidate.execute_unit_steps (states := secondPrefix s slot)
  intro i hi
  refine ⟨.base (leafInstr slot (9+i)), fetch_leaf slot (9+i) (by omega) _ ?_, ?_, ?_⟩
  · interval_cases i <;> simp [secondPrefix,secondInstructions,execInstrBr,MachineState.setPC,pc,
      leafPC,BitVec.add_assoc,BitVec.ofNat_add,Nat.add_assoc]
  · have v := valid i hi
    interval_cases i <;>
      simp only [leafInstr,leafInstructions,firstInstructions,secondInstructions,List.cons_append,List.nil_append,
        List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some, Nat.reduceAdd] at v ⊢ <;>
      simp only [ordinaryStep,v,↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

end TwoPermutationPrototype.RV64
