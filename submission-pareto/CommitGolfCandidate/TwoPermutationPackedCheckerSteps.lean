import CommitGolfCandidate.TwoPermutationPackedImage

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp

theorem fetch_at (s : MachineState) (index : Nat) (instruction : Instr)
    (bounded : index < 367) (pc : s.pc = BitVec.ofNat 64 (4096+4*index))
    (decoded : (packedImage.code[index]?).bind decodeInstruction = some (.base instruction)) :
    fetch packedImage s = some (.base instruction) :=
  cap_image_fetch packedImage s index instruction (by omega) pc decoded

/-- Ordinary packed checker code with separately accounted fuel and cycle cost. -/
def Hop (s t : MachineState) (steps cycles : Nat) : Prop :=
  ∀ fuel, execute packedImage (steps+fuel) s false = do
    let result ← execute packedImage fuel t false
    return result.charge cycles 0

abbrev GroupHop (s t : MachineState) (cost : Nat) : Prop := Hop s t cost cost

attribute [local irreducible] execute

theorem Hop.thenDo {s t u : MachineState} {a b c d : Nat}
    (first : Hop s t a c) (last : Hop t u b d) : Hop s u (a+b) (c+d) := by
  intro fuel
  rw [Nat.add_assoc,first,last]
  simp only [bind_assoc,pure_bind,Execution.charge,Nat.zero_add,← Nat.add_assoc]

theorem GroupHop.thenDo {s t u : MachineState} {a b : Nat}
    (first : GroupHop s t a) (last : GroupHop t u b) : GroupHop s u (a+b) :=
  Hop.thenDo first last

end TwoPermutationPrototype.Packed.Checker
