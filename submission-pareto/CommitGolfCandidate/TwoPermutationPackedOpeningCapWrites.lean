import CommitGolfCandidate.TwoPermutationPackedOpeningBytes
import CommitGolfCandidate.TwoPermutationOpeningCapWrites

namespace TwoPermutationPrototype.PackedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open Opening (capDigestAddress cap_digest_bounds proofBase)

structure CapWrites (before after : MachineState) (dest : Nat) (nodes : List Nat) : Prop where
  frame : ∀ address < 2^64, address < dest ∨ dest+30*nodes.length ≤ address →
    after.getByte (BitVec.ofNat 64 address) = before.getByte (BitVec.ofNat 64 address)
  digest : ∀ i (inside : i < nodes.length),
    readBuffer after (dest+30*i) 30 =
      (readBuffer before (capDigestAddress nodes[i]) 32).extractLsb' 0 240

theorem CapWrites.move {before after before' after' : MachineState} {dest : Nat} {nodes : List Nat}
    (writes : CapWrites before after dest nodes) (start : before'.mem = before.mem)
    (finish : after'.mem = after.mem) :
    CapWrites before' after' dest nodes := by
  constructor
  · intro address fit outside
    simpa only [MachineState.getByte, MachineState.getMem, start, finish] using writes.frame address fit outside
  · intro i inside
    simpa only [readBuffer, MachineState.getByte, MachineState.getMem, start, finish] using
      writes.digest i inside

theorem cap_writes_empty (before after : MachineState) (dest : Nat) (memory : after.mem = before.mem) :
    CapWrites before after dest [] := by
  constructor
  · intro address _ _
    simp only [MachineState.getByte, MachineState.getMem, memory]
  · intro i inside
    simp at inside

theorem ByteCopy.cap_writes {before after : MachineState} {node dest : Nat}
    (copy : ByteCopy before after (capDigestAddress node) dest 30)
    (fits : dest+30 ≤ 2^64) : CapWrites before after dest [node] := by
  constructor
  · intro address bound outside
    apply copy.frame
    intro i hi same
    have eq := Opening.nat_address_injective bound (by omega) same
    simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one] at outside
    omega
  · intro i inside
    have zero : i = 0 := by simpa using inside
    subst i
    simpa only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] using copy.read_low_digest

private theorem frame_buffer {before after : MachineState} {dest : Nat} {nodes : List Nat}
    (writes : CapWrites before after dest nodes) (start count : Nat)
    (fits : start+count ≤ 2^64)
    (outside : start+count ≤ dest ∨ dest+30*nodes.length ≤ start) :
    readBuffer after start count = readBuffer before start count := by
  unfold readBuffer
  apply congrArg (BitVec.ofNat (8*count))
  apply Finset.sum_congr rfl
  intro i hi
  have bound := Finset.mem_range.mp hi
  rw [writes.frame _ (by omega) (outside.imp (by omega) (by omega))]

theorem CapWrites.join {before midway after : MachineState} {dest : Nat} {left right : List Nat}
    (first : CapWrites before midway dest left)
    (second : CapWrites midway after (dest+30*left.length) right)
    (afterHeap : proofBase ≤ dest)
    (rightBound : ∀ node ∈ right, node < 512)
    (fits : dest+30*(left++right).length ≤ MEMORY_BYTES) :
    CapWrites before after dest (left++right) := by
  have fit64 : dest+30*(left++right).length ≤ 2^64 := by
    unfold MEMORY_BYTES at fits
    omega
  simp only [List.length_append, Nat.mul_add] at fit64
  constructor
  · intro address bounded outside
    simp only [List.length_append, Nat.mul_add] at outside
    exact (second.frame address bounded (outside.imp (by omega) (by omega))).trans
      (first.frame address bounded (outside.imp (by omega) (by omega)))
  · intro i inside
    by_cases isLeft : i < left.length
    · rw [List.getElem_append_left isLeft]
      rw [frame_buffer second (dest+30*i) 30 (by omega) (Or.inl (by omega))]
      exact first.digest i isLeft
    · have rightInside : i-left.length < right.length := by
        simp only [List.length_append] at inside
        omega
      rw [List.getElem_append_right (by omega)]
      have offset : dest+30*i = (dest+30*left.length)+30*(i-left.length) := by omega
      rw [offset, second.digest (i-left.length) rightInside]
      have srcBound : capDigestAddress right[i-left.length] + 32 ≤ proofBase :=
        (cap_digest_bounds _ (rightBound _ (List.getElem_mem rightInside))).2
      rw [frame_buffer first _ 32 (by omega) (Or.inl (srcBound.trans afterHeap))]

end TwoPermutationPrototype.PackedOpening
