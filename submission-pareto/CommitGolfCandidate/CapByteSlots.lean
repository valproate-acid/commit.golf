import CommitGolfCandidate.CapEncoding
import CommitGolfCandidate.InputMemory

/-! Exact little-endian slots of the cap transcript. The suffix is an arbitrary
byte list, so these identities do not silently discard a partial trailing
digest. Actual loader selection and checker scheduling are separate bridges. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

theorem cap_encoding_byte (digests : List Digest) (suffix : Proof)
    (ordinal offset : Nat) (present : ordinal < digests.length) (inside : offset < 32) :
    (capDigestEncoding digests ++ suffix)[32 * ordinal + offset]?.getD 0 =
      digests[ordinal].extractLsb' (8 * offset) 8 := by
  induction digests generalizing ordinal with
  | nil => simp at present
  | cons head rest ih =>
      cases ordinal with
      | zero =>
          simp only [capDigestEncoding, List.flatMap_cons, List.append_assoc,
            Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
          rw [List.getElem?_append_left (by simpa [digestBytes_length] using inside)]
          simp only [digestBytes, List.getElem?_ofFn, inside, ↓reduceDIte, Option.getD_some]
      | succ ordinal =>
          have tailPresent : ordinal < rest.length := by simp at present; omega
          simp only [capDigestEncoding, List.flatMap_cons, List.append_assoc,
            List.getElem_cons_succ]
          rw [List.getElem?_append_right (by
            rw [digestBytes_length]
            omega), digestBytes_length]
          have offsetEq : 32 * (ordinal + 1) + offset - 32 = 32 * ordinal + offset := by omega
          rw [offsetEq]
          exact ih ordinal tailPresent

/-- Reading one complete slot from any memory containing these bytes yields the
exact digest. The arbitrary suffix cannot affect an in-range slot. -/
theorem cap_encoding_read (state : MachineState) (digests : List Digest) (suffix : Proof)
    (base ordinal : Nat) (present : ordinal < digests.length)
    (bytes : ∀ offset < 32,
      state.getByte (BitVec.ofNat 64 (base + 32 * ordinal + offset)) =
        (capDigestEncoding digests ++ suffix)[32 * ordinal + offset]?.getD 0) :
    readBuffer state (base + 32 * ordinal) 32 = digests[ordinal] := by
  have decoded := read_serialized_slice state digests[ordinal]
    (base + 32 * ordinal) 0 32 (by
      intro offset inside
      simpa only [Nat.zero_add] using
        (bytes offset inside).trans (cap_encoding_byte digests suffix ordinal offset present inside))
  simpa only [Nat.mul_zero, Nat.zero_add, Nat.reduceMul, BitVec.extractLsb'_eq_self] using decoded

/-- A seventeen-digest lower record begins with its salt. -/
theorem cap_lower_encoding_salt (record : CapLowerRecord) :
    (capLowerEncoding record)[0]'(by rw [cap_lower_encoding_length]; decide) =
      record.salt := rfl

/-- Its next sixteen slots are the original supplied siblings in order. -/
theorem cap_lower_encoding_sibling (record : CapLowerRecord) (level : Fin 16) :
    (capLowerEncoding record)[level.val + 1]'(by
      rw [cap_lower_encoding_length]; omega) = record.sibling level := by
  simp only [capLowerEncoding, List.getElem_cons_succ, List.getElem_ofFn]
end CommitGolfCandidate
