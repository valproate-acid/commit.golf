import CommitGolfCandidate.TwoPermutationPentaSpec
import CommitGolfCandidate.TwoPermutationSyscall
import CommitGolfCandidate.TwoPermutationHeapInvariant
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! The aligned 200-byte workspace at word 1600 represents exactly `pentaInput`
of its five 32-byte slots when its first five words are zero. -/
namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 16384
set_option maxHeartbeats 1600000

/-- Word representation of the shared penta input, low word first. -/
def pentaInputWords (c : Fin 5 → BitVec 256) (i : Fin 25) : Word :=
  if h : i.val<5 then 0 else
    (c ⟨(i.val-5)/4,by have := i.isLt; omega⟩).extractLsb' (64*((i.val-5)%4)) 64

theorem penta_input_word (c : Fin 5 → BitVec 256) (i : Fin 25) :
    (pentaInput c).extractLsb' (64*i.val) 64=pentaInputWords c i := by
  fin_cases i
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 0) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 64) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 128) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 192) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_add_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 256) (len := 64) (by decide)).trans BitVec.extractLsb'_zero
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 320) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 0) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 384) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 64) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 448) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 128) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 512) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 192) (len := 64) (by decide)))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 256) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 0) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 320) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 64) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 384) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 128) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 768) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 448) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 192) (len := 64) (by decide))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 832) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 512) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 256) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 0) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 896) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 320) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 64) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 960) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 384) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 128) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1024) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 448) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 192) (len := 64) (by decide)))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1088) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 768) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 512) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 256) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4) (xlo := c 3)
        (start := 0) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1152) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 832) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 320) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4) (xlo := c 3)
        (start := 64) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1216) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 896) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 384) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4) (xlo := c 3)
        (start := 128) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1280) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 960) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 448) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_add_le (xhi := c 4) (xlo := c 3)
        (start := 192) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1344) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 1024) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 768) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 512) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4) (xlo := c 3)
        (start := 256) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1408) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 1088) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 832) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 576) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4) (xlo := c 3)
        (start := 320) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1472) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 1152) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 896) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 640) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4) (xlo := c 3)
        (start := 384) (len := 64) (by decide))))))
  · exact (BitVec.extractLsb'_append_eq_of_le (xhi := (((c 4 ++ c 3) ++ c 2) ++ c 1) ++ c 0) (xlo := (0#320))
        (start := 1536) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := ((c 4 ++ c 3) ++ c 2) ++ c 1) (xlo := c 0)
        (start := 1216) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := (c 4 ++ c 3) ++ c 2) (xlo := c 1)
        (start := 960) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4 ++ c 3) (xlo := c 2)
        (start := 704) (len := 64) (by decide)).trans ((BitVec.extractLsb'_append_eq_of_le (xhi := c 4) (xlo := c 3)
        (start := 448) (len := 64) (by decide))))))

/-- Children as present in the actual workspace, in slot order. -/
def levelChildren (s : MachineState) : Fin 5 → BitVec 256 :=
  fun t => readBuffer s (12840+32*t.val) 32

theorem workspace_penta_input (s : MachineState)
    (zeros : ∀ i<5, memoryView s (1600+i)=0) :
    packBuffer (window (memoryView s) 1600)=pentaInput (levelChildren s) := by
  rw [←read_permutation_window]
  apply aligned_buffer_eq s 1600 200 (by decide)
  intro k bound
  let i : Fin 25 := ⟨k,bound⟩
  refine Eq.trans ?_ (penta_input_word (levelChildren s) i).symm
  change memoryView s (1600+i.val)=pentaInputWords (levelChildren s) i
  unfold pentaInputWords
  split
  · exact zeros _ (by assumption)
  · rename_i h
    rw [levelChildren,read_digest_word _ _ _ (by omega) (by omega)]
    dsimp only [Fin.val_mk]
    change s.getMem (wordAddress (1600+i.val))=s.getMem (BitVec.ofNat 64 _)
    congr 2
    unfold wordAddress
    congr 1
    omega

end TwoPermutationPrototype.Quad.Checker
