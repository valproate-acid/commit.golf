import CommitGolfCandidate.TwoPermutationHeapInvariant

namespace TwoPermutationPrototype.RV64.PackedLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def rawPrefix (message : Words 32) : Words 25 := fun i => message ⟨i.val,by omega⟩

def pinnedWords (tag : Word) (nonce : Words 2) (reply : Words 25) (message : Words 32) : Words 25 :=
  fun i => if i.val=0 then tag else if h : i.val<3 then nonce ⟨i.val-1,by omega⟩
    else if h : i.val<14 then reply ⟨i.val+11,by omega⟩ else message ⟨i.val+7,by omega⟩

def stamp (mem : Memory) (start : Nat) (tag : Word) (nonce : Words 2) : Memory :=
  writeWord (writeWord (writeWord mem (start+12) tag) (start+13) (nonce 0)) (start+14) (nonce 1)

def pinnedWrites (mem : Memory) (tag : Word) (nonce : Words 2) (start dst : Nat) (a b : BitVec 1600) : Memory :=
  writeWindow (stamp (writeWindow mem (start+1) (replyWords a)) start tag nonce) dst (replyWords b)

theorem raw_first_window (mem : Memory) (start : Nat) :
    window mem (start+5) = rawPrefix (window mem (start+5)) := rfl

theorem pinned_second_window (mem : Memory) (start : Nat) (tag : Word) (nonce : Words 2) (reply : Words 25) :
    window (stamp (writeWindow mem (start+1) reply) start tag nonce) (start+12) =
      pinnedWords tag nonce reply (window mem (start+5)) := by
  funext i
  by_cases hdr : i.val < 3
  · have cases3 : i.val=0 ∨ i.val=1 ∨ i.val=2 := by omega
    rcases cases3 with h|h|h <;>
      simp [pinnedWords,window,stamp,writeWord,h,Nat.add_assoc,show (⟨0,by decide⟩ : Fin 2)=0 from rfl,
        show (⟨1,by decide⟩ : Fin 2)=1 from rfl]
  · have n0 : i.val≠0 := by omega
    have a : start+12+i.val≠start+12 := by omega
    have b : start+12+i.val≠start+13 := by omega
    have c : start+12+i.val≠start+14 := by omega
    simp only [window,stamp,writeWord,a,b,c,ite_false,pinnedWords,n0,hdr,dite_false]
    by_cases h : i.val < 14
    · have val : start+1 ≤ start+12+i.val ∧ start+12+i.val < start+1+25 := by omega
      have pos : start+12+i.val-(start+1)=i.val+11 := by omega
      simp [writeWindow,h,val,pos]
    · have val : ¬(start+1 ≤ start+12+i.val ∧ start+12+i.val < start+1+25) := by omega
      simp only [writeWindow,h,val,dite_false]
      congr 1 <;> omega

theorem pinned_digest_words (mem : Memory) (tag : Word) (nonce : Words 2) (start dst : Nat) (a b : BitVec 1600) :
    window (pinnedWrites mem tag nonce start dst a b) dst = lowDigest (replyWords b) := by
  funext i
  have val : dst ≤ dst+i.val ∧ dst+i.val<dst+25 := by have := i.isLt; omega
  simp [pinnedWrites,window,writeWindow,lowDigest,val]

theorem pinned_word_outside (mem : Memory) (tag : Word) (nonce : Words 2) (start dst w : Nat) (a b : BitVec 1600)
    (sourceOut : w<start+1 ∨ start+26≤w) (heapOut : w<dst ∨ dst+25≤w) :
    pinnedWrites mem tag nonce start dst a b w=mem w := by
  have d : ¬(dst≤w ∧ w<dst+25) := by omega
  have m : ¬(start+1≤w ∧ w<start+1+25) := by omega
  have p : w≠start+12 := by omega
  have q : w≠start+13 := by omega
  have r : w≠start+14 := by omega
  simp only [pinnedWrites,writeWindow,stamp,writeWord,d,m,p,q,r,dite_false,ite_false]
end TwoPermutationPrototype.RV64.PackedLeaves
