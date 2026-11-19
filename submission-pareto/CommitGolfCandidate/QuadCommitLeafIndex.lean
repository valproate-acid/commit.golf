import CommitGolfCandidate.QuadCommitLeafFetch

/-! Closed program counters and exact instruction counts for the leaf body. -/
namespace TwoPermutationPrototype.Quad.Commit.Leaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def heapExtra (u : Nat) : Nat := if u%45=44 then 1 else 0
def nonceExtra (u : Nat) : Nat := if u%256=127 then 1 else 0
def adjustExtra (u : Nat) : Nat := if u=4095 then 1 else 0
def extra (u : Nat) : Nat := heapExtra u + nonceExtra u + adjustExtra u

theorem leaf_word_count (u : Nat) : (leafWords u).length = 11+extra u := by
  simp only [leafWords,List.length_append,List.length_cons,List.length_nil,extra,heapExtra,nonceExtra,adjustExtra]
  split_ifs <;> simp_all

attribute [local irreducible] leafWords

theorem leaf_index_next (u : Nat) : leafIndex (u+1) = leafIndex u+11+extra u := by
  unfold leafIndex
  rw [List.range_succ,List.flatMap_append,List.length_append]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,leaf_word_count]
  omega

theorem extra_count (u : Nat) (inside : u<4096) :
    (u+1)/45+(u+1+128)/256+(if u+1=4096 then 1 else 0) = u/45+(u+128)/256+extra u := by
  unfold extra heapExtra nonceExtra adjustExtra
  split_ifs <;> omega

theorem leaf_index_formula (u : Nat) (inside : u≤4096) :
    leafIndex u = 19+11*u+u/45+(u+128)/256+(if u=4096 then 1 else 0) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    have bound : u<4096 := by omega
    have old := ih (by omega)
    have count := extra_count u bound
    rw [leaf_index_next,old,if_neg (by omega)]
    omega

theorem leaf_body_end : leafIndex 4096 = 45183 := by
  rw [leaf_index_formula 4096 (by omega)]
  decide

theorem leaf_code_word_count : leafCode.length = 45164 := by
  change ((List.range 4096).flatMap leafWords).length = 45164
  have endIndex := leaf_body_end
  unfold leafIndex at endIndex
  omega

end TwoPermutationPrototype.Quad.Commit.Leaves
