import CommitGolfCandidate.TwoPermutationAllLeaves

/-! An ascending heap invariant for the full leaf phase. Each completed 32-byte
digest agrees with the original input and nonce tape under the fixed permutation. -/
namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure check_evaluation_support)
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

def finalReply (oracle : Oracle) (mem : Memory) (i : Nat) : BitVec 1600 :=
  let msg := window mem (leafStart i+5)
  let salt := window mem (leafSalt i)
  let a := oracle.permutation (packBuffer (firstInput i salt msg))
  oracle.permutation (packBuffer (secondInput i (replyWords a) msg))

theorem final_reply_rows (oracle : Oracle) (mem : Memory) (i : Index) :
    finalReply oracle mem i.val =
      (secondRow oracle.permutation i (window mem (leafStart i.val+5))
        (firstRow oracle.permutation i (window mem (leafSalt i.val)) (window mem (leafStart i.val+5))).2).2 := rfl

structure LeafPrefix (oracle : Oracle) (before : Memory) (s : MachineState) (count : Nat) : Prop where
  digests : ∀ i < count, (window (memoryView s) (leafDest i) : Words 4) =
    lowDigest (replyWords (finalReply oracle before i))
  messages : ∀ i, count ≤ i → i < 2^24 → (window (memoryView s) (leafStart i+5) : Words 32) =
    window before (leafStart i+5)
  salts : ∀ i < 2^24, (window (memoryView s) (leafSalt i) : Words 2) = window before (leafSalt i)

theorem empty_leaf_prefix (oracle : Oracle) (s : MachineState) : LeafPrefix oracle (memoryView s) s 0 :=
  ⟨fun _ impossible => False.elim (by omega),fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem nonce_memory_window (s : MachineState) (g : Nat) (slot : Fin 16) (r : ProductionRegs s g slot) :
    nonceWords s slot = window (memoryView s) (leafSalt (16*g+slot.val)) := by
  funext k
  fin_cases k <;> simp only [nonceWords,window,memoryView,r.salts] <;> dsimp <;>
    congr 1 <;> simp only [wordAddress,← BitVec.ofNat_add] <;> congr 1 <;> unfold leafSalt <;> omega

theorem production_prefix_step (oracle : Oracle) (before : Memory) (s : MachineState) (g : Nat) (u : Fin 16)
    (bound : g < 2^20) (r : ProductionRegs s g u) (inv : LeafPrefix oracle before s (16*g+u.val)) :
    let i := 16*g+u.val
    let next := (checkEvaluation oracle (leafTrace s u (leafStart i) i (leafDest i))).1
    LeafPrefix oracle before next (i+1) := by
  let i := 16*g+u.val
  have inside : i < 2^24 := by dsimp [i]; have := u.isLt; omega
  let idx : Index := ⟨i, by exact inside⟩
  let msg := (window (memoryView s) (leafStart i+5) : Words 32)
  let a := (firstRow oracle.permutation idx (nonceWords s u) msg).2
  let b := (secondRow oracle.permutation idx msg a).2
  have response : b = finalReply oracle before i := by
    change oracle.permutation (packBuffer (secondInput i (replyWords (oracle.permutation
      (packBuffer (firstInput i (nonceWords s u) msg)))) msg)) = _
    rw [nonce_memory_window s g u r, inv.salts i inside]
    dsimp only [msg]
    rw [inv.messages i (by omega) inside]
    rfl
  have step := production_fixed_leaf oracle s g u bound r
  have spill := production_leaf_spill s g u bound r a b
  change checkEvaluation oracle (leafTrace s u (leafStart i) i (leafDest i)) =
    (finishedLeaf s u (leafStart i) (leafDest i) a b,2) at step
  dsimp only
  rw [step]
  refine ⟨?_,?_,?_⟩
  · intro j hj
    by_cases last : j = i
    · subst j
      exact spill.1.trans (congrArg (fun x => lowDigest (replyWords x)) response)
    · have h : j < i := by change j < i+1 at hj; omega
      apply Eq.trans _ (inv.digests j h)
      funext k
      exact spill.2.1 j h k.val k.isLt
  · intro j later limit
    apply Eq.trans _ (inv.messages j (by change i+1 ≤ j at later; omega) limit)
    funext k
    exact spill.2.2.1 j (by change i+1 ≤ j at later; omega) limit k.val k.isLt
  · intro j limit
    apply Eq.trans _ (inv.salts j limit)
    funext k
    exact spill.2.2.2.1 j limit k.val k.isLt

theorem slot_prefix_step (oracle : Oracle) (before : Memory) (s : MachineState) (g u : Nat)
    (bound : g < 2^20) (hu : u < 16) (r : GroupRegs s g u) (inv : LeafPrefix oracle before s (16*g+u)) :
    LeafPrefix oracle before (checkEvaluation oracle (slotTrace s g u)).1 (16*g+u+1) := by
  have eq : (groupSlot u).val = u := Nat.mod_eq_of_lt hu
  have prev : LeafPrefix oracle before s (16*g+(groupSlot u).val) := by rw [eq];exact inv
  simpa only [slotTrace,eq] using production_prefix_step oracle before s g (groupSlot u) bound (group_prod_regs r hu) prev

theorem group_prefix (oracle : Oracle) (before : Memory) (g count u : Nat) (s : MachineState)
    (bound : g < 2^20) (inner : u+count ≤ 16) (r : GroupRegs s g u) (inv : LeafPrefix oracle before s (16*g+u)) :
    LeafPrefix oracle before (checkEvaluation oracle (groupTrace g count u s)).1 (16*g+u+count) := by
  induction count generalizing u s with
  | zero => simpa only [groupTrace,check_evaluation_pure,Nat.add_zero] using inv
  | succ k ih =>
    simp only [groupTrace,check_evaluation_bind]
    have step := slot_prefix_step oracle before s g u bound (by omega) r inv
    have regs := trace_advance_regs bound (by omega : u < 16) r (check_evaluation_support oracle (slotTrace s g u))
    rw [show 16*g+u+(k+1) = 16*g+(u+1)+k by omega]
    exact ih (u+1) _ (by omega) regs (by simpa only [← Nat.add_assoc] using step)

theorem batch_prefix (oracle : Oracle) (before : Memory) (g : Nat) (s : MachineState)
    (bound : g < 2^20) (r : GroupRegs s g 0) (inv : LeafPrefix oracle before s (16*g)) :
    LeafPrefix oracle before (checkEvaluation oracle (batchTrace g s)).1 (16*(g+1)) := by
  simp only [batchTrace,check_evaluation_bind,check_evaluation_pure]
  rw [show 16*(g+1)=16*g+0+16 by omega]
  have body := group_prefix oracle before g 16 0 s bound (by decide) r inv
  exact ⟨body.digests,body.messages,body.salts⟩

theorem all_leaves_prefix (oracle : Oracle) (before : Memory) (groups g : Nat) (s : MachineState)
    (bound : g+groups ≤ 2^20) (r : 0<groups → GroupRegs s g 0)
    (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) (inv : LeafPrefix oracle before s (16*g)) :
    LeafPrefix oracle before (checkEvaluation oracle (leavesTrace groups g s)).1 (16*(g+groups)) := by
  induction groups generalizing g s with
  | zero => simpa only [leavesTrace,check_evaluation_pure,Nat.add_zero] using inv
  | succ k ih =>
    simp only [leavesTrace,check_evaluation_bind]
    have valid := r (by omega)
    have step := batch_prefix oracle before g s (by omega) valid inv
    obtain ⟨next,endReg,_⟩ := batch_next g s (by omega) valid stop (check_evaluation_support oracle (batchTrace g s))
    rw [show g+(k+1)=g+1+k by omega]
    exact ih (g+1) _ (by omega) (fun more => next (by omega)) endReg step

theorem production_leaf_outputs (oracle : Oracle) (s : MachineState) (r : GroupRegs s 0 0)
    (stop : s.getReg .x21 = wordAddress (leafDest (2^24))) :
    LeafPrefix oracle (memoryView s) (checkEvaluation oracle (leavesTrace (2^20) 0 s)).1 (2^24) :=
  all_leaves_prefix oracle (memoryView s) (2^20) 0 s (by decide) (fun _ => r) stop (empty_leaf_prefix oracle s)

end TwoPermutationPrototype.RV64
