import CommitGolfCandidate.TwoPermutationPackedCapVisit
import CommitGolfCandidate.TwoPermutationPackedCapFrontier
import CommitGolfCandidate.TwoPermutationPackedPaths
import CommitGolfCandidate.TwoPermutationPackedCapBytes
import CommitGolfCandidate.TwoPermutationCheckerCapCounts

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.Checker (capRootAt capHashCount)

/-- A subtree preserves all previous root slots, all marks, the proof input,
and all marked leaves. This also covers the left sibling during a right visit. -/
def CapRetained (groups : List Nat) (node word : Nat) : Prop :=
  word < 2048+4*node ∨ 4096 ≤ word ∨
    ∃ leaf ∈ groups, 256 ≤ leaf ∧ leaf < 512 ∧ 2048+4*leaf ≤ word ∧ word < 2048+4*leaf+4

def CapFrame (groups : List Nat) (node : Nat) (before after : MachineState) : Prop :=
  ∀ word < 2^61, CapRetained groups node word → memoryView after word = memoryView before word

theorem CapRetained.later {groups : List Nat} {node next word : Nat} (seen : CapRetained groups node word)
    (order : node ≤ next) : CapRetained groups next word := by
  rcases seen with prior | external | marked
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl external)
  · exact Or.inr (Or.inr marked)

theorem CapFrame.join {groups : List Nat} {node a b : Nat} {start middle finish : MachineState}
    (first : CapFrame groups a start middle) (last : CapFrame groups b middle finish)
    (firstOrder : node ≤ a) (lastOrder : node ≤ b) : CapFrame groups node start finish :=
  fun word bound keep => (last word bound (keep.later lastOrder)).trans (first word bound (keep.later firstOrder))

theorem cap_retained_digest {groups : List Nat} {node : Nat} {before after : MachineState}
    (frame : CapFrame groups node before after) (root : Nat) (bounded : root < 512)
    (keep : root < node ∨ (root ∈ groups ∧ 256 ≤ root)) :
    capRootAt after root = capRootAt before root := by
  unfold capRootAt
  apply read_digest_congr _ _ _ (by omega)
  intro word small
  simp only [← Nat.mul_add]
  change memoryView after (2048+4*root+word) = memoryView before (2048+4*root+word)
  apply frame _ (by omega)
  rcases keep with ancestor | ⟨marked, leaf⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inr ⟨root, marked, leaf, bounded, by omega, by omega⟩)

structure CapContents (groups : List Nat) (before : MachineState)
    (node height pointer : Nat) (heap : Nat → BitVec 256) : Prop where
  leaves : ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 → leaf/2^height = node →
    capRootAt before leaf = heap leaf
  frontier : ∀ i (bounded : i < (capFrontierNodes groups node height).length),
    (0#16 ++ readBuffer before (pointer+30*i) 30) = heap ((capFrontierNodes groups node height)[i])

def CapHeapCorrect (oracle : Oracle) (heap : Nat → BitVec 256) : Prop :=
  ∀ node, 0 < node → node < 256 → heap node =
    padLow (oracle.compression (heap (2*node+1) ++ heap (2*node)))

structure CapWalkResult (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (node height pointer : Nat) where
  state : MachineState
  segment : Segment oracle before state
  done : Bool
  outPointer : Nat
  pc : state.pc = if done then 0x1528 else 0x15b0
  position : done = true → CapPosition groups state node outPointer
  readLength : done = true → outPointer = pointer + 30*(capFrontierNodes groups node height).length
  steps : segment.steps ≤ 44*(2^(height+1)-1)
  calls : segment.rows.length ≤ capHashCount groups node height
  stable : CapStable before state
  frame : CapFrame groups node before state
  authentic : done = true → ∀ leaf ∈ groups, 256 ≤ leaf → leaf < 512 → leaf / 2^height = node →
    ProjectedPath segment.rows leaf height (capRootAt before leaf) (capRootAt state node)
  available : pointer + 30*(capFrontierNodes groups node height).length ≤
    (before.getReg .x22).toNat → done = true
  realizes : done = true → ∀ heap, CapHeapCorrect oracle heap →
    CapContents groups before node height pointer heap → capRootAt state node = heap node

private theorem mark_of_group (groups : List Nat) (node height group : Nat)
    (active : group ∈ groups) (belongs : group/2^height = node) :
    capIsMarked groups node height = true := by
  simp only [capIsMarked, List.any_eq_true, beq_iff_eq]
  exact ⟨group, active, belongs⟩

def cap_walk_known_leaf {groups : List Nat} {before : MachineState} {node pointer : Nat}
    (oracle : Oracle) (position : CapPosition groups before node pointer)
    (pc : before.pc = 0x147c) (span : Opening.CapSpan node 0)
    (marked : capIsMarked groups node 0 = true) : CapWalkResult oracle groups before node 0 pointer := by
  let after := capLookup before
  let segment := capLookupSegment oracle before node position.context.controls position.heap pc
    (Opening.cap_span_node node 0 span).2
  obtain ⟨target, nextPosition, mem⟩ := cap_lookup_position position span
  refine ⟨after, segment, true, pointer, by simpa [marked] using target,
    fun _ => by simpa [marked] using nextPosition, ?_, ?_, by simp [segment, capLookupSegment, Segment.ordinary, capHashCount],
    cap_lookup_stable before, fun word _ _ => congrFun mem _, ?_, fun _ => rfl, ?_⟩
  · intro _
    simp [capFrontierNodes, marked]
  · exact (cap_lookup_limit before).trans (by decide)
  · intro _ leaf _ _ _ belongs
    have atNode : leaf = node := by simpa using belongs
    subst leaf
    have stable : capRootAt after node = capRootAt before node := by
      unfold capRootAt
      exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun mem _)
    rw [stable]
    exact .done node _
  · intro _ heap _ contents
    have stable : capRootAt after node = capRootAt before node := by
      unfold capRootAt
      exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun mem _)
    rw [stable]
    have low := Opening.cap_span_is_leaf node span
    have high := (Opening.cap_span_node node 0 span).2
    have member : node ∈ groups := by
      simpa [capIsMarked, List.any_eq_true, beq_iff_eq] using marked
    exact contents.leaves node member low high (by simp)

private theorem unmarked_frontier (groups : List Nat) (node height : Nat)
    (unmarked : capIsMarked groups node height = false) :
    capFrontierNodes groups node height = [node] := by cases height <;> simp [capFrontierNodes, unmarked]

def cap_walk_frontier (codec : FrontierKernel) {groups : List Nat} {before : MachineState} {node height pointer : Nat}
    (oracle : Oracle) (position : CapPosition groups before node pointer)
    (pc : before.pc = 0x147c) (span : Opening.CapSpan node height)
    (unmarked : capIsMarked groups node height = false)
    (fitsMemory : pointer+30*(capFrontierNodes groups node height).length ≤ MEMORY_BYTES) :
    CapWalkResult oracle groups before node height pointer := by
  let looked := capLookup before
  let lookup := capLookupSegment oracle before node position.context.controls position.heap pc
    (Opening.cap_span_node node height span).2
  obtain ⟨target, nextPosition, mem⟩ := cap_lookup_position position span
  have lookPC : looked.pc = 0x1498 := by simpa [unmarked] using target
  have lookPos : CapPosition groups looked node pointer := by simpa [unmarked] using nextPosition
  have actual := unmarked_frontier groups node height unmarked
  have memoryRange : pointer+30 ≤ MEMORY_BYTES := by simpa [actual] using fitsMemory
  have ready : FrontierReady looked node pointer :=
    ⟨lookPC, lookPos.heap, lookPos.context.controls.roots, lookPos.proof,
      (Opening.cap_span_node node height span).2, lookPos.above, lookPos.even, memoryRange⟩
  have stepLimit : 44 ≤ 44*(2^(height+1)-1) := by
    have p : 2 ≤ 2^(height+1) := by rw [Nat.pow_succ]; have := Nat.one_le_pow height 2 (by decide); omega
    omega
  by_cases short : looked.getReg .x22 < looked.getReg .x21+30#64
  · let shortPath := Segment.ordinary oracle 4 4 (execute_frontier_prefix looked lookPC)
    let after := frontierPrefix looked 4
    have retain : CapStable looked after := by
      intro r found
      simp [capFixedRegisters] at found
      rcases found with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact frontier_prefix_register looked _ (by decide) (by decide)
    refine ⟨after, lookup.append shortPath, false, pointer,
      cap_short_frontier_reject looked lookPC short, by simp, by simp, ?_, ?_,
      (cap_lookup_stable before).trans retain, ?_, by simp, ?_, by simp⟩
    · have bound := cap_lookup_limit before
      change capLookupSteps before+4 ≤ _
      omega
    · change 0 ≤ _
      omega
    · intro word _ _
      exact (congrFun (frontier_prefix_post looked lookPC).2.2.2 _).trans (congrFun mem _)
    · intro enough
      have proofEnd := (cap_lookup_stable before) .x22 (by decide)
      change looked.getReg .x22 = _ at proofEnd
      have address : looked.getReg .x21+30#64 = BitVec.ofNat 64 (pointer+30) := by
        rw [ready.proofReg, BitVec.ofNat_add]
      rw [address, proofEnd] at short
      change (before.getReg .x22).toNat < (BitVec.ofNat 64 (pointer+30)).toNat at short
      have size : MEMORY_BYTES < 2^64 := by decide
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : pointer+30 < 2^64)] at short
      rw [actual] at enough
      simp only [List.length_singleton, Nat.mul_one] at enough
      omega
  · let after := codec.after looked
    let read := capFrontierSegment codec oracle ready short
    have stable := (cap_lookup_stable before).trans (cap_frontier_stable codec looked)
    refine ⟨after, lookup.append read, true, pointer+30, (codec.pointer looked node pointer ready).1,
      fun _ => cap_frontier_position codec lookPos ready short, ?_, ?_, ?_, stable, ?_, ?_, fun _ => rfl, ?_⟩
    · intro _
      simp [actual]
    · have bound := cap_lookup_limit before
      change capLookupSteps before+36 ≤ _
      omega
    · change 0 ≤ _
      omega
    · intro word bounded keep
      have outside : word < 2048+4*node ∨ 2048+4*node+4 ≤ word := by
        rcases keep with low | external | ⟨leaf, mark, large, small, start, finish⟩
        · exact Or.inl low
        · have := ready.below
          exact Or.inr (by omega)
        · have different : leaf ≠ node := by
            intro same
            subst leaf
            cases height with
            | zero =>
              have proof : node/2^0 = node := by simp
              rw [mark_of_group groups node 0 node mark proof] at unmarked
              contradiction
            | succ height =>
              have inside := Opening.cap_span_is_internal node height span
              omega
          omega
      exact (codec.frame looked node pointer ready short word bounded outside).trans (congrFun mem _)
    · intro _ leaf active _ _ belongs
      have marked := mark_of_group groups node height leaf active belongs
      rw [marked] at unmarked
      contradiction
    · intro _ heap _ contents
      have loaded := codec.digest looked node pointer ready short
      have memory : looked.mem = before.mem := mem
      have unchanged : readBuffer looked pointer 30 = readBuffer before pointer 30 := by
        simp only [readBuffer, MachineState.getByte, MachineState.getMem, memory]
      rw [loaded, unchanged]
      have first := contents.frontier 0 (by simp [actual])
      simpa [actual] using first

private theorem joined_parent_path {rows : List PublicRow} {node h leaf : Nat}
    {leafDigest childDigest sibling parent : BitVec 256}
    (child : ProjectedPath rows leaf h leafDigest childDigest)
    (branch : leaf/2^h = node)
    (recorded : PublicRow.compression (pathPair node childDigest sibling) parent ∈ rows) :
    ProjectedPath rows leaf (h+1) leafDigest (padLow parent) := by
  have edge : ProjectedPath rows node 1 childDigest (padLow parent) := .step recorded (.done (node/2) (padLow parent))
  exact child.append (by simpa only [branch] using edge)

private theorem child_scope (leaf node height : Nat) (inside : leaf/2^(height+1) = node) :
    leaf/2^height = 2*node ∨ leaf/2^height = 2*node+1 := by
  have divide : leaf/2^(height+1) = (leaf/2^height)/2 := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
  rw [divide] at inside
  omega

attribute [local irreducible] capLookup capRight capAfterTests capRootAt

theorem execute_cap_subtree (codec : FrontierKernel) (oracle : Oracle) (groups : List Nat) (before : MachineState)
    (node height pointer : Nat) (position : CapPosition groups before node pointer)
    (pc : before.pc = 0x147c) (span : Opening.CapSpan node height)
    (proofRoom : pointer+30*(capFrontierNodes groups node height).length ≤ MEMORY_BYTES) :
    Nonempty (CapWalkResult oracle groups before node height pointer) := by
  induction height generalizing before node pointer with
  | zero =>
    cases marked : capIsMarked groups node 0
    · exact ⟨cap_walk_frontier codec oracle position pc span marked proofRoom⟩
    · exact ⟨cap_walk_known_leaf oracle position pc span marked⟩
  | succ height ih =>
    cases marked : capIsMarked groups node (height+1)
    · exact ⟨cap_walk_frontier codec oracle position pc span marked proofRoom⟩
    · let looked := capLookup before
      let lookup := capLookupSegment oracle before node position.context.controls position.heap pc
        (Opening.cap_span_node node (height+1) span).2
      obtain ⟨lookupPC, lookupPos, lookupMem⟩ := cap_lookup_position position span
      have lpos : CapPosition groups looked (2*node) pointer := by simpa [marked] using lookupPos
      have lpc : looked.pc = 0x147c := by simpa [marked] using lookupPC
      obtain ⟨leftSpan, rightSpan⟩ := Opening.cap_span_children node height span
      let leftNodes := capFrontierNodes groups (2*node) height
      let rightNodes := capFrontierNodes groups (2*node+1) height
      have frontier : capFrontierNodes groups node (height+1) = leftNodes ++ rightNodes := by
        simp [capFrontierNodes, marked, leftNodes, rightNodes]
      have length := congrArg List.length frontier
      rw [List.length_append] at length
      rw [frontier, List.length_append, Nat.mul_add] at proofRoom
      have leftRoom : pointer+30*leftNodes.length ≤ MEMORY_BYTES := by omega
      obtain ⟨left⟩ := ih looked (2*node) pointer lpos lpc leftSpan leftRoom
      have preFrame : CapFrame groups node before looked := fun _ _ _ => congrFun lookupMem _
      have leftFrame := preFrame.join left.frame (Nat.le_refl _) (by omega)
      have preStable := (cap_lookup_stable before).trans left.stable
      have leftFuel := left.steps
      have lookupFuel := cap_lookup_limit before
      have spread : 2^(height+1)-1 + (2^(height+1)-1) + 1 = 2^(height+1+1)-1 := by
        rw [Nat.pow_succ 2 (height+1)]
        have : 0 < 2^(height+1) := by positivity
        omega
      have budget : capHashCount groups node (height+1) =
          1+capHashCount groups (2*node) height+capHashCount groups (2*node+1) height := by
        simp [capHashCount, marked]
      have leftCalls := left.calls
      have nodePositive := (Opening.cap_span_node node (height+1) span).1
      by_cases leftDone : left.done = true
      · have endPC : left.state.pc = 0x1528 := by simpa [leftDone] using left.pc
        have endPointer := left.readLength leftDone
        change left.outPointer = pointer+30*leftNodes.length at endPointer
        obtain ⟨across, acrossSteps, acrossRows, rightPC, rightPos, acrossMem⟩ :=
          cap_next_sibling oracle (left.position leftDone) endPC
            ⟨nodePositive, (Opening.cap_span_node _ _ leftSpan).2⟩
        let middle := capRight (capAfterTests left.state)
        have rightRoom : left.outPointer+30*rightNodes.length ≤ MEMORY_BYTES := by omega
        obtain ⟨right⟩ := ih middle (2*node+1) left.outPointer rightPos rightPC rightSpan rightRoom
        let combined := ((lookup.append left.segment).append across).append right.segment
        have frameAcross : CapFrame groups node left.state middle := fun _ _ _ => congrFun acrossMem _
        have framePrefix := (leftFrame.join frameAcross (Nat.le_refl _) (Nat.le_refl _)).join
          right.frame (Nat.le_refl _) (by omega)
        have stableAcross := (cap_tests_stable left.state).trans (cap_right_stable (capAfterTests left.state))
        have stablePrefix := (preStable.trans stableAcross).trans right.stable
        have rightFuel := right.steps
        have rightCalls := right.calls
        have prefixSteps : combined.steps = capLookupSteps before + left.segment.steps + 6 + right.segment.steps := by
          simp only [combined, Segment.append, acrossSteps]
          rfl
        have prefixRows : combined.rows = left.segment.rows ++ right.segment.rows := by
          simp [combined, Segment.append, acrossRows, lookup, capLookupSegment, Segment.ordinary]
        by_cases rightDone : right.done = true
        · have returnPC : right.state.pc = 0x1528 := by simpa [rightDone] using right.pc
          let parent := cap_return_parent oracle (right.position rightDone) returnPC
            ⟨nodePositive, (Opening.cap_span_node _ _ rightSpan).2⟩
          let segment := combined.append parent.segment
          have parentFrame : CapFrame groups node right.state parent.state := by
            intro word limited retained
            apply parent.frame word limited
            rcases retained with earlier | outside | ⟨leaf, active, low, bound, start, finish⟩
            · exact Or.inl earlier
            · have internal := Opening.cap_span_is_internal node height span
              exact Or.inr (by omega)
            · have internal := Opening.cap_span_is_internal node height span
              exact Or.inr (by omega)
          refine ⟨⟨parent.state, segment, true, right.outPointer, parent.pc,
            fun _ => parent.position, ?_, ?_, ?_, stablePrefix.trans parent.stable,
            framePrefix.join parentFrame (Nat.le_refl _) (Nat.le_refl _), ?_, fun _ => rfl, ?_⟩⟩
          · intro _
            have rightRead := right.readLength rightDone
            change right.outPointer = left.outPointer+30*rightNodes.length at rightRead
            rw [frontier, List.length_append, Nat.mul_add]
            omega
          · change combined.steps+parent.segment.steps ≤ _
            rw [prefixSteps, parent.steps, ← spread]
            omega
          · change (combined.rows ++ parent.segment.rows).length ≤ _
            rw [prefixRows, parent.row, List.length_append, List.length_append, List.length_singleton, budget]
            omega
          · intro _ leaf group low high covered
            have lhs Row (member : Row ∈ left.segment.rows) : Row ∈ segment.rows := by
              change Row ∈ combined.rows ++ parent.segment.rows
              rw [prefixRows]
              exact List.mem_append_left _ (List.mem_append_left _ member)
            have rhs Row (member : Row ∈ right.segment.rows) : Row ∈ segment.rows := by
              change Row ∈ combined.rows ++ parent.segment.rows
              rw [prefixRows]
              exact List.mem_append_left _ (List.mem_append_right _ member)
            have row : .compression (capRootAt right.state (2*node+1) ++ capRootAt right.state (2*node))
                (oracle.compression (capRootAt right.state (2*node+1) ++ capRootAt right.state (2*node))) ∈ segment.rows := by
              change _ ∈ combined.rows ++ parent.segment.rows
              rw [parent.row]
              exact List.mem_append_right _ (by simp)
            rcases child_scope leaf node height covered with leftLeaf | rightLeaf
            · have recorded := (left.authentic leftDone leaf group low high leftLeaf).mono lhs
              have initial : capRootAt looked leaf = capRootAt before leaf := by
                unfold capRootAt
                exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun lookupMem _)
              have acrossDigest : capRootAt middle (2*node) = capRootAt left.state (2*node) := by
                unfold capRootAt
                exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun acrossMem _)
              have still := cap_retained_digest right.frame (2*node) (Opening.cap_span_node _ _ leftSpan).2
                (Or.inl (by omega : 2*node < 2*node+1))
              rw [initial, ← acrossDigest, ← still] at recorded
              rw [parent.digest]
              apply joined_parent_path recorded leftLeaf (sibling := capRootAt right.state (2*node+1))
              simpa [pathPair, show (2*node)%2 = 0 by omega] using row
            · have recorded := (right.authentic rightDone leaf group low high rightLeaf).mono rhs
              have beforeRight := leftFrame.join frameAcross (Nat.le_refl _) (Nat.le_refl _)
              rw [cap_retained_digest beforeRight leaf high (Or.inr ⟨group,low⟩)] at recorded
              rw [parent.digest]
              apply joined_parent_path recorded rightLeaf (sibling := capRootAt right.state (2*node))
              simpa [pathPair, show (2*node+1)%2 ≠ 0 by omega] using row
          · intro _ heap model contents
            have leftIn (leaf : Nat) (under : leaf/2^height = 2*node) : leaf/2^(height+1) = node := by
              rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, under]
              omega
            have rightIn (leaf : Nat) (under : leaf/2^height = 2*node+1) : leaf/2^(height+1) = node := by
              rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, under]
              omega
            have leftContents : CapContents groups looked (2*node) height pointer heap := by
              constructor
              · intro leaf group low high under
                have stable : capRootAt looked leaf = capRootAt before leaf := by
                  unfold capRootAt
                  exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun lookupMem _)
                rw [stable]
                exact contents.leaves leaf group low high (leftIn leaf under)
              · intro i high
                change i < leftNodes.length at high
                have indexHigh : i < (capFrontierNodes groups node (height+1)).length := by rw [length]; omega
                have expected := contents.frontier i indexHigh
                simp only [frontier, List.getElem_append_left (show i < leftNodes.length from high)] at expected
                have memory : looked.mem = before.mem := lookupMem
                have stable : readBuffer looked (pointer+30*i) 30 = readBuffer before (pointer+30*i) 30 := by
                  simp only [readBuffer, MachineState.getByte, MachineState.getMem, memory]
                rw [stable]
                exact expected
            have leftRoot := left.realizes leftDone heap model leftContents
            have beforeRight := leftFrame.join frameAcross (Nat.le_refl _) (Nat.le_refl _)
            have rightContents : CapContents groups middle (2*node+1) height left.outPointer heap := by
              constructor
              · intro leaf group low high under
                rw [cap_retained_digest beforeRight leaf high (Or.inr ⟨group,low⟩)]
                exact contents.leaves leaf group low high (rightIn leaf under)
              · intro i high
                change i < rightNodes.length at high
                have indexHigh : leftNodes.length+i < (capFrontierNodes groups node (height+1)).length := by
                  rw [length]
                  omega
                have expected := contents.frontier (leftNodes.length+i) indexHigh
                simp only [frontier, List.getElem_append_right (by omega : leftNodes.length ≤ leftNodes.length+i),
                  Nat.add_sub_cancel_left] at expected
                have word : left.outPointer+30*i = pointer+30*(leftNodes.length+i) := by omega
                have stable : readBuffer middle (left.outPointer+30*i) 30 =
                    readBuffer before (left.outPointer+30*i) 30 := by
                  have base := position.above
                  have spacious : MEMORY_BYTES < 2^64 := by decide
                  apply read_buffer_above before middle _ _ 4096 (by omega) (by omega)
                  intro digit after bounded
                  exact beforeRight _ bounded (Or.inr (Or.inl after))
                rw [stable, word]
                exact expected
            have rightRoot := right.realizes rightDone heap model rightContents
            have leftRetained := cap_retained_digest right.frame (2*node) (Opening.cap_span_node _ _ leftSpan).2
              (Or.inl (by omega : 2*node < 2*node+1))
            have leftAcross : capRootAt middle (2*node) = capRootAt left.state (2*node) := by
              unfold capRootAt
              exact read_digest_congr _ _ _ (by omega) (fun _ _ => congrFun acrossMem _)
            rw [parent.digest, rightRoot, leftRetained, leftAcross, leftRoot,
              ← model node nodePositive (Opening.cap_span_is_internal node height span)]
        · have failed : right.done = false := Bool.eq_false_iff.mpr rightDone
          refine ⟨⟨right.state, combined, false, right.outPointer, by simpa [failed] using right.pc,
            by simp, by simp, ?_, ?_, stablePrefix, framePrefix, by simp, ?_, by simp⟩⟩
          · rw [prefixSteps, ← spread]
            omega
          · rw [prefixRows, List.length_append, budget]
            omega
          · intro enough
            have endStable := (preStable.trans stableAcross) .x22 (by decide)
            change middle.getReg .x22 = before.getReg .x22 at endStable
            have rightEnough : left.outPointer+30*rightNodes.length ≤ (middle.getReg .x22).toNat := by
              rw [endStable, endPointer]
              rw [frontier, List.length_append] at enough
              omega
            exact False.elim (rightDone (right.available rightEnough))
      · have failed : left.done = false := Bool.eq_false_iff.mpr leftDone
        let segment := lookup.append left.segment
        refine ⟨⟨left.state, segment, false, left.outPointer, by simpa [failed] using left.pc,
          by simp, by simp, ?_, ?_, preStable, leftFrame, by simp, ?_, by simp⟩⟩
        · change capLookupSteps before+left.segment.steps ≤ _
          rw [← spread]
          omega
        · change left.segment.rows.length ≤ _
          rw [budget]
          omega
        · intro enough
          have endStable := (cap_lookup_stable before) .x22 (by decide)
          change looked.getReg .x22 = before.getReg .x22 at endStable
          have leftEnough : pointer+30*leftNodes.length ≤ (looked.getReg .x22).toNat := by
            rw [endStable]
            rw [frontier, List.length_append] at enough
            omega
          exact False.elim (leftDone (left.available leftEnough))

end TwoPermutationPrototype.Packed.Checker
