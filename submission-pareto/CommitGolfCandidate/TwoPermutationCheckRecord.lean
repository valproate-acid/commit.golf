import CommitGolfCandidate.TwoPermutationCheckerRecordSetup
import CommitGolfCandidate.TwoPermutationHonestLower
import CommitGolfCandidate.TwoPermutationCheckerLeafData

namespace TwoPermutationPrototype.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling

/-- Entry to one record, before loading its sorted index. Addresses count aligned words. -/
structure CheckRecordReady (state : MachineState) (source nonce : Nat) (index : Index) where
  pc : state.pc = 0x10cc
  indexAccess : accessValid (state.getReg .x8) 8 = true
  indexWord : state.getMem (state.getReg .x8) = BitVec.ofNat 64 index.val
  tagBase : state.getReg .x3 = 4056
  sourceAddress : state.getReg .x19 = wordAddress source
  nonceAddress : state.getReg .x21 = wordAddress nonce
  digestAddress : state.getReg .x23 = wordAddress 1536
  pairAddress : state.getReg .x24 = wordAddress 1568
  challengeLength : state.getReg .x20 = BitVec.ofNat 64 LENGTH
  selector : state.getReg .x5 = 0
  nonceAbove : 4096 ≤ nonce
  separate : source+37 ≤ nonce
  proofRoom : nonce+66 ≤ 2^33

def recordLeaf (oracle : Oracle) (state : MachineState) (source : Nat) (index : Index) :
    MachineState × List PublicRow :=
  (checkEvaluation oracle (recordRows (leafQueries (beginRecord state 6) source index))).1

def recordLower (oracle : Oracle) (state : MachineState) (source : Nat) (index : Index) : LowerResult :=
  lowerRun oracle 16 (beginLower (recordLeaf oracle state source index).1 5)

theorem record_leaf_ready {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) :
    LeafReady (beginRecord state 6) source nonce index :=
  record_setup_ready state source nonce index ready.pc ready.indexWord ready.tagBase ready.sourceAddress
    ready.nonceAddress ready.digestAddress ready.selector ready.separate (by have := ready.proofRoom; omega)

theorem record_leaf_view (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) :
    let leaf := recordLeaf oracle state source index
    leaf.1.pc = 0x111c ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x28 → r ≠ .x10 → r ≠ .x11 → r ≠ .x13 → r ≠ .x12 → r ≠ .x31 →
        leaf.1.getReg r = state.getReg r) ∧
      leaf.1.getReg .x6 = BitVec.ofNat 64 index.val ∧
      (∀ word < 2^33, (word < source ∨ source+25 ≤ word) → (word < 1536 ∨ 1561 ≤ word) →
        memoryView leaf.1 word = memoryView state word) := by
  dsimp only [recordLeaf]
  rw [checker_leaf_rows]
  dsimp only
  refine ⟨checker_leaf_finished_pc (record_leaf_ready ready) _ _, ?_, ?_, ?_⟩
  · intro r node tag input size kind dest temp
    exact (checker_leaf_preserved_register _ _ _ _ r input dest temp).trans
      (record_setup_register _ r node tag input size kind)
  · exact (checker_leaf_preserved_register _ _ _ _ .x6 (by decide) (by decide) (by decide)).trans
      ((record_setup_post state).1.trans ready.indexWord)
  · intro word bounded sourceOutside digestOutside
    rw [checker_leaf_frame (record_leaf_ready ready) _ _ word bounded sourceOutside digestOutside]
    exact congrFun (record_setup_mem state) _

theorem record_lower_ready (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) :
    let positioned := beginLower (recordLeaf oracle state source index).1 5
    LowerReady positioned (LENGTH+index.val) (nonce+2) ∧ positioned.getReg .x29 = 16 := by
  obtain ⟨pc, preserved, idx, _⟩ := record_leaf_view oracle ready
  let leaf := (recordLeaf oracle state source index).1
  let positioned := beginLower leaf 5
  obtain ⟨pointer, node, size, kind, counter, stepped⟩ := lower_setup_post leaf
  have frame (r : Reg) (a : r ≠ .x21) (b : r ≠ .x6) (c : r ≠ .x11) (d : r ≠ .x13)
      (e : r ≠ .x29) (f : r ≠ .x28) (g : r ≠ .x10) (h : r ≠ .x12) (j : r ≠ .x31) :
      positioned.getReg r = state.getReg r :=
    (lower_setup_register leaf r a b c d e).trans (preserved r b f g c d h j)
  have fixed (r : Reg) (a : r ≠ .x6) (b : r ≠ .x28) (c : r ≠ .x10) (d : r ≠ .x11)
      (e : r ≠ .x13) (f : r ≠ .x12) (g : r ≠ .x31) :
      leaf.getReg r = state.getReg r := preserved r a b c d e f g
  have room := ready.proofRoom
  have above := ready.nonceAbove
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, size, kind, by omega, by omega⟩, counter⟩
  · exact stepped.trans (congrArg (· + 20) pc)
  · calc
      _ = BitVec.ofNat 64 index.val + BitVec.ofNat 64 LENGTH := by
        rw [node, idx, fixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          ready.challengeLength]
      _ = _ := by rw [← BitVec.ofNat_add, Nat.add_comm]
  · calc
      _ = wordAddress nonce + wordAddress 2 := by
        rw [pointer, fixed _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          ready.nonceAddress]
        rfl
      _ = _ := (wordAddress_add nonce 2).symm
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ready.digestAddress
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ready.pairAddress
  · exact (frame _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans ready.selector

theorem record_lower_geometry (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) :
    let result := recordLower oracle state source index
    result.state.pc = 0x11d8 ∧
      result.state.getReg .x6 = BitVec.ofNat 64 (capGroup index) ∧
      result.state.getReg .x21 = wordAddress (nonce+66) := by
  obtain ⟨positioned, counter⟩ := record_lower_ready oracle ready
  have nodeBound : LENGTH+index.val < 2^64 := by
    have h := index.isLt
    change index.val < 16777216 at h
    change 16777216+index.val < 2^64
    omega
  have room := ready.proofRoom
  obtain ⟨_, pointer, node, _, pc⟩ :=
    lower_run_trace oracle 16 (by decide) (fun _ => positioned) nodeBound counter
      positioned.proofReg positioned.nodeReg (by omega)
  exact ⟨pc (by decide), node, pointer⟩

set_option maxHeartbeats 1000000 in
theorem execute_check_record (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) (fuel : Nat) :
    let leaf := recordLeaf oracle state source index
    let lower := recordLower oracle state source index
    let tail := checkEvaluation oracle (recordRows (execute checkerImage fuel lower.state false))
    checkEvaluation oracle (recordRows (execute checkerImage (25+lower.steps+fuel) state false)) =
      ((tail.1.1.charge (39+lower.cycles) 18, leaf.2 ++ lower.rows ++ tail.1.2), 18+tail.2) := by
  let initialized := beginRecord state 6
  let leaf := recordLeaf oracle state source index
  let lower := recordLower oracle state source index
  obtain ⟨positioned, counter⟩ := record_lower_ready oracle ready
  have room := ready.proofRoom
  have nodeBound : LENGTH+index.val < 2^64 := by
    have h := index.isLt
    change index.val < 16777216 at h
    change 16777216+index.val < 2^64
    omega
  dsimp only
  rw [show 25+lower.steps+fuel = 6+(14+(5+(lower.steps+fuel))) by omega,
    execute_record_setup state ready.pc _ ready.indexAccess]
  simp only [bind_pure_comp, check_recorded_map]
  rw [execute_checker_leaf (record_leaf_ready ready), check_recorded_bind]
  simp only [bind_pure_comp, check_recorded_map]
  have leafCount : (checkEvaluation oracle (recordRows (leafQueries initialized source index))).2 = 2 := by
    dsimp only [initialized]
    rw [checker_leaf_rows]
  have afterLeaf := (record_leaf_view oracle ready).1
  erw [execute_lower_setup leaf.1 afterLeaf]
  simp only [bind_pure_comp, check_recorded_map]
  erw [execute_lower_run oracle 16 (by decide) (fun _ => positioned) nodeBound counter (by omega)]
  simp only [leafCount, Execution.charge, List.append_assoc, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add]
  rfl

theorem check_record_steps (oracle : Oracle) (state : MachineState) (source : Nat) (index : Index) :
    25+(recordLower oracle state source index).steps ≤ 441 := by
  unfold recordLower
  have budget := lower_run_steps oracle 16 (beginLower (recordLeaf oracle state source index).1 5)
  omega

/-- Registers preserved by the record before cap-group insertion. -/
def RecordRegisterPreserved (reg : Reg) : Prop :=
  reg ∉ ([.x6, .x7, .x10, .x11, .x12, .x13, .x21, .x28, .x29, .x31] : List Reg)

theorem record_lower_frame (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) :
    let after := (recordLower oracle state source index).state
    (∀ r, RecordRegisterPreserved r → after.getReg r = state.getReg r) ∧
      (∀ word < 2^33, (word < source ∨ source+25 ≤ word) → (word < 1536 ∨ 1576 ≤ word) →
        memoryView after word = memoryView state word) := by
  obtain ⟨_, leafRegs, _, leafMem⟩ := record_leaf_view oracle ready
  obtain ⟨positioned, counter⟩ := record_lower_ready oracle ready
  have room := ready.proofRoom
  have indexBound : index.val < 16777216 := index.isLt
  have nodeBound : LENGTH+index.val < 2^64 := by change 16777216+index.val < 2^64; omega
  obtain ⟨lowerRegs, lowerMem⟩ := lower_run_frame oracle 16 (by decide) (fun _ => positioned)
    nodeBound counter (by omega)
  let leaf := (recordLeaf oracle state source index).1
  constructor
  · intro r kept
    have ⟨a, b, c, d, e, f, g, h, j, k⟩ : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧
        r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x21 ∧ r ≠ .x28 ∧ r ≠ .x29 ∧ r ≠ .x31 := by
      simpa only [RecordRegisterPreserved, List.mem_cons, List.not_mem_nil, or_false, not_or] using kept
    exact (lowerRegs r c e a g j k b).trans
      ((lower_setup_register leaf r g a d f j).trans (leafRegs r a h c d f e k))
  · intro word bounded outside scratch
    exact (lowerMem word (by omega) (by omega) (by omega)).trans
      ((congrFun (lower_setup_mem leaf) _).trans (leafMem word bounded outside (by omega)))

/-- The actual record supplies both leaf query rows and the path to its cap group. -/
structure RecordedLower (oracle : Oracle) (index : Index) (value : Entry) (groupRoot : BitVec 256)
    (rows : List PublicRow) where
  nonce : Words 2
  first : PublicRow.permutation
    (firstRow oracle.permutation index nonce (entryWords value)).1
    (firstRow oracle.permutation index nonce (entryWords value)).2 ∈ rows
  second : PublicRow.permutation
    (secondRow oracle.permutation index (entryWords value)
      (firstRow oracle.permutation index nonce (entryWords value)).2).1
    (secondRow oracle.permutation index (entryWords value)
      (firstRow oracle.permutation index nonce (entryWords value)).2).2 ∈ rows
  path : RecordedPath rows (LENGTH+index.val) 16
    (outputDigest (secondRow oracle.permutation index (entryWords value)
      (firstRow oracle.permutation index nonce (entryWords value)).2).2) groupRoot

def RecordedLower.mono {oracle : Oracle} {index : Index} {value : Entry} {groupRoot : BitVec 256}
    {before after : List PublicRow} (lower : RecordedLower oracle index value groupRoot before)
    (contains : ∀ row ∈ before, row ∈ after) : RecordedLower oracle index value groupRoot after :=
  ⟨lower.nonce, contains _ lower.first, contains _ lower.second, lower.path.mono contains⟩

def RecordedLower.join {oracle : Oracle} {index : Index} {value : Entry} {groupRoot : BitVec 256}
    {rows : List PublicRow} {root : Commitment} (lower : RecordedLower oracle index value groupRoot rows)
    (cap : RecordedPath rows (capGroup index) 8 groupRoot root) :
    RecordedOpening oracle index value root rows :=
  ⟨lower.nonce, lower.first, lower.second, lower.path.append cap⟩

theorem record_lower_evidence (oracle : Oracle) {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index) (value : Entry)
    (decoded : readBuffer state (8*(source+5)) 256 = value) :
    let leaf := recordLeaf oracle state source index
    let lower := recordLower oracle state source index
    Nonempty (RecordedLower oracle index value (readBuffer lower.state 12288 32) (leaf.2 ++ lower.rows)) := by
  let initial := beginRecord state 6
  let words := checkerNonce initial
  let first := firstRow oracle.permutation index words (entryWords value)
  let second := secondRow oracle.permutation index (entryWords value) first.2
  let leaf := recordLeaf oracle state source index
  let lower := recordLower oracle state source index
  let final := secondReplyState initial source first.2 second.2
  have wordData : window (memoryView initial) (source+5) = entryWords value :=
    checker_value_data (fun _ => value) index
      ((read_buffer_memory_congr _ _ (record_setup_mem state) _ _).trans decoded)
  have observed : leaf = (final, [.permutation first.1 first.2, .permutation second.1 second.2]) := by
    change (checkEvaluation oracle (recordRows (leafQueries initial source index))).1 = _
    rw [checker_leaf_rows]
    dsimp only
    exact congrArg
      (fun w =>
        let a := firstRow oracle.permutation index words w
        let b := secondRow oracle.permutation index w a.2
        (secondReplyState initial source a.2 b.2,
          [PublicRow.permutation a.1 a.2, PublicRow.permutation b.1 b.2])) wordData
  obtain ⟨positioned, counter⟩ := record_lower_ready oracle ready
  have room := ready.proofRoom
  have indexBound : index.val < 16777216 := index.isLt
  have nodeBound : LENGTH+index.val < 2^64 := by change 16777216+index.val < 2^64; omega
  have trace := (lower_run_trace oracle 16 (by decide) (fun _ => positioned) nodeBound counter
      positioned.proofReg positioned.nodeReg (by omega)).1
  have startDigest : readBuffer (beginLower leaf.1 5) 12288 32 = outputDigest second.2 := by
    rw [read_buffer_memory_congr _ _ (lower_setup_mem leaf.1) _ _, observed]
    exact checker_leaf_digest _ _ _ _
  change Nonempty (RecordedLower oracle index value (readBuffer lower.state 12288 32) (leaf.2 ++ lower.rows))
  refine ⟨⟨words, ?_, ?_, ?_⟩⟩
  · apply List.mem_append_left
    rw [observed]
    exact List.mem_cons_self
  · apply List.mem_append_left
    rw [observed]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · change RecordedPath lower.rows (LENGTH+index.val) 16
      (readBuffer (beginLower leaf.1 5) 12288 32) (readBuffer lower.state 12288 32) at trace
    rw [startDigest] at trace
    exact trace.mono (fun _ found => List.mem_append_right _ found)

/-- A complete honest record produces its canonical root before the group comparison. -/
theorem honest_record_group (oracle : Oracle) (message : Message) (salts : CompleteSaltTape)
    {state : MachineState} {source nonce : Nat} {index : Index}
    (ready : CheckRecordReady state source nonce index)
    (saltData : readBuffer state (8*nonce) 16 = salts index)
    (valueData : readBuffer state (8*(source+5)) 256 = message index)
    (siblings : ∀ offset < 16, readBuffer state (8*(nonce+2+4*offset)) 32 =
      transcriptHeap false oracle.compression
        (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts)
        (((LENGTH+index.val)/2^offset) ^^^ 1)) :
    readBuffer (recordLower oracle state source index).state 12288 32 =
      transcriptHeap false oracle.compression
        (fullLeafDigests (BiPermutation.equiv Block oracle.permutation) message salts) (capGroup index) := by
  let leaf := (recordLeaf oracle state source index).1
  let positioned := beginLower leaf 5
  have room := ready.proofRoom
  have separate := ready.separate
  have above := ready.nonceAbove
  have memory := record_setup_mem state
  have leafDigest := honest_leaf_digest oracle message salts (record_leaf_ready ready)
    ((read_buffer_memory_congr _ _ memory _ _).trans saltData)
    ((read_buffer_memory_congr _ _ memory _ _).trans valueData)
  obtain ⟨lowerReady, counter⟩ := record_lower_ready oracle ready
  have leafFrame := (record_leaf_view oracle ready).2.2.2
  apply honest_lower_record oracle _ index lowerReady counter (by omega)
  · exact (read_buffer_memory_congr _ _ (lower_setup_mem leaf) _ _).trans leafDigest
  · intro offset inside
    exact (read_buffer_memory_congr _ _ (lower_setup_mem leaf) _ _).trans
      ((aligned_digest_frame state leaf _ fun k hk => leafFrame _ (by omega) (Or.inr (by omega))
        (Or.inr (by omega))).trans (siblings offset inside))

end TwoPermutationPrototype.Checker
