import CommitGolfCandidate.TwoPermutationTaglessEvents
import CommitGolfCandidate.TwoPermutationHidingTwoStage

namespace TwoPermutationPrototype.Sampling
open CommitGolf OracleComp MeasureTheory CommitGolfCandidate
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
set_option exponentiation.threshold 2048

def taglessFirstAddress (messages : Index → Words 32) (salts : Index → BitVec 128)
    (index : Index) : Block :=
  hiddenFirstInput index (messages index) (salts index)

def taglessSecondAddress (messages : Index → Words 32) (index : Index) (reply : Block) : Block :=
  taglessSecondBlock reply (taglessMessageTail (messages index))

def taglessLeafPlans (messages : Index → Words 32) (salts : Index → BitVec 128) :
    List Index → List InputPlan
  | [] => []
  | index :: rest =>
    (fun _ => taglessFirstAddress messages salts index) ::
      (fun answers => taglessSecondAddress messages index (answers.headD 0)) ::
      taglessLeafPlans messages salts rest

@[simp] theorem tagless_leaf_plans_length (messages : Index → Words 32)
    (salts : Index → BitVec 128) (indices : List Index) :
    (taglessLeafPlans messages salts indices).length = 2 * indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih => simp only [taglessLeafPlans, List.length_cons, ih]; omega

theorem tagless_first_address_domain (messages : Index → Words 32) (salts : Index → BitVec 128)
    (index : Index) : taglessFirstAddress messages salts index ∈ firstDomain :=
  packed_first_domain index (saltWords (salts index)) (messages index)

theorem tagless_first_address_injective (messages : Index → Words 32) (salts : Index → BitVec 128) :
    Function.Injective (taglessFirstAddress messages salts) := by
  intro left right same
  apply hidden_first_tag_indices
  have eq := congrArg (fun address : Block => address.extractLsb' 0 64) same
  simpa only [taglessFirstAddress, hidden_first_tag] using eq

structure TaglessOpenedResult where
  replies : List Block
  cache : Cache
  bad : Bool

noncomputable def runTaglessOpened (messages : Index → Words 32) (salts : Index → BitVec 128)
    (cache : Cache) (replies : List Block) : List Index → ProbComp TaglessOpenedResult
  | [] => pure ⟨replies, cache, false⟩
  | index :: rest => by
    classical
    exact do
      let a ← cache.forward (taglessFirstAddress messages salts index)
      let address := taglessSecondAddress messages index a.1
      let b ← a.2.forward address
      let tail ← runTaglessOpened messages salts b.2 (b.1 :: a.1 :: replies) rest
      pure { tail with bad := decide (address ∈ firstDomain) || tail.bad }

private theorem tagless_opened_bind {α : Type} (messages : Index → Words 32)
    (salts : Index → BitVec 128) (cache : Cache) (replies : List Block) (indices : List Index)
    (next : (List Block × Cache) → ProbComp α) :
    (runTaglessOpened messages salts cache replies indices >>= fun result => next (result.replies, result.cache)) =ᵈ
      (runPrepared cache replies (taglessLeafPlans messages salts indices) >>= next) := by
  induction indices generalizing cache replies with
  | nil => simp [runTaglessOpened, taglessLeafPlans, runPrepared]
  | cons index rest ih =>
    simp only [runTaglessOpened, taglessLeafPlans, runPrepared, bind_assoc, pure_bind, List.headD_cons]
    apply EvalDistEq.bind_right
    intro a
    apply EvalDistEq.bind_right
    intro b
    exact ih b.2 (b.1 :: a.1 :: replies)

theorem tagless_opened_posterior {α : Type} (messages : Index → Words 32)
    (salts : Index → BitVec 128) (cache : Cache) (replies : List Block) (indices : List Index)
    (next : List Block → BiPermutation Block → ProbComp α) :
    (do let permutation ← cache.sample
        runPlanned next permutation.val replies (taglessLeafPlans messages salts indices)) =ᵈ
      (do let result ← runTaglessOpened messages salts cache replies indices
          let permutation ← result.cache.sample
          next result.replies permutation.val) :=
  (prepared_posterior_equivalence next cache replies _).trans
    (tagless_opened_bind messages salts cache replies indices (fun settled =>
      settled.2.sample >>= fun p => next settled.1 p.val)).symm

theorem tagless_forward_step_rows (cache : Cache) (input : Block) (result : Block × Cache)
    (present : result ∈ support (cache.forward input)) :
    result.2.entries = cache.entries ∨ result.2.entries = (input, result.1) :: cache.entries := by
  unfold PermutationCache.forward at present
  split at present
  · obtain ⟨reply, _, same⟩ := (mem_support_bind_iff _ _ _).mp present
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    exact Or.inr rfl
  · simp only [support_pure, Set.mem_singleton_iff] at present
    subst result
    exact Or.inl rfl

theorem tagless_forward_step_room (cache : Cache) (input : Block) (result : Block × Cache)
    (present : result ∈ support (cache.forward input)) :
    result.2.entries.length ≤ cache.entries.length + 1 := by
  rcases tagless_forward_step_rows cache input result present with same | grew
  · simp [same]
  · simp [grew]

theorem tagless_forward_step_preserves_fresh (cache : Cache) (input address : Block)
    (different : input ≠ address) (unused : UnusedInput cache.entries address) (result : Block × Cache)
    (present : result ∈ support (cache.forward input)) : UnusedInput result.2.entries address := by
  rcases tagless_forward_step_rows cache input result present with same | grew
  · rwa [same]
  · rw [grew]
    intro row belongs
    rcases List.mem_cons.mp belongs with rfl | older
    · exact different
    · exact unused row older

private theorem tagless_opened_first_step_bad (messages : Index → Words 32)
    (salts : Index → BitVec 128) (index : Index) (cache : Cache)
    (fresh : UnusedInput cache.entries (taglessFirstAddress messages salts index))
    (room : cache.entries.length ≤ 2 ^ 121) :
    Pr{let a ← cache.forward (taglessFirstAddress messages salts index)}[
      taglessSecondAddress messages index a.1 ∈ firstDomain] ≤ (1 : ENNReal) / 2 ^ 167 := by
  unfold PermutationCache.forward
  simp only [fresh, dite_true, bind_pure_comp, prEvent_map]
  exact tagless_fresh_forward_first_domain_le cache _ fresh room (taglessMessageTail (messages index))

theorem tagless_opened_guard_le (messages : Index → Words 32) (salts : Index → BitVec 128)
    (cache : Cache) (replies : List Block) (indices : List Index)
    (distinct : indices.Nodup)
    (unseen : ∀ i ∈ indices, UnusedInput cache.entries (taglessFirstAddress messages salts i))
    (room : cache.entries.length + 2 * indices.length ≤ 2 ^ 121) :
    Pr{let result ← runTaglessOpened messages salts cache replies indices}[result.bad = true] ≤
      (indices.length : ENNReal) * ((1 : ENNReal) / 2 ^ 167) := by
  classical
  induction indices generalizing cache replies with
  | nil => simp [runTaglessOpened]
  | cons index rest ih =>
    let rate : ENNReal := 1 / 2 ^ 167
    let head := taglessFirstAddress messages salts index
    let bad (a : Block × Cache) := taglessSecondAddress messages index a.1 ∈ firstDomain
    let step (a : Block × Cache) : ProbComp TaglessOpenedResult := do
      let address := taglessSecondAddress messages index a.1
      let b ← a.2.forward address
      let tail ← runTaglessOpened messages salts b.2 (b.1 :: a.1 :: replies) rest
      pure { tail with bad := decide (address ∈ firstDomain) || tail.bad }
    change Pr{let result ← (cache.forward head >>= step)}[result.bad = true] ≤ _
    have one : Pr{let a ← cache.forward head}[bad a] ≤ rate :=
      tagless_opened_first_step_bad messages salts index cache (unseen index List.mem_cons_self) (by omega)
    have restBound (a : Block × Cache) (found : a ∈ support (cache.forward head)) (good : ¬ bad a) :
        Pr{let result ← step a}[result.bad = true] ≤ (rest.length : ENNReal) * rate := by
      let second := taglessSecondAddress messages index a.1
      have outside : second ∉ firstDomain := good
      have aRoom := tagless_forward_step_room cache head a found
      have splitDistinct := List.nodup_cons.mp distinct
      have afterA : ∀ i ∈ rest, UnusedInput a.2.entries (taglessFirstAddress messages salts i) := by
        intro i inside
        apply tagless_forward_step_preserves_fresh cache head _ _ (unseen i (List.mem_cons_of_mem _ inside)) a found
        intro same
        have eq := tagless_first_address_injective messages salts same
        exact splitDistinct.1 (eq.symm ▸ inside)
      simp only [step, ← show second = taglessSecondAddress messages index a.1 from rfl, outside,
        decide_false, Bool.false_or]
      apply prEvent_bind_le_of_forall_le_of_support
      intro b bPossible
      have bRoom := tagless_forward_step_room a.2 second b bPossible
      have afterB (i : Index) (inside : i ∈ rest) :
          UnusedInput b.2.entries (taglessFirstAddress messages salts i) := by
        apply tagless_forward_step_preserves_fresh a.2 second _ _ (afterA i inside) b bPossible
        intro same
        exact outside (same.symm ▸ tagless_first_address_domain messages salts i)
      have tailRoom : b.2.entries.length + 2 * rest.length ≤ 2 ^ 121 := by
        simp only [List.length_cons] at room
        omega
      convert ih b.2 (b.1 :: a.1 :: replies) splitDistinct.2 afterB tailRoom using 1
      rw [bind_pure_comp, prEvent_map]
    have union := prEvent_bind_le_prEvent_add_of_support (cache.forward head) step bad
      (fun result => result.bad = true) restBound
    refine union.trans ((add_le_add one le_rfl).trans_eq ?_)
    rw [List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm]

private theorem tagless_forward_step_prefix (cache : Cache) (input : Block) (result : Block × Cache)
    (present : result ∈ support (cache.forward input)) :
    ∃ rows, result.2.entries = rows ++ cache.entries ∧ rows.length ≤ 1 ∧
      ∀ row ∈ rows, row.1 = input := by
  rcases tagless_forward_step_rows cache input result present with same | grew
  · exact ⟨[], by simpa using same, by decide, by simp⟩
  · exact ⟨[(input, result.1)], by simpa using grew, by simp, by simp⟩

/-- Opened rows admitted by the guard either lie outside the first-round domain,
or have the low word of an opened site's first-round address. -/
def taglessOpenedAddress (positions : Positions) (address : Block) : Prop :=
  address ∉ firstDomain ∨ ∃ i ∈ positions, address.extractLsb' 0 64 = firstTag i.val

theorem tagless_opened_rows (positions : Positions) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (cache : Cache) (replies : List Block) (indices : List Index)
    (opened : ∀ i ∈ indices, i ∈ positions) (result : TaglessOpenedResult)
    (possible : result ∈ support (runTaglessOpened messages salts cache replies indices))
    (good : result.bad = false) :
    ∃ added : List Row, result.cache.entries = added ++ cache.entries ∧
      added.length ≤ 2 * indices.length ∧ ∀ row ∈ added, taglessOpenedAddress positions row.1 := by
  classical
  induction indices generalizing cache replies result with
  | nil =>
    simp only [runTaglessOpened, support_pure, Set.mem_singleton_iff] at possible
    subst result
    exact ⟨[], by simp⟩
  | cons index rest ih =>
    simp only [runTaglessOpened] at possible
    obtain ⟨a, aPossible, possible⟩ := (mem_support_bind_iff _ _ _).mp possible
    obtain ⟨b, bPossible, possible⟩ := (mem_support_bind_iff _ _ _).mp possible
    obtain ⟨tail, tailPossible, same⟩ := (mem_support_bind_iff _ _ _).mp possible
    simp only [support_pure, Set.mem_singleton_iff] at same
    subst result
    change (decide (taglessSecondAddress messages index a.1 ∈ firstDomain) || tail.bad) = false at good
    have safe := Bool.or_eq_false_iff.mp good
    have secondSafe : taglessSecondAddress messages index a.1 ∉ firstDomain := of_decide_eq_false safe.1
    obtain ⟨more, tailLayout, tailCount, tailGuard⟩ := ih b.2 (b.1 :: a.1 :: replies)
      (fun i h => opened i (List.mem_cons_of_mem _ h)) tail tailPossible safe.2
    obtain ⟨afterA, aLayout, aCount, aOnly⟩ := tagless_forward_step_prefix cache _ a aPossible
    obtain ⟨afterB, bLayout, bCount, bOnly⟩ := tagless_forward_step_prefix a.2 _ b bPossible
    refine ⟨(more ++ afterB) ++ afterA, ?_, ?_, ?_⟩
    · change tail.cache.entries = _
      simp only [tailLayout, bLayout, aLayout, List.append_assoc]
    · simp only [List.length_append, List.length_cons]
      omega
    · intro row included
      rcases List.mem_append.mp included with earlier | aRow
      · rcases List.mem_append.mp earlier with tailRow | bRow
        · exact tailGuard row tailRow
        · exact Or.inl (bOnly row bRow ▸ secondSafe)
      · exact Or.inr ⟨index, opened index List.mem_cons_self,
          (aOnly row aRow) ▸ hidden_first_tag index (messages index) (salts index)⟩

theorem tagless_opened_address_disjoint {positions : Positions} {address : Block}
    (guard : taglessOpenedAddress positions address) (messages : Index → Words 32)
    (salts : Index → BitVec 128) (i : Index) (hidden : i ∉ positions) :
    address ≠ taglessFirstAddress messages salts i := by
  intro same
  subst address
  rcases guard with outside | ⟨j, opened, tag⟩
  · exact outside (tagless_first_address_domain messages salts i)
  · exact hidden ((hidden_first_tag_indices ((hidden_first_tag i (messages i) (salts i)).symm.trans tag)).symm ▸ opened)

noncomputable local instance {ι α : Type} [Fintype ι] [Fintype α] [Nonempty α] :
    SampleableType (ι → α) := by
  classical
  exact SampleableType.ofFintype _

noncomputable def taglessOpenedBad {positions : Positions} (messages : Index → Words 32)
    (cache : Cache) (salts : OpenedSalts positions) (result : TaglessOpenedResult) : Prop :=
  (∃ row ∈ cache.entries, ∃ i : {i : Index // i ∈ positions},
    hiddenFirstInput i.val (messages i.val) (salts i) = row.1) ∨ result.bad = true

theorem tagless_opened_tape_guard_le (positions : Positions) (messages : Index → Words 32)
    (cache : Cache) (room : cache.entries.length + 2 * positions.card ≤ 2 ^ 121) :
    Pr{let result ← (do let salts ← $ᵗ OpenedSalts positions
                        let opened ← runTaglessOpened messages (publicOpenedSalts salts) cache [] positions.toList
                        pure (salts, opened))}[taglessOpenedBad messages cache result.1 result.2] ≤
      (cache.entries.length : ENNReal) / 2 ^ 128 + (positions.card : ENNReal) / 2 ^ 167 := by
  classical
  let badSalt (salts : OpenedSalts positions) := ∃ row ∈ cache.entries,
    ∃ i : {i : Index // i ∈ positions}, hiddenFirstInput i.val (messages i.val) (salts i) = row.1
  let next (salts : OpenedSalts positions) : ProbComp (OpenedSalts positions × TaglessOpenedResult) := do
    let opened ← runTaglessOpened messages (publicOpenedSalts salts) cache [] positions.toList
    pure (salts, opened)
  change Pr{let result ← ($ᵗ OpenedSalts positions) >>= next}[
      taglessOpenedBad messages cache result.1 result.2] ≤ _
  have initial : Pr{let salts ← $ᵗ OpenedSalts positions}[badSalt salts] ≤
      (cache.entries.length : ENNReal) / 2 ^ 128 := by
    have bound := tagless_first_tape_cache_hit
      (fun i : {i : Index // i ∈ positions} => i.val) Subtype.val_injective messages (cache.entries.map Prod.fst)
    simp only [List.length_map] at bound
    refine (prEvent_mono ($ᵗ OpenedSalts positions) (p := badSalt)
      (q := fun salts => ∃ address ∈ cache.entries.map Prod.fst, ∃ i : {i : Index // i ∈ positions},
        hiddenFirstInput i.val (messages i.val) (salts i) = address) ?_).trans bound
    rintro salts ⟨row, included, i, hit⟩
    exact ⟨row.1, List.mem_map_of_mem included, i, hit⟩
  have tail (salts : OpenedSalts positions) (_ : salts ∈ support ($ᵗ OpenedSalts positions))
      (good : ¬ badSalt salts) :
      Pr{let result ← next salts}[taglessOpenedBad messages cache result.1 result.2] ≤
        (positions.card : ENNReal) / 2 ^ 167 := by
    have fresh (i : Index) (inside : i ∈ positions.toList) :
        UnusedInput cache.entries (taglessFirstAddress messages (publicOpenedSalts salts) i) := by
      intro row present same
      have belongs := Finset.mem_toList.mp inside
      refine good ⟨row, present, ⟨i, belongs⟩, ?_⟩
      simpa only [taglessFirstAddress, publicOpenedSalts, belongs, dite_true] using same.symm
    have guard := tagless_opened_guard_le messages (publicOpenedSalts salts) cache [] positions.toList
      (Finset.nodup_toList _) fresh (by simpa only [Finset.length_toList] using room)
    simp only [next, bind_pure_comp, prEvent_map]
    simp only [taglessOpenedBad, show (∃ row ∈ cache.entries, ∃ i : {i : Index // i ∈ positions},
        hiddenFirstInput i.val (messages i.val) (salts i) = row.1) = False from propext (iff_false_intro good),
      false_or]
    simpa only [Finset.length_toList, mul_one_div] using guard
  exact (prEvent_bind_le_prEvent_add_of_support ($ᵗ OpenedSalts positions) next badSalt
    (fun result => taglessOpenedBad messages cache result.1 result.2) tail).trans (add_le_add initial le_rfl)

end TwoPermutationPrototype.Sampling
