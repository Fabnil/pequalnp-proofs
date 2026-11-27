import CrownFourthReaders

namespace CrownFourthStructure.Case

open CrownForks CrownForest CrownFourNetwork CrownFourNormal CrownVisibility CrownFirstAnd
open CrownFourProfiles Finset
open CrownProfileThree.Network (ones)
open scoped Classical

variable {N : Network Ten} (C : CrownFourthStructure.Case N)

def first (N : Network Ten) (i : Ten) : ℕ := firstHot N.forest (singletonInput i)

def others : Finset Ten := univ.erase C.a

def cold : Finset Ten := C.others.filter (fun i => first N i = 4)

def hidden : Finset Ten := C.others.filter (fun i => outputWeight N.forest (ones i) = 0)

def hotVisible : Finset Ten := (C.others.filter (fun i => first N i ≠ 4)).filter
  (fun i => outputWeight N.forest (ones i) ≠ 0)

def lastReaders : Finset Ten := C.hidden.filter (fun i => 0 < N.stages.rawAt 3 i)

theorem noHot_of_cold {i : Ten} (cold : first N i = 4) :
    true ∉ CrownProfiles.profile N.forest (singletonInput i) := by
  intro active
  have bound := firstHot_lt N.forest (singletonInput i) active
  change first N i < numShared N.forest at bound
  rw [cold, N.numShared_eq] at bound
  omega

theorem mem_hidden {i : Ten} : i ∈ C.hidden ↔ i ≠ C.a ∧ outputWeight N.forest (ones i) = 0 := by
  simp [hidden, others]

theorem mem_lastReaders {i : Ten} : i ∈ C.lastReaders ↔
    i ≠ C.a ∧ outputWeight N.forest (ones i) = 0 ∧ 0 < N.stages.rawAt 3 i := by
  simp only [lastReaders, mem_filter, C.mem_hidden, and_assoc]

theorem mem_hotVisible {i : Ten} : i ∈ C.hotVisible ↔
    i ≠ C.a ∧ first N i < 4 ∧ 0 < outputWeight N.forest (ones i) := by
  have higher := N.firstHot_le (singletonInput i)
  change first N i ≤ 4 at higher
  have early : first N i ≠ 4 ↔ first N i < 4 := by omega
  simp [hotVisible, others, early, Nat.pos_iff_ne_zero, and_assoc]

theorem sum_groups (w : Ten → ℕ) :
    (∑ i ∈ C.cold, w i) + ((∑ i ∈ C.hidden, w i) + (∑ i ∈ C.hotVisible, w i)) =
      ∑ i ∈ C.others, w i := by
  let warm := C.others.filter (fun i => first N i ≠ 4)
  have split := sum_filter_add_sum_filter_not (s := C.others) (p := fun i => first N i = 4) w
  have splitWarm := sum_filter_add_sum_filter_not (s := warm)
    (p := fun i => outputWeight N.forest (ones i) = 0) w
  have same : warm.filter (fun i => outputWeight N.forest (ones i) = 0) = C.hidden := by
    ext i
    constructor
    · intro h
      obtain ⟨warmMem, read⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨(mem_filter.mp warmMem).1, read⟩
    · intro h
      have ⟨ia, read⟩ := C.mem_hidden.mp h
      have hot : first N i ≠ 4 := by
        intro eq
        have seen := C.cold_is_visible ia (noHot_of_cold eq)
        omega
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_erase.mpr ⟨ia, mem_univ i⟩, hot⟩, read⟩
  rw [same] at splitWarm
  change (∑ i ∈ C.cold, w i) + (∑ i ∈ warm, w i) = _ at split
  rw [← splitWarm] at split
  exact split

theorem card_balance : 1 + C.cold.card + C.hidden.card + C.hotVisible.card = 10 := by
  have groups := C.sum_groups (fun _ => 1)
  simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one] at groups
  have outside : C.others.card = 9 := by
    unfold others
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

theorem cold_cap : C.cold.card ≤ 3 := by
  apply le_trans (card_le_card (t := CrownFourNormal.emptyProfiles N.forest) ?_)
    (emptyProfileCount N.forest C.valid C.test (fun i => (C.raw i).le) (by decide))
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, noHot_of_cold (mem_filter.mp hi).2⟩

def assignedStage (k : Fin 4) : ℕ :=
  if k = 0 then C.p.val else if k = 1 then C.q.val else if k = 2 then C.missing.val else 3

private def visibleClass (i : Ten) : Fin 4 :=
  if first N i = C.p.val then 0 else if first N i = C.q.val then 1 else if first N i = C.missing.val then 2 else 3

def slot (k : Fin 4) : Finset Ten := C.hotVisible.filter (fun i => C.visibleClass i = k)

theorem stage_in_range (k : Fin 4) : C.assignedStage k < 4 := by
  fin_cases k
  · exact C.p.isLt.trans (by decide)
  · exact C.q.isLt.trans (by decide)
  · exact C.missing.isLt.trans (by decide)
  · change (3 : ℕ) < 4
    decide

theorem first_of_slot {i : Ten} {k : Fin 4} (mem : i ∈ C.slot k) : first N i = C.assignedStage k := by
  obtain ⟨vis, tag⟩ := mem_filter.mp mem
  rw [← tag]
  have early := (C.mem_hotVisible.mp vis).2.1
  unfold visibleClass
  split
  · assumption
  split
  · assumption
  split
  · assumption
  rename_i notP notQ notM
  change first N i = 3
  by_contra! different
  have bound : first N i < 3 := by omega
  have options := C.early_cases ⟨first N i, bound⟩
  rcases options with p | q | m
  · exact notP (congrArg Fin.val p)
  · exact notQ (congrArg Fin.val q)
  · exact notM (congrArg Fin.val m)

theorem sum_slots (w : Ten → ℕ) :
    (∑ i ∈ C.slot 0, w i) + (∑ i ∈ C.slot 1, w i) +
      (∑ i ∈ C.slot 2, w i) + (∑ i ∈ C.slot 3, w i) =
      ∑ i ∈ C.hotVisible, w i := by
  have split := sum_fiberwise C.hotVisible C.visibleClass w
  rw [Fin.sum_univ_four] at split
  exact split

theorem card_slots :
    (C.slot 0).card + (C.slot 1).card + (C.slot 2).card + (C.slot 3).card = C.hotVisible.card := by
  simpa only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one] using C.sum_slots (fun _ => 1)

private theorem subset_slot_cap (k : Fin 4) (S : Finset Ten) (inside : S ⊆ C.slot k)
    (a : Ten) (outside : a ∉ S) (on : signal N.forest (C.assignedStage k) (singletonInput a) = true) :
    S.card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra h
  have it := C.first_of_slot (inside hi)
  have jt := C.first_of_slot (inside hj)
  have inI := C.mem_hotVisible.mp (mem_filter.mp (inside hi)).1
  have inJ := C.mem_hotVisible.mp (mem_filter.mp (inside hj)).1
  have ia : i ≠ a := fun eq => outside (eq ▸ hi)
  have ja : j ≠ a := fun eq => outside (eq ▸ hj)
  exact twoVisible N.forest C.test h ia ja
    (N.hot_of_firstHot_lt _ inI.2.1) (N.hot_of_firstHot_lt _ inJ.2.1) inI.2.2 inJ.2.2
    (C.raw i).le (C.raw j).le (it.trans jt.symm) (by
      change signal N.forest (first N i) (singletonInput a) = true
      rw [it]
      exact on)

theorem slot_caps_except_missing :
    (C.slot 0).card ≤ 1 ∧ (C.slot 1).card ≤ 1 ∧ (C.slot 3).card ≤ 1 := by
  have outside (k : Fin 4) : C.a ∉ C.slot k := by
    intro found
    exact (C.mem_hotVisible.mp (mem_filter.mp found).1).1 rfl
  exact ⟨C.subset_slot_cap 0 _ (fun _ h => h) C.a (outside 0) C.onP,
    C.subset_slot_cap 1 _ (fun _ h => h) C.a (outside 1) C.onQ,
    C.subset_slot_cap 3 _ (fun _ h => h) C.a (outside 3) C.onLast⟩

theorem slot_missing_cap_two : (C.slot 2).card ≤ 2 := by
  by_contra! larger
  obtain ⟨a, mem⟩ := card_pos.mp (show 0 < (C.slot 2).card by omega)
  have hot := N.firstHot_flags (singletonInput a) (C.stage_in_range 2) (C.first_of_slot mem)
  have cap := C.subset_slot_cap 2 ((C.slot 2).erase a) (erase_subset _ _) a (notMem_erase _ _) hot.1
  rw [card_erase_of_mem mem] at cap
  omega

theorem hidden_nonempty : C.hidden.Nonempty := by
  apply card_pos.mp
  have ⟨p, q, d⟩ := C.slot_caps_except_missing
  have m := C.slot_missing_cap_two
  have slots := C.card_slots
  have total := C.card_balance
  have cold := C.cold_cap
  omega

theorem slot_missing_cap : (C.slot 2).card ≤ 1 := by
  obtain ⟨a, mem⟩ := C.hidden_nonempty
  obtain ⟨aa, absent⟩ := C.mem_hidden.mp mem
  have outside : a ∉ C.slot 2 := by
    intro there
    have on := (C.mem_hotVisible.mp (mem_filter.mp there).1).2.2
    omega
  exact C.subset_slot_cap 2 _ (fun _ h => h) a outside (C.hidden_activates_missing aa absent)

theorem hidden_min_two : 2 ≤ C.hidden.card := by
  have ⟨p, q, d⟩ := C.slot_caps_except_missing
  have m := C.slot_missing_cap
  have slots := C.card_slots
  have total := C.card_balance
  have cold := C.cold_cap
  omega

theorem last_cap : C.lastReaders.card ≤ 2 := by
  by_contra! big
  obtain ⟨i, mem⟩ := card_pos.mp (show 0 < C.lastReaders.card by omega)
  obtain ⟨ia, hidden, read⟩ := C.mem_lastReaders.mp mem
  have bound : C.lastReaders.card ≤ 2 := by
    apply CrownProfiles.profileCapacity N.forest C.test C.lastReaders
      (CrownProfiles.profile N.forest (singletonInput i))
    · intro j hj
      by_cases same : j = i
      · rw [same]
      obtain ⟨ja, absent, used⟩ := C.mem_lastReaders.mp hj
      exact C.hidden_last_pair_profile ja ia same absent hidden used read
    · exact fun j _ => (C.raw j).le
    · by_contra cold
      have active := C.cold_is_visible ia cold
      omega
  omega

private theorem cap_of_early_reader (t : Fin 3) (different : C.missing.castSucc ≠ t.castSucc) :
    (C.hidden.filter (fun i => 0 < N.stages.rawAt t.castSucc i)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra ne
  obtain ⟨inI, readI⟩ := mem_filter.mp hi
  obtain ⟨inJ, readJ⟩ := mem_filter.mp hj
  obtain ⟨ia, noI⟩ := C.mem_hidden.mp inI
  obtain ⟨ja, noJ⟩ := C.mem_hidden.mp inJ
  exact C.hidden_missing_and_blocks ia ne noI different readI
    (C.hidden_activates_missing ja noJ) (C.direct_on t j readJ)

theorem hidden_rest_cap :
    (C.hidden.filter (fun i => ¬ 0 < N.stages.rawAt 3 i)).card ≤ 2 := by
  let rest := C.hidden.filter (fun i => ¬ 0 < N.stages.rawAt 3 i)
  let atP (i : Ten) := 0 < N.stages.rawAt C.p.castSucc i
  have split := card_filter_add_card_filter_not (s := rest) atP
  have capP := (card_le_card (show rest.filter atP ⊆ C.hidden.filter atP from
    fun _ m => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp m).1).1, (mem_filter.mp m).2⟩)).trans
    (C.cap_of_early_reader C.p C.missing_ne_p)
  have subset : (rest.filter (fun i => ¬ atP i)) ⊆
      C.hidden.filter (fun i => 0 < N.stages.rawAt C.q.castSucc i) := by
    intro i mem
    obtain ⟨slot, nP⟩ := mem_filter.mp mem
    obtain ⟨h, nD⟩ := mem_filter.mp slot
    obtain ⟨ia, absent⟩ := C.mem_hidden.mp h
    rcases C.hidden_second ia absent with p | q | d
    · exact (nP p).elim
    · exact mem_filter.mpr ⟨h, q⟩
    · exact (nD d).elim
  have capQ := (card_le_card subset).trans (C.cap_of_early_reader C.q C.missing_ne_q)
  change rest.card ≤ 2
  omega

theorem hidden_last_count : C.lastReaders.card + (C.hidden.filter (fun i => ¬ 0 < N.stages.rawAt 3 i)).card =
    C.hidden.card := card_filter_add_card_filter_not (s := C.hidden) _

theorem hidden_cap : C.hidden.card ≤ 4 := by
  have first := C.last_cap
  have second := C.hidden_rest_cap
  have sum := C.hidden_last_count
  omega

/-- If the missing signal feeds one earlier stage, a hidden input with that
    stage as second reader blocks every other hidden input. -/
theorem hidden_cap_with_link {t u : Fin 3}
    (sides : (t = C.p ∧ u = C.q) ∨ (t = C.q ∧ u = C.p)) (used : N.link C.missing t) :
    C.hidden.card ≤ 2 := by
  have different : C.missing.castSucc ≠ t.castSucc := by
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C.missing_ne_p
    · exact C.missing_ne_q
  have goes (i : Ten) (mem : i ∈ C.hidden) : signal N.forest t.val (singletonInput i) = true := by
    have h := C.mem_hidden.mp mem
    exact (Bool.le_iff_imp.mp (C.link_implies used _)) (C.hidden_activates_missing h.1 h.2)
  have noOther (i : Ten) (mem : i ∈ C.hidden) : ¬ 0 < N.stages.rawAt u.castSucc i := by
    intro read
    have onT := goes i mem
    have onU := C.direct_on u i read
    apply C.noBoth i (C.mem_hidden.mp mem).1
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨onT, onU⟩
    · exact ⟨onU, onT⟩
  by_cases has : ∃ i ∈ C.hidden, 0 < N.stages.rawAt t.castSucc i
  · obtain ⟨i, mem, read⟩ := has
    obtain ⟨ia, absent⟩ := C.mem_hidden.mp mem
    have contained : C.hidden ⊆ ({i} : Finset Ten) := by
      intro j hj
      obtain ⟨ja, noJ⟩ := C.mem_hidden.mp hj
      apply mem_singleton.mpr
      by_contra same
      exact C.hidden_missing_and_blocks ia (fun eq => same eq.symm) absent different read
        (C.hidden_activates_missing ja noJ) (goes j hj)
    exact (card_le_card contained).trans (by simp)
  · have subset : C.hidden ⊆ C.lastReaders := by
      intro i mem
      obtain ⟨ia, absent⟩ := C.mem_hidden.mp mem
      have notT : ¬ 0 < N.stages.rawAt t.castSucc i := fun h => has ⟨i, mem, h⟩
      have notU := noOther i mem
      have possibilities := C.hidden_second ia absent
      have last : 0 < N.stages.rawAt 3 i := by
        rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
      exact C.mem_lastReaders.mpr ⟨ia, absent, last⟩
    exact (card_le_card subset).trans C.last_cap

end CrownFourthStructure.Case
