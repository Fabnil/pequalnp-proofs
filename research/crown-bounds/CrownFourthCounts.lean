import CrownFourthGroups
import CrownThirdCounts

namespace CrownFourthCounts

open CrownForks CrownForest CrownFourNetwork CrownFourNormal CrownVisibility CrownFirstAnd
open CrownProfiles CrownFourProfiles CrownFourthStructure Finset
open CrownProfileThree.Network (ones)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

variable {N : Network Ten}

private def price (N : Network Ten) (i : Ten) : ℕ :=
  2 ^ (4 - (profile N.forest (singletonInput i)).count true)

private theorem by_load (i : Ten) (k : ℕ) (load : (profile N.forest (singletonInput i)).count true ≤ k) :
    2 ^ (4 - k) ≤ price N i := Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left load 4)

private theorem two_off (i : Ten) {s t : Fin 4} (different : s ≠ t)
    (offS : signal N.forest s.val (singletonInput i) = false)
    (offT : signal N.forest t.val (singletonInput i) = false) : 4 ≤ price N i := by
  have rule : ∀ (a b c d : Bool) (s t : Fin 4), s ≠ t →
    bitAt [a, b, c, d] s.val = false → bitAt [a, b, c, d] t.val = false →
    [a, b, c, d].count true ≤ 2 := by decide +kernel
  exact by_load i 2 (rule _ _ _ _ s t different offS offT)

private theorem three_off (i : Ten) {s t u : Fin 4} (st : s ≠ t) (su : s ≠ u) (tu : t ≠ u)
    (offS : signal N.forest s.val (singletonInput i) = false)
    (offT : signal N.forest t.val (singletonInput i) = false)
    (offU : signal N.forest u.val (singletonInput i) = false) : 8 ≤ price N i := by
  have rule : ∀ (a b c d : Bool) (s t u : Fin 4), s ≠ t → s ≠ u → t ≠ u →
    bitAt [a, b, c, d] s.val = false → bitAt [a, b, c, d] t.val = false →
    bitAt [a, b, c, d] u.val = false → [a, b, c, d].count true ≤ 1 := by decide +kernel
  exact by_load i 1 (rule _ _ _ _ s t u st su tu offS offT offU)

private theorem at_least_two (C : Case N) (i : Ten) : 2 ≤ price N i := by
  have no := noFull N.forest C.valid C.test (fun a => (C.raw a).le) (by decide) N.numShared_eq i
  let x := singletonInput i
  have notAll : ¬ (signal N.forest 0 x = true ∧ signal N.forest 1 x = true ∧
      signal N.forest 2 x = true ∧ signal N.forest 3 x = true) := by
    rintro ⟨p, q, r, s⟩
    apply no
    intro t inside
    rw [N.numShared_eq] at inside
    interval_cases t <;> assumption
  have rule : ∀ p q r s : Bool, ¬ (p = true ∧ q = true ∧ r = true ∧ s = true) →
      [p, q, r, s].count true ≤ 3 := by decide +kernel
  exact by_load i 3 (rule _ _ _ _ notAll)

private theorem anchor_price (C : Case N) : price N C.a = 2 := by
  have rule : ∀ (a b c d : Bool) (m : Fin 3), bitAt [a, b, c, d] m.val = false →
      (∀ k : Fin 4, k.val ≠ m.val → bitAt [a, b, c, d] k.val = true) →
      [a, b, c, d].count true = 3 := by decide +kernel
  have count : (profile N.forest (singletonInput C.a)).count true = 3 :=
    rule _ _ _ _ C.missing C.offMissing (fun k ne => C.anchor_on_except_missing k.val k.isLt ne)
  rw [price, count]
  rfl

private theorem cold_floor (C : Case N) {i : Ten} (hi : i ∈ C.cold) : 16 ≤ price N i := by
  have none : (profile N.forest (singletonInput i)).count true = 0 :=
    List.count_eq_zero.mpr (Case.noHot_of_cold (mem_filter.mp hi).2)
  exact by_load i 0 none.le

private theorem sum_floor (S : Finset Ten) (base : ℕ) (lower : ∀ i ∈ S, base ≤ price N i) :
    base * S.card ≤ ∑ i ∈ S, price N i := by
  calc
    _ = ∑ _i ∈ S, base := by simp [Nat.mul_comm]
    _ ≤ _ := sum_le_sum lower

private theorem total (C : Case N) :
    2 + (∑ i ∈ C.cold, price N i) + (∑ i ∈ C.hidden, price N i) +
      (∑ i ∈ C.hotVisible, price N i) ≤ 64 := by
  have packed := packing64 N.forest C.valid C.test (fun i => (C.raw i).le) N.numShared_eq N.twoReads_valid
  change ∑ i : Ten, price N i ≤ 64 at packed
  have groups := C.sum_groups (price N)
  have split := sum_erase_add (s := univ) (f := price N) (mem_univ C.a)
  change (∑ i ∈ C.others, price N i) + price N C.a = _ at split
  have anchor := anchor_price C
  omega

private theorem cast_ne {s t : Fin 3} (ne : s ≠ t) : s.castSucc ≠ t.castSucc :=
  fun h => ne (Fin.ext (congrArg (fun k : Fin 4 => k.val) h))

private theorem prior_ne_last (s : Fin 3) : s.castSucc ≠ (3 : Fin 4) := by
  intro eq
  have ht := s.isLt
  have value : s.val = 3 := congrArg Fin.val eq
  omega

private theorem visible_other (C : Case N) {i : Ten} (vis : i ∈ C.hotVisible)
    {t k : Fin 4} (atT : Case.first N i = t.val) (ne : k ≠ t) : N.stages.rawAt k i = 0 := by
  obtain ⟨_, before, seen⟩ := C.mem_hotVisible.mp vis
  have hot := N.hot_of_firstHot_lt (singletonInput i) before
  have measure := (visibleReads N.forest (singletonInput i) hot seen (C.raw i).le).2 k.val
  change stageWeight N.forest (ones i) k.val = (if k.val = Case.first N i then 1 else 0) at measure
  rw [N.rawAt_eq k i]
  simpa only [atT, ite_eq_right (fun h => ne (Fin.ext h))] using measure

private theorem visible_pq_floor (C : Case N) {i : Ten} (vis : i ∈ C.hotVisible)
    {t u : Fin 3} (sides : (t = C.p ∧ u = C.q) ∨ (t = C.q ∧ u = C.p))
    (atT : Case.first N i = t.val) : 4 ≤ price N i := by
  have mt : C.missing.castSucc ≠ t.castSucc := by
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C.missing_ne_p
    · exact C.missing_ne_q
  have mu : C.missing.castSucc ≠ u.castSucc := by
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact C.missing_ne_q
    · exact C.missing_ne_p
  have ut : u.castSucc ≠ t.castSucc := by
    rcases sides with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (cast_ne C.pq).symm
    · exact cast_ne C.pq
  have offM := C.no_input_no_signal C.missing i (visible_other C vis atT mt) (by
    intro s used
    rcases (C.possible_links used).2 with p | q
    · exact (C.pm p.symm).elim
    · exact (C.qm q.symm).elim)
  have offU := C.no_input_no_signal u i (visible_other C vis atT ut) (by
    intro s used
    rw [(C.possible_links used).1]
    exact offM)
  exact two_off i mu offM offU

private theorem visible_last_floor (i : Ten) (firstI : Case.first N i = 3) : 8 ≤ price N i := by
  have flags := N.firstHot_flags (singletonInput i) (by decide) firstI
  exact three_off i (s := 0) (t := 1) (u := 2) (by decide) (by decide) (by decide)
    (flags.2 0 (by decide)) (flags.2 1 (by decide)) (flags.2 2 (by decide))

private theorem absent_links_of_three_hidden (C : Case N) (many : 3 ≤ C.hidden.card) :
    ∀ s t : Fin 3, ¬ N.link s t := by
  intro s t used
  obtain ⟨source, atP | atQ⟩ := C.possible_links used
  · subst s
    subst t
    have cap := C.hidden_cap_with_link (u := C.q) (Or.inl ⟨rfl, rfl⟩) used
    omega
  · subst s
    subst t
    have cap := C.hidden_cap_with_link (u := C.p) (Or.inr ⟨rfl, rfl⟩) used
    omega

private theorem last_readers_off (C : Case N) (noLinks : ∀ s t : Fin 3, ¬ N.link s t)
    {i : Ten} (mem : i ∈ C.lastReaders) :
    signal N.forest C.p.val (singletonInput i) = false ∧ signal N.forest C.q.val (singletonInput i) = false := by
  obtain ⟨ia, hidden, last⟩ := C.mem_lastReaders.mp mem
  have m := C.hidden_reads_missing ia hidden
  have other := (N.stages.rawAtTwo C.missing_ne_last (N.stageBudget i (C.raw i).le)
    (show 0 < N.stages.rawAt C.missing.castSucc i by rw [m]; decide) last).2
  have pOff := C.no_input_no_signal C.p i (other _ C.missing_ne_p.symm (prior_ne_last _))
    (fun s h => (noLinks s C.p h).elim)
  have qOff := C.no_input_no_signal C.q i (other _ C.missing_ne_q.symm (prior_ne_last _))
    (fun s h => (noLinks s C.q h).elim)
  exact ⟨pOff, qOff⟩

private theorem hidden_floor (C : Case N) (noLinks : ∀ s t : Fin 3, ¬ N.link s t)
    (hasLast : C.lastReaders.Nonempty) {i : Ten} (hidden : i ∈ C.hidden) : 4 ≤ price N i := by
  by_cases member : i ∈ C.lastReaders
  · obtain ⟨p, q⟩ := last_readers_off C noLinks member
    exact two_off i (cast_ne C.pq) p q
  obtain ⟨j, hj⟩ := hasLast
  obtain ⟨ja, noJ, lastJ⟩ := C.mem_lastReaders.mp hj
  obtain ⟨ia, noI⟩ := C.mem_hidden.mp hidden
  have ji : j ≠ i := fun eq => member (eq ▸ hj)
  have sOff := C.last_read_rules_out_last ja ji noJ lastJ (C.hidden_activates_missing ia noI)
  by_cases onP : signal N.forest C.p.val (singletonInput i) = true
  · have offQ := Bool.eq_false_of_not_eq_true (fun onQ => C.noBoth i ia ⟨onP, onQ⟩)
    exact two_off i (prior_ne_last C.q) offQ sOff
  · exact two_off i (prior_ne_last C.p) (Bool.eq_false_of_not_eq_true onP) sOff

private theorem visible_missing_floor (C : Case N) (noLinks : ∀ s t : Fin 3, ¬ N.link s t)
    (hasLast : C.lastReaders.Nonempty) {i : Ten} (mem : i ∈ C.slot 2) : 8 ≤ price N i := by
  have seen := (mem_filter.mp mem).1
  have atM := C.first_of_slot mem
  change Case.first N i = C.missing.val at atM
  have onM : signal N.forest C.missing.val (singletonInput i) = true :=
    (N.firstHot_flags (singletonInput i) (C.missing.isLt.trans (by decide)) atM).1
  have offP := C.no_input_no_signal C.p i (visible_other C seen atM C.missing_ne_p.symm)
    (fun s h => (noLinks s C.p h).elim)
  have offQ := C.no_input_no_signal C.q i (visible_other C seen atM C.missing_ne_q.symm)
    (fun s h => (noLinks s C.q h).elim)
  obtain ⟨j, hj⟩ := hasLast
  obtain ⟨ja, noJ, read⟩ := C.mem_lastReaders.mp hj
  have ji : j ≠ i := by
    intro eq
    have readI := (C.mem_hotVisible.mp seen).2.2
    rw [eq] at noJ
    omega
  have offD := C.last_read_rules_out_last ja ji noJ read onM
  exact three_off i (cast_ne C.pq) (prior_ne_last C.p) (prior_ne_last C.q) offP offQ offD

private theorem last_floor_eight (C : Case N) (noLinks : ∀ s t : Fin 3, ¬ N.link s t)
    (two : 2 ≤ C.lastReaders.card) {i : Ten} (hi : i ∈ C.lastReaders) : 8 ≤ price N i := by
  have nonempty : (C.lastReaders.erase i).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hi]
    omega
  obtain ⟨j, hj⟩ := nonempty
  obtain ⟨ji, member⟩ := mem_erase.mp hj
  obtain ⟨ja, noJ, lastJ⟩ := C.mem_lastReaders.mp member
  obtain ⟨ia, noI, _⟩ := C.mem_lastReaders.mp hi
  obtain ⟨offP, offQ⟩ := last_readers_off C noLinks hi
  have offD := C.last_read_rules_out_last ja ji noJ lastJ (C.hidden_activates_missing ia noI)
  exact three_off i (cast_ne C.pq) (prior_ne_last C.p) (prior_ne_last C.q) offP offQ offD

private theorem three_hidden_numbers (c p q m d : ℕ)
    (pmax : p ≤ 1) (qmax : q ≤ 1) (mmax : m ≤ 1) (dmax : d ≤ 1)
    (count : 1 + c + 3 + p + q + m + d = 10)
    (bound : 2 + 16 * c + 12 + (4 * p + 4 * q + 8 * m + 8 * d) ≤ 64) : False := by
  omega

private theorem four_hidden_numbers (c p q m d : ℕ)
    (pmax : p ≤ 1) (qmax : q ≤ 1) (mmax : m ≤ 1) (dmax : d ≤ 1)
    (count : 1 + c + 4 + p + q + m + d = 10)
    (bound : 2 + 16 * c + 24 + (4 * p + 4 * q + 8 * m + 8 * d) ≤ 64) : False := by
  omega

private theorem last_positive (h l r : ℕ) (many : 3 ≤ h) (sum : l + r = h) (rest : r ≤ 2) :
    0 < l := by omega

private theorem last_two_with_cost (h l r : ℕ) (many : 3 ≤ h) (cap : h ≤ 4) (notThree : h ≠ 3)
    (sum : l + r = h) (rest : r ≤ 2) : h = 4 ∧ 2 ≤ l ∧ 24 ≤ 8 * l + 4 * r := by
  omega

theorem impossible (C : Case N) : False := by
  obtain ⟨capP, capQ, capD⟩ := C.slot_caps_except_missing
  have capM := C.slot_missing_cap
  have slots := C.card_slots
  have counts : 1 + C.cold.card + C.hidden.card + (C.slot 0).card + (C.slot 1).card +
      (C.slot 2).card + (C.slot 3).card = 10 := by
    simpa only [← slots, Nat.add_assoc] using C.card_balance
  have weight := total C
  have weightC := sum_floor C.cold 16 (fun _ h => cold_floor C h)
  have sumV := C.sum_slots (price N)
  have weightP := sum_floor (C.slot 0) 4 (fun _ mem =>
    visible_pq_floor C (mem_filter.mp mem).1 (u := C.q) (Or.inl ⟨rfl, rfl⟩) (C.first_of_slot mem))
  have weightQ := sum_floor (C.slot 1) 4 (fun _ mem =>
    visible_pq_floor C (mem_filter.mp mem).1 (u := C.p) (Or.inr ⟨rfl, rfl⟩) (C.first_of_slot mem))
  have weightD := sum_floor (C.slot 3) 8 (fun i mem => visible_last_floor i (C.first_of_slot mem))
  have priceV (m : ℕ) (weightM : m * (C.slot 2).card ≤ ∑ i ∈ C.slot 2, price N i) :
      4 * (C.slot 0).card + 4 * (C.slot 1).card + m * (C.slot 2).card + 8 * (C.slot 3).card ≤
        ∑ i ∈ C.hotVisible, price N i := by
    rw [← sumV]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add weightP weightQ) weightM) weightD
  have priceTotal (h v : ℕ) (bh : h ≤ ∑ i ∈ C.hidden, price N i)
      (bv : v ≤ ∑ i ∈ C.hotVisible, price N i) :
      2 + 16 * C.cold.card + h + v ≤ 64 :=
    (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left weightC 2) bh) bv).trans weight
  by_cases two : C.hidden.card = 2
  · have weightH := sum_floor C.hidden 2 (fun i _ => at_least_two C i)
    have weightM := sum_floor (C.slot 2) 2 (fun i _ => at_least_two C i)
    have bound := priceTotal _ _ weightH (priceV 2 weightM)
    exact CrownTenCases.fourthWithLink _ _ _ _ _ _ C.cold_cap two.le capP capQ capM capD counts
      (by simpa only [Nat.add_assoc] using bound)
  · have many : 3 ≤ C.hidden.card := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne C.hidden_min_two (fun h => two h.symm))
    have noLinks := absent_links_of_three_hidden C many
    have splitCount := C.hidden_last_count
    have outside := C.hidden_rest_cap
    have hasLast : C.lastReaders.Nonempty := card_pos.mp (last_positive _ _ _ many splitCount outside)
    have weightM := sum_floor (C.slot 2) 8 (fun _ h => visible_missing_floor C noLinks hasLast h)
    have floorH (i : Ten) (h : i ∈ C.hidden) := hidden_floor C noLinks hasLast h
    by_cases three : C.hidden.card = 3
    · have weightH := sum_floor C.hidden 4 floorH
      rw [three] at weightH counts
      exact three_hidden_numbers _ _ _ _ _ capP capQ capM capD counts (priceTotal 12 _ weightH (priceV 8 weightM))
    · obtain ⟨four, twoLast, enough⟩ := last_two_with_cost _ _ _ many C.hidden_cap three splitCount outside
      have part := sum_filter_add_sum_filter_not (s := C.hidden)
        (p := fun i => 0 < N.stages.rawAt 3 i) (price N)
      let earlier := C.hidden.filter (fun i => ¬ 0 < N.stages.rawAt 3 i)
      change (∑ i ∈ C.lastReaders, price N i) + (∑ i ∈ earlier, price N i) = _ at part
      have weightL := sum_floor C.lastReaders 8 (fun _ => last_floor_eight C noLinks twoLast)
      have weightE := sum_floor earlier 4 (fun i h => floorH i (mem_filter.mp h).1)
      have weightH := enough.trans (Nat.add_le_add weightL weightE)
      rw [part] at weightH
      rw [four] at counts
      exact four_hidden_numbers _ _ _ _ _ capP capQ capM capD counts (priceTotal 24 _ weightH (priceV 8 weightM))

theorem noOverlapAtFourth : ¬ HasOverlapAt 3 := by
  intro hyp
  obtain ⟨N, ⟨C⟩⟩ := CrownFourthStructure.ofOverlap hyp
  exact impossible C

theorem crownTenOnlyOr
    (small : RepSizeAtMost (fun u v : Ten => decide (u ≠ v)) 33) :
    CrownFirstOr.HasOrPrefix 4 :=
  (CrownThirdCounts.crownTenTwoCases small).resolve_left noOverlapAtFourth

end CrownFourthCounts
