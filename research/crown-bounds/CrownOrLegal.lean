import CrownOrPrices
import CrownOrOriginGroups

namespace CrownOrLegal

open CrownFourNetwork CrownFourNormal CrownOrSupport CrownOrGraph CrownOrOrigins CrownOrOriginGroups
open CrownOrPrices Finset

def pairChosen (N : Network Ten) (k : Fin 6) : Bool :=
  decide (0 < (labels N (.pair k)).card)

def singleRepeated (N : Network Ten) (t : Fin 4) : Bool :=
  decide ((labels N (.single t)).card = 2)

def pairMask (N : Network Ten) : Fin 64 :=
  ⟨word6 (pairChosen N 0) (pairChosen N 1) (pairChosen N 2) (pairChosen N 3) (pairChosen N 4) (pairChosen N 5),
    word6_range _ _ _ _ _ _⟩

def repeatMask (N : Network Ten) : Fin 16 :=
  ⟨word4 (singleRepeated N 0) (singleRepeated N 1) (singleRepeated N 2) (singleRepeated N 3),
    word4_range _ _ _ _⟩

def pairsUsed (N : Network Ten) : List (Fin 6) := (List.finRange 6).filter (pairChosen N)

def repeatedUsed (N : Network Ten) : List (Fin 4) := (List.finRange 4).filter (singleRepeated N)

def onceUsed (N : Network Ten) : List (Fin 4) :=
  (List.finRange 4).filter fun t => decide ((labels N (.single t)).card = 1)

private theorem pair_bit (N : Network Ten) (k : Fin 6) : (pairMask N).val.testBit k.val = pairChosen N k := by
  obtain ⟨a, b, c, d, e, f⟩ := word6_bits (pairChosen N 0) (pairChosen N 1) (pairChosen N 2)
    (pairChosen N 3) (pairChosen N 4) (pairChosen N 5)
  fin_cases k <;> first | exact a | exact b | exact c | exact d | exact e | exact f

private theorem repeat_bit (N : Network Ten) (k : Fin 4) :
    (repeatMask N).val.testBit k.val = singleRepeated N k := by
  obtain ⟨a, b, c, d⟩ :=
    word4_bits (singleRepeated N 0) (singleRepeated N 1) (singleRepeated N 2) (singleRepeated N 3)
  fin_cases k <;> first | exact a | exact b | exact c | exact d

private theorem ways_agree : ∀ m : Fin 64, CrownOrProfiles.waysToStart m.val =
    ((List.finRange 6).filter fun k => m.val.testBit k.val).map
      (fun k => ((endpoints k).1.val, (endpoints k).2.val)) := by decide +kernel

private theorem flags_agree : ∀ m : Fin 16, CrownOrProfiles.flags.filter m.val.testBit =
    ((List.finRange 4).filter fun k => m.val.testBit k.val).map Fin.val := by decide +kernel

theorem paired_profiles (N : Network Ten) : CrownOrProfiles.hiddenProfiles (graph N).val (pairMask N).val =
    (pairsUsed N).map (fun k => close (graph N) (.pair k)) := by
  unfold CrownOrProfiles.hiddenProfiles
  rw [ways_agree, List.map_map]
  simp only [pair_bit]
  rfl

theorem repeated_profiles (N : Network Ten) :
    CrownOrProfiles.repeatedProfiles (graph N).val (repeatMask N).val =
      (repeatedUsed N).map (fun t => close (graph N) (.single t)) := by
  unfold CrownOrProfiles.repeatedProfiles
  rw [flags_agree, List.map_map]
  simp only [repeat_bit]
  rfl

def mandatory (N : Network Ten) : List Origin :=
  (pairsUsed N).map Origin.pair ++ (repeatedUsed N).map Origin.single

private theorem mandatory_profile_list (N : Network Ten) :
    CrownOrProfiles.hiddenProfiles (graph N).val (pairMask N).val ++
      CrownOrProfiles.repeatedProfiles (graph N).val (repeatMask N).val =
        (mandatory N).map (close (graph N)) := by
  rw [paired_profiles, repeated_profiles]
  simp only [mandatory, List.map_append, List.map_map, Function.comp_def]

private theorem pairs_mandatory (N : Network Ten) {k : Fin 6} (h : k ∈ pairsUsed N) :
    Mandatory N (.pair k) := card_pos.mp (of_decide_eq_true (List.mem_filter.mp h).2)

private theorem repeats_mandatory (N : Network Ten) {t : Fin 4} (h : t ∈ repeatedUsed N) :
    Mandatory N (.single t) := by
  change (labels N (.single t)).card = 2
  exact of_decide_eq_true (List.mem_filter.mp h).2

private theorem mem_mandatory (N : Network Ten) {s : Origin} (mem : s ∈ mandatory N) :
    Mandatory N s := by
  rcases List.mem_append.mp mem with a | b
  · obtain ⟨k, used, rfl⟩ := List.mem_map.mp a
    exact pairs_mandatory N used
  · obtain ⟨k, used, rfl⟩ := List.mem_map.mp b
    exact repeats_mandatory N used

private theorem mandatory_nodup (N : Network Ten) : (mandatory N).Nodup := by
  have pairs := List.Nodup.sublist (List.filter_sublist (p := pairChosen N)) (List.nodup_finRange 6)
  have reps := List.Nodup.sublist (List.filter_sublist (p := singleRepeated N)) (List.nodup_finRange 4)
  apply List.nodup_append.mpr
  refine ⟨pairs.map (fun _ _ eq => Origin.pair.inj eq), reps.map (fun _ _ eq => Origin.single.inj eq), ?_⟩
  intro s hs t ht
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hs
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ht
  exact Origin.noConfusion

variable {N : Network Ten}

private theorem antichain_of (C : Case N) (origins : List Origin) (distinct : origins.Nodup)
    (selected : ∀ s ∈ origins, Mandatory N s) :
    CrownOrProfiles.antichain (origins.map (close (graph N))) = true := by
  induction origins with
  | nil => rfl
  | cons s tail ih =>
    obtain ⟨sep, nodup⟩ := List.nodup_cons.mp distinct
    have rest := ih nodup (fun x h => selected x (List.mem_cons_of_mem _ h))
    have all : (tail.map (close (graph N))).all (CrownOrProfiles.incomparable (close (graph N) s)) = true := by
      rw [List.all_eq_true]
      intro m mem
      obtain ⟨t, inside, rfl⟩ := List.mem_map.mp mem
      have ne : s ≠ t := fun h => sep (h.symm ▸ inside)
      have ms := selected s (by simp)
      have mt := selected t (List.mem_cons_of_mem _ inside)
      have st := mandatory_forbids C ms ne (mandatory_nonempty mt)
      have ts := mandatory_forbids C mt (fun h => ne h.symm) (mandatory_nonempty ms)
      simp [CrownOrProfiles.incomparable, st, ts]
    simp only [List.map_cons, CrownOrProfiles.antichain, all, rest, Bool.and_self]

theorem legal (C : Case N) : CrownOrProfiles.legal (graph N).val (pairMask N).val (repeatMask N).val = true := by
  have degrees : CrownOrProfiles.flags.all (fun k =>
      (CrownOrProfiles.successors (graph N).val k).length ≤ 2) = true := by
    rw [List.all_eq_true]
    intro k hk
    have range : k < 4 := by simp [CrownOrProfiles.flags] at hk; omega
    exact decide_eq_true (degree_cap C ⟨k, range⟩)
  have pairs : (CrownOrProfiles.waysToStart (pairMask N).val).all (fun (i, j) =>
      CrownOrProfiles.incomparable (CrownOrProfiles.closure (graph N).val (1 <<< i))
        (CrownOrProfiles.closure (graph N).val (1 <<< j))) = true := by
    rw [ways_agree, List.all_eq_true]
    intro e he
    obtain ⟨k, chosen, rfl⟩ := List.mem_map.mp he
    have used : k ∈ pairsUsed N := by simpa only [pairsUsed, pair_bit] using chosen
    obtain ⟨i, iUsed⟩ := pairs_mandatory N used
    have ⟨fst, snd⟩ := pair_incomparable C ((mem_labels ..).mp iUsed)
    simpa [CrownOrProfiles.incomparable, close, Origin.seed, singletonSeed] using And.intro fst snd
  have chain := antichain_of C (mandatory N) (mandatory_nodup N) (fun _ h => mem_mandatory N h)
  rw [← mandatory_profile_list] at chain
  simp only [CrownOrProfiles.legal, degrees, pairs, chain, Bool.and_self]

def available (N : Network Ten) (t : Fin 4) : Bool :=
  !(repeatMask N).val.testBit t.val &&
    !((mandatory N).map (close (graph N))).any
      (CrownOrProfiles.includes (close (graph N) (.single t)))

theorem once_available (C : Case N) {t : Fin 4} (used : t ∈ onceUsed N) : available N t = true := by
  have one : (labels N (.single t)).card = 1 := of_decide_eq_true (List.mem_filter.mp used).2
  have usedOnce : (labels N (.single t)).Nonempty := card_pos.mp (by omega)
  have safe : ((mandatory N).map (close (graph N))).any
      (CrownOrProfiles.includes (close (graph N) (.single t))) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro yes
    obtain ⟨k, inList, hit⟩ := List.any_eq_true.mp yes
    obtain ⟨s, mem, rfl⟩ := List.mem_map.mp inList
    have mand := mem_mandatory N mem
    have ne : s ≠ .single t := by
      intro eq
      rw [eq] at mand
      change (labels N (.single t)).card = 2 at mand
      omega
    rw [mandatory_forbids C mand ne usedOnce] at hit
    contradiction
  simp [available, repeat_bit, singleRepeated, one, safe]

theorem options_eq (N : Network Ten) :
    CrownOrProfiles.optionalCosts (graph N).val (pairMask N).val (repeatMask N).val =
      [256, 256, 256] ++ (((List.finRange 4).filter (available N)).map fun t =>
        CrownOrProfiles.price (graph N).val (close (graph N) (.single t)) 1) := by
  unfold CrownOrProfiles.optionalCosts
  dsimp only
  have flags : CrownOrProfiles.flags = (List.finRange 4).map Fin.val := rfl
  rw [flags, List.filter_map, List.map_map, mandatory_profile_list]
  rfl

end CrownOrLegal
