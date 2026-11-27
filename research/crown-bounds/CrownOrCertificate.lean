import CrownOrLegal

namespace CrownOrCertificate

open CrownFourNetwork CrownFourNormal CrownOrSupport CrownOrGraph CrownOrOrigins
open CrownOrOriginGroups CrownOrPrices CrownOrLegal Finset

private theorem fin_sum_as_list {n : ℕ} (f : Fin n → ℕ) :
    (∑ i : Fin n, f i) = ((List.finRange n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, ih]
    rfl

private theorem capacity_one {A : Type} (l : List A) (count price : A → ℕ) (cap : ∀ x, count x ≤ 1) :
    (l.map fun x => count x * price x).sum =
      ((l.filter fun x => decide (0 < count x)).map price).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have one := cap a
    have cases : count a = 0 ∨ count a = 1 := by omega
    rcases cases with h | h <;> simp [h, ih]

private theorem capacity_two {A : Type} (l : List A) (count price : A → ℕ) (cap : ∀ x, count x ≤ 2) :
    (l.map fun x => count x * price x).sum =
      ((l.filter fun x => decide (count x = 1)).map price).sum +
      2 * ((l.filter fun x => decide (count x = 2)).map price).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have two := cap a
    have cases : count a = 0 ∨ count a = 1 ∨ count a = 2 := by omega
    rcases cases with h | h | h <;> simp [h, ih, Nat.mul_add] <;> omega

variable {N : Network Ten}

private theorem sum_by_choices (C : Case N) (w : Origin → ℕ) :
    (∑ i : Ten, w (origin N i)) =
      (labels N .cold).card * w .cold + ((onceUsed N).map fun t => w (.single t)).sum +
        2 * ((repeatedUsed N).map fun t => w (.single t)).sum +
        ((pairsUsed N).map fun k => w (.pair k)).sum := by
  have source := sum_labels N (fun i => w (origin N i))
  have group (s : Origin) : (∑ i ∈ labels N s, w (origin N i)) = (labels N s).card * w s := by
    apply sum_const_nat
    intro i mem
    rw [(mem_labels ..).mp mem]
  simp only [group] at source
  have one := capacity_one (List.finRange 6) (fun k => (labels N (.pair k)).card)
    (fun k => w (.pair k)) (pair_cap C)
  have two := capacity_two (List.finRange 4) (fun t => (labels N (.single t)).card)
    (fun t => w (.single t)) (single_cap C)
  rw [fin_sum_as_list, fin_sum_as_list, one, two] at source
  rw [← source]
  change (labels N .cold).card * w .cold +
      (((onceUsed N).map fun t => w (.single t)).sum +
        2 * ((repeatedUsed N).map fun t => w (.single t)).sum +
        ((pairsUsed N).map fun k => w (.pair k)).sum) = _
  ac_rfl

private def chosen (N : Network Ten) : List ℕ :=
  List.replicate (labels N .cold).card 256 ++ ((onceUsed N).map fun t =>
    CrownOrProfiles.price (graph N).val (close (graph N) (.single t)) 1)

private theorem filter_sublist_of_imp {A : Type} (l : List A) (p q : A → Bool)
    (h : ∀ a ∈ l, p a = true → q a = true) : (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    have tail := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    cases picked : p a with
    | false =>
      cases allowed : q a with
      | false => simpa [picked, allowed] using tail
      | true => simpa [picked, allowed] using List.Sublist.cons a tail
    | true =>
      have allowed := h a (by simp) picked
      simpa [picked, allowed] using List.Sublist.cons_cons a tail

private theorem chosen_sublist (C : Case N) :
    (chosen N).Sublist (CrownOrProfiles.optionalCosts (graph N).val (pairMask N).val (repeatMask N).val) := by
  rw [options_eq]
  refine List.Sublist.append ((List.replicate_sublist_replicate _).mpr (cold_cap C)) ?_
  apply List.Sublist.map
  exact filter_sublist_of_imp (List.finRange 4)
    (fun t => decide ((labels N (.single t)).card = 1)) (available N)
    (fun t mem one => once_available C (List.mem_filter.mpr ⟨mem, one⟩))

private theorem count (C : Case N) :
    CrownOrProfiles.mandatoryCount (graph N).val (pairMask N).val (repeatMask N).val + (chosen N).length = 10 := by
  have counts := sum_by_choices C (fun _ => 1)
  simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one, card_univ, Fintype.card_fin,
    List.map_const', List.sum_replicate_nat] at counts
  unfold CrownOrProfiles.mandatoryCount
  rw [paired_profiles, repeated_profiles, List.length_map, List.length_map]
  have len : (chosen N).length = (labels N .cold).card + (onceUsed N).length := by
    simp [chosen]
  rw [len]
  exact (by
    rw [counts]
    ac_rfl)

private theorem cold_price : ∀ graph : Fin 64, CrownOrProfiles.price graph.val 0 2 = 256 := by decide +kernel

private theorem total_cost (C : Case N) :
    CrownOrProfiles.mandatoryCost (graph N).val (pairMask N).val (repeatMask N).val + (chosen N).sum ≤ 1024 := by
  let w (s : Origin) := CrownOrProfiles.price (graph N).val (close (graph N) s) (2 - s.count)
  have counted := sum_by_choices C w
  have atCold : w .cold = 256 := by
    change CrownOrProfiles.price (graph N).val (close (graph N) .cold) 2 = 256
    rw [cold_closure]
    exact cold_price (graph N)
  have all : ∑ i : Ten, w (origin N i) ≤ 1024 := cost_budget C
  rw [counted, atCold] at all
  unfold CrownOrProfiles.mandatoryCost
  rw [paired_profiles, repeated_profiles, List.map_map, List.map_map]
  have optional : (chosen N).sum = (labels N .cold).card * 256 +
      ((onceUsed N).map fun t => w (.single t)).sum := by
    simp only [chosen, List.sum_append, List.sum_replicate_nat]
    rfl
  rw [optional]
  change ((pairsUsed N).map fun k => w (.pair k)).sum +
    2 * ((repeatedUsed N).map fun t => w (.single t)).sum +
      ((labels N .cold).card * 256 + ((onceUsed N).map fun t => w (.single t)).sum) ≤ 1024
  convert all using 1
  ac_rfl

theorem impossible (C : Case N) (nonzero : (graph N).val ≠ 0) : False :=
  CrownOrProfiles.noTenWithConnection (graph N) (pairMask N) (repeatMask N)
    nonzero (legal C) (chosen N) (chosen_sublist C) (count C) (total_cost C)

end CrownOrCertificate
