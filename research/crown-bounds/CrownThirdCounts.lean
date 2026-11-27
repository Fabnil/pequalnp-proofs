import CrownThirdStructure
import CrownTenCases

namespace CrownThirdCounts

open CrownForks CrownForest CrownProfiles CrownVisibility CrownFirstAnd CrownFourProfiles
open CrownFourNetwork CrownFourNormal CrownThirdStructure CrownThirdStructure.Case Finset
open CrownProfileThree.Network (ones)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

variable {N : Network Ten}

private def classify (N : Network Ten) (i : Ten) : Fin 5 :=
  ⟨first N i, Nat.lt_succ_of_le (N.firstHot_le (singletonInput i))⟩

private def group (C : Case N) (t : ℕ) : Finset Ten :=
  (univ.erase C.a).filter (fun i => first N i = t)

private theorem memGroup (C : Case N) {i : Ten} {t : ℕ} :
    i ∈ group C t ↔ i ≠ C.a ∧ first N i = t := by
  simp [group]

private theorem groupSum (C : Case N) (w : Ten → ℕ) :
    (∑ i ∈ group C 0, w i) +
      ((∑ i ∈ group C 1, w i) + (∑ i ∈ group C 2, w i) +
        (∑ i ∈ group C 3, w i) + (∑ i ∈ group C 4, w i)) =
      ∑ i ∈ univ.erase C.a, w i := by
  have matchGroup (t : Fin 5) :
      ((univ.erase C.a).filter (fun i => classify N i = t)) = group C t.val := by
    ext
    simp [classify, group, Fin.ext_iff]
  have sum := sum_fiberwise (univ.erase C.a) (classify N) w
  simp only [matchGroup] at sum
  rw [Fin.sum_univ_succ, Fin.sum_univ_four] at sum
  exact sum

private theorem hidden_of_not_visible {i : Ten} (h : ¬ visible N i) :
    outputWeight N.forest (ones i) = 0 := by
  unfold visible at h
  omega

private theorem early_capacities (C : Case N) (t : Fin 4) (early : t ≠ 3) :
    ((group C t.val).filter (visible N)).card ≤ 1 ∧
      ((group C t.val).filter (fun i => ¬ visible N i)).card ≤ 1 := by
  have inside : t.val < 3 := by omega
  constructor
  · apply card_le_one.mpr
    intro i hi j hj
    by_contra ne
    obtain ⟨gi, vi⟩ := mem_filter.mp hi
    obtain ⟨gj, vj⟩ := mem_filter.mp hj
    have a := (memGroup C).mp gi
    have b := (memGroup C).mp gj
    exact C.visible_unique_early ne a.1 b.1 inside a.2 b.2 vi vj
  · apply card_le_one.mpr
    intro i hi j hj
    by_contra ne
    obtain ⟨gi, vi⟩ := mem_filter.mp hi
    obtain ⟨gj, vj⟩ := mem_filter.mp hj
    have a := (memGroup C).mp gi
    have b := (memGroup C).mp gj
    exact C.hidden_unique_early ne a.1 b.1 t early a.2 b.2 (hidden_of_not_visible vi) (hidden_of_not_visible vj)

private theorem early_cap (C : Case N) (t : Fin 4) (early : t ≠ 3) : (group C t.val).card ≤ 2 := by
  obtain ⟨v, h⟩ := early_capacities C t early
  have split := card_filter_add_card_filter_not (s := group C t.val) (visible N)
  omega

private theorem early_full (C : Case N) (t : Fin 4) (early : t ≠ 3) (two : (group C t.val).card = 2) :
    ∃ v u, v ∈ group C t.val ∧ u ∈ group C t.val ∧ v ≠ u ∧
      visible N v ∧ outputWeight N.forest (ones u) = 0 := by
  obtain ⟨v, h⟩ := early_capacities C t early
  have split := card_filter_add_card_filter_not (s := group C t.val) (visible N)
  obtain ⟨s, hs⟩ := card_pos.mp (show 0 < ((group C t.val).filter (visible N)).card by omega)
  obtain ⟨r, hr⟩ := card_pos.mp
    (show 0 < ((group C t.val).filter (fun i => ¬ visible N i)).card by omega)
  have sv := mem_filter.mp hs
  have rh := mem_filter.mp hr
  exact ⟨s, r, sv.1, rh.1, fun eq => rh.2 (eq ▸ sv.2), sv.2, hidden_of_not_visible rh.2⟩

private theorem last_cap (C : Case N) : (group C 3).card ≤ 2 := by
  apply profileCapacity N.forest C.test (group C 3) [false, false, false, true]
  · intro i hi
    exact last_group_profile i ((memGroup C).mp hi).2
  · exact fun i _ => (C.raw i).le
  · simp

private theorem cold_no_hot {i : Ten} (cold : first N i = 4) :
    true ∉ profile N.forest (singletonInput i) := by
  intro hot
  have bound := firstHot_lt N.forest (singletonInput i) hot
  change first N i < numShared N.forest at bound
  rw [cold, N.numShared_eq] at bound
  omega

private theorem cold_cap (C : Case N) : (group C 4).card ≤ 3 := by
  apply le_trans (card_le_card (t := CrownFourNormal.emptyProfiles N.forest) ?_)
    (emptyProfileCount N.forest C.valid C.test (fun i => (C.raw i).le) (by decide))
  intro i hi
  exact mem_filter.mpr ⟨mem_univ _, cold_no_hot ((memGroup C).mp hi).2⟩

private def price (N : Network Ten) (i : Ten) : ℕ :=
  2 ^ (4 - (profile N.forest (singletonInput i)).count true)

private def cost (C : Case N) (t : ℕ) : ℕ := ∑ i ∈ group C t, price N i

private theorem price_of_load {i : Ten} {k : ℕ}
    (load : (profile N.forest (singletonInput i)).count true ≤ k) :
    2 ^ (4 - k) ≤ price N i :=
  Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left load 4)

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
  exact price_of_load (k := 3) (rule _ _ _ _ notAll)

private theorem at_least_four_of_pairs {i : Ten}
    (pq : ¬ (signal N.forest 0 (singletonInput i) = true ∧ signal N.forest 1 (singletonInput i) = true))
    (rs : ¬ (signal N.forest 2 (singletonInput i) = true ∧ N.last (singletonInput i) = true)) :
    4 ≤ price N i := by
  have rule : ∀ p q r s : Bool, ¬ (p = true ∧ q = true) → ¬ (r = true ∧ s = true) →
      [p, q, r, s].count true ≤ 2 := by decide +kernel
  exact price_of_load (k := 2) (rule _ _ _ _ pq rs)

private theorem third_at_least_four {i : Ten} (start : first N i = 2) : 4 ≤ price N i := by
  have earlier := (N.firstHot_flags (singletonInput i) (by decide) start).2
  have p : (N.stages.bits (singletonInput i)).1 = false := earlier 0 (by decide)
  have q : (N.stages.bits (singletonInput i)).2.1 = false := earlier 1 (by decide)
  apply price_of_load (k := 2)
  rw [N.profile_eq, p, q]
  generalize (N.stages.bits (singletonInput i)).2.2 = r
  generalize N.last (singletonInput i) = s
  cases r <;> cases s <;> decide

private theorem third_at_least_eight {i : Ten} (start : first N i = 2)
    (off : N.last (singletonInput i) = false) : 8 ≤ price N i := by
  have earlier := (N.firstHot_flags (singletonInput i) (by decide) start).2
  have p : (N.stages.bits (singletonInput i)).1 = false := earlier 0 (by decide)
  have q : (N.stages.bits (singletonInput i)).2.1 = false := earlier 1 (by decide)
  apply price_of_load (k := 1)
  rw [N.profile_eq, p, q, off]
  cases (N.stages.bits (singletonInput i)).2.2 <;> decide

private theorem uniform_cost (C : Case N) (t base : ℕ)
    (atLeast : ∀ i ∈ group C t, base ≤ price N i) :
    base * (group C t).card ≤ cost C t := by
  calc
    base * (group C t).card = ∑ _i ∈ group C t, base := by simp [Nat.mul_comm]
    _ ≤ cost C t := sum_le_sum atLeast

private theorem early_cost (C : Case N) (t : Fin 4) (early : t ≠ 3) (base : ℕ)
    (atLeast : ∀ i ∈ group C t.val, base ≤ price N i)
    (bonus : ∀ i ∈ group C t.val, N.last (singletonInput i) = false → 2 * base ≤ price N i) :
    2 * base * (group C t.val).card - base ≤ cost C t.val := by
  have cap := early_cap C t early
  have uniform := uniform_cost C t.val base atLeast
  by_cases empty : (group C t.val).card = 0
  · simp [empty]
  by_cases single : (group C t.val).card = 1
  · rw [single] at uniform ⊢
    omega
  have filled : (group C t.val).card = 2 := by omega
  obtain ⟨v, u, hv, hu, vu, _, hidden⟩ := early_full C t early filled
  have read := C.hidden_early_reads ((memGroup C).mp hu).1 hidden t early ((memGroup C).mp hu).2
  have no : N.last (singletonInput v) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro on
    exact C.hidden_saturates vu.symm hidden t early (by omega : 0 < N.stages.rawAt t u)
      (by omega : 0 < N.stages.rawAt 3 u)
      (N.firstHot_flags (singletonInput v) t.isLt ((memGroup C).mp hv).2).1 on
  have subset : ({v, u} : Finset Ten) ⊆ group C t.val := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have bound := sum_le_sum_of_subset_of_nonneg (f := price N) subset (fun _ _ _ => Nat.zero_le _)
  rw [sum_insert (by simpa using vu), sum_singleton] at bound
  have lowV := bonus v hv no
  have lowU := atLeast u hu
  change price N v + price N u ≤ cost C t.val at bound
  rw [filled]
  omega

private theorem last_weight (i : Ten) (firstI : first N i = 3) : price N i = 8 := by
  unfold price
  rw [last_group_profile i firstI]
  rfl

private theorem cold_weight {i : Ten} (firstI : first N i = 4) : price N i = 16 := by
  have zero : (profile N.forest (singletonInput i)).count true = 0 :=
    List.count_eq_zero.mpr (cold_no_hot firstI)
  rw [price, zero]
  rfl

private theorem counts (C : Case N) :
    1 + (group C 4).card + (group C 0).card + (group C 1).card +
      (group C 2).card + (group C 3).card = 10 := by
  have sum := groupSum C (fun _ => 1)
  simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one] at sum
  have remaining : (univ.erase C.a).card = 9 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  omega

private theorem total_cost (C : Case N) :
    2 + cost C 4 + cost C 0 + cost C 1 + cost C 2 + cost C 3 ≤ 64 := by
  have packed := packing64 N.forest C.valid C.test (fun i => (C.raw i).le) N.numShared_eq N.twoReads_valid
  change ∑ i : Ten, price N i ≤ 64 at packed
  have sum := groupSum C (price N)
  change cost C 0 + (cost C 1 + cost C 2 + cost C 3 + cost C 4) = _ at sum
  have erase := sum_erase_add (s := univ) (f := price N) (mem_univ C.a)
  have anchor : price N C.a = 2 := by rw [price, C.anchorProfile]; rfl
  omega

private theorem third_filled (C : Case N) :
    (group C 4).card = 1 ∧ (group C 0).card = 2 ∧ (group C 1).card = 2 ∧
      (group C 2).card = 2 ∧ (group C 3).card = 2 := by
  have cold := uniform_cost C 4 16 (fun i hi => (cold_weight ((memGroup C).mp hi).2).ge)
  have last := uniform_cost C 3 8 (fun i hi => (last_weight i ((memGroup C).mp hi).2).ge)
  have bonus (t : ℕ) (i : Ten) (mem : i ∈ group C t) (off : N.last (singletonInput i) = false) :
      4 ≤ price N i :=
    at_least_four_of_pairs (C.noBoth i ((memGroup C).mp mem).1) (fun h => by rw [off] at h; tauto)
  have p := early_cost C 0 (by decide) 2 (fun i _ => at_least_two C i) (bonus 0)
  have q := early_cost C 1 (by decide) 2 (fun i _ => at_least_two C i) (bonus 1)
  have r := early_cost C 2 (by decide) 4 (fun _ hi => third_at_least_four ((memGroup C).mp hi).2)
    (fun _ hi off => third_at_least_eight ((memGroup C).mp hi).2 off)
  change 4 * (group C 0).card - 2 ≤ cost C 0 at p
  change 4 * (group C 1).card - 2 ≤ cost C 1 at q
  change 8 * (group C 2).card - 4 ≤ cost C 2 at r
  have budget := total_cost C
  exact CrownTenCases.thirdFillsAll _ _ _ _ _ (cold_cap C) (early_cap C 0 (by decide))
    (early_cap C 1 (by decide)) (early_cap C 2 (by decide)) (last_cap C) (counts C) (by omega)

private theorem allThirdOff (C : Case N) (filled : (group C 3).card = 2) {i : Ten}
    (mem : i ∈ group C 2) : N.last (singletonInput i) = false := by
  have firstI := ((memGroup C).mp mem).2
  obtain ⟨x, hx, y, hy, ne⟩ := one_lt_card.mp (show 1 < (group C 3).card by omega)
  obtain ⟨xa, firstX⟩ := (memGroup C).mp hx
  obtain ⟨_, firstY⟩ := (memGroup C).mp hy
  have xi : x ≠ i := by intro eq; rw [eq] at firstX; omega
  have yi : y ≠ i := by intro eq; rw [eq] at firstY; omega
  apply Bool.eq_false_of_not_eq_true
  intro on
  by_cases vx : visible N x
  · have vy : visible N y := by
      by_contra invisible
      exact C.last_cannot_mix ne firstX firstY vx (hidden_of_not_visible invisible)
    have hotX := N.hot_of_firstHot_lt (singletonInput x) (by change first N x < 4; omega)
    have hotY := N.hot_of_firstHot_lt (singletonInput y) (by change first N y < 4; omega)
    exact twoVisible N.forest C.test ne xi yi hotX hotY vx vy (C.raw x).le (C.raw y).le
      (firstX.trans firstY.symm) (by
        change signal N.forest (first N x) (singletonInput i) = true
        rw [firstX]
        exact on)
  · have hidden := hidden_of_not_visible vx
    obtain ⟨r, s⟩ := C.hidden_last_group_reads xa firstX hidden
    exact C.hidden_saturates xi hidden 2 (by decide) (by omega : 0 < N.stages.rawAt 2 x)
      (by omega : 0 < N.stages.rawAt 3 x) (N.firstHot_flags (singletonInput i) (by decide) firstI).1 on

theorem impossible (C : Case N) : False := by
  obtain ⟨cold, p, q, r, s⟩ := third_filled C
  obtain ⟨_, j, _, hj, _, _, hidden⟩ := early_full C 2 (by decide) r
  obtain ⟨ja, firstJ⟩ := (memGroup C).mp hj
  obtain ⟨readR, readS, _⟩ := C.hidden_early_reads ja hidden 2 (by decide) firstJ
  have boundPQ (t : ℕ) (early : t < 2) (i : Ten) (mem : i ∈ group C t) : 4 ≤ price N i := by
    obtain ⟨ia, firstI⟩ := (memGroup C).mp mem
    have ji : j ≠ i := by intro eq; rw [eq] at firstJ; omega
    apply at_least_four_of_pairs (C.noBoth i ia)
    rintro ⟨onR, onS⟩
    exact C.hidden_saturates ji hidden 2 (by decide) (by omega : 0 < N.stages.rawAt 2 j)
      (by omega : 0 < N.stages.rawAt 3 j) onR onS
  have c0 := uniform_cost C 0 4 (boundPQ 0 (by decide))
  have c1 := uniform_cost C 1 4 (boundPQ 1 (by decide))
  have c2 := uniform_cost C 2 8 (fun i hi => third_at_least_eight ((memGroup C).mp hi).2 (allThirdOff C s hi))
  have c3 := uniform_cost C 3 8 (fun i hi => (last_weight i ((memGroup C).mp hi).2).ge)
  have c4 := uniform_cost C 4 16 (fun _ hi => (cold_weight ((memGroup C).mp hi).2).ge)
  have total := total_cost C
  omega

theorem noOverlapAtThird : ¬ HasOverlapAt 2 := by
  intro hyp
  obtain ⟨N, ⟨C⟩⟩ := CrownThirdStructure.ofOverlap hyp
  exact impossible C

theorem crownTenTwoCases
    (small : RepSizeAtMost (fun u v : Ten => decide (u ≠ v)) 33) :
    HasOverlapAt 3 ∨ CrownFirstOr.HasOrPrefix 4 :=
  (crownTenThreeCases small).resolve_left noOverlapAtThird

end CrownThirdCounts
