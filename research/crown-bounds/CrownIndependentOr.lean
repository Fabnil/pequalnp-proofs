import CrownOrIncident
import CrownFourthCounts

namespace CrownIndependentOr

open CrownForks CrownForest CrownFourNetwork CrownFourNormal CrownPairFormula
open CrownAllOrModel CrownOrSupport CrownOrPacking Finset
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open scoped Classical

private def group (N : Network Ten) (k : ℕ) : Finset Ten :=
  univ.filter (fun i => (support N i).card = k)

private theorem in_group {N : Network Ten} {k : ℕ} {i : Ten} :
    i ∈ group N k ↔ (support N i).card = k := by simp [group]

private theorem group_sum (N : Network Ten) (cap : ∀ i, (support N i).card ≤ 2) (w : Ten → ℕ) :
    (∑ i ∈ group N 0, w i) + (∑ i ∈ group N 1, w i) + (∑ i ∈ group N 2, w i) = ∑ i : Ten, w i := by
  let classify (i : Ten) : Fin 3 := ⟨(support N i).card, Nat.lt_succ_of_le (cap i)⟩
  have term (k : Fin 3) :
      (univ.filter (fun i => classify i = k)) = group N k.val := by
    ext
    simp [group, classify, Fin.ext_iff]
  have sum := sum_fiberwise (univ : Finset Ten) classify w
  rw [Fin.sum_univ_three] at sum
  simpa only [term, show (0 : Fin 3).val = 0 by rfl, show (1 : Fin 3).val = 1 by rfl,
    show (2 : Fin 3).val = 2 by rfl] using sum

private theorem group_weights (N : Network Ten) (k : ℕ) :
    (∑ i ∈ group N k, 2 ^ (2 - (support N i).card)) =
      (group N k).card * 2 ^ (2 - k) := by
  apply sum_const_nat
  intro i mem
  rw [in_group.mp mem]

private theorem packing_small {N : Network Ten} (C : Case N)
    (read : ∀ i, (support N i).card + reads (output N) (.inr i) ≤ 2) :
    ∑ i : Ten, 2 ^ (2 - (support N i).card) ≤ 16 := by
  have packed := profilePacking (output N) (fun i => flagValues N (singletonInput i))
    C.tests univ (fun i => 2 + (support N i).card) 4 (by
      intro i _
      have counted : (∑ k ∈ support N i, reads (output N) (.inl k)) ≤ (support N i).card * 2 := by
        calc
          _ ≤ ∑ _k ∈ support N i, (2 : ℕ) :=
            sum_le_sum fun k _ => output_flag_cap N C.valid k
          _ = _ := by simp
      have bound := read i
      change reads (output N) (.inr i) + (∑ k ∈ support N i, reads (output N) (.inl k)) ≤ _
      omega) (fun i _ => by have bound := read i; omega)
  have exponent (i : Ten) : 4 - (2 + (support N i).card) = 2 - (support N i).card := by omega
  simpa only [exponent, show (2 : ℕ) ^ 4 = 16 by rfl] using packed

private theorem numbers (c s d : ℕ) (count : c + s + d = 10) (mass : 4 * c + 2 * s + d ≤ 16)
    (singles : s ≤ 4) (doubles : d ≤ 6) :
    3 ≤ s ∧ d = 6 := by omega

private theorem four_flags : Fintype.card Flag = 4 := by decide +kernel

private theorem double_universe_card : ((univ : Finset Flag).powersetCard 2).card = 6 := by
  rw [card_powersetCard, card_univ, four_flags]
  rfl

private theorem doubles_avoiding_card (k : Flag) :
    (((univ : Finset Flag).erase k).powersetCard 2).card = 3 := by
  rw [card_powersetCard, card_erase_of_mem (mem_univ _), card_univ, four_flags]
  rfl

theorem impossible {N : Network Ten} (C : Case N)
    (independent : ∀ s t, N.readsFlag s t = 0) : False := by
  have read (i : Ten) : (support N i).card + reads (output N) (.inr i) ≤ 2 := by
    rw [support_eq_readers N C.pure independent i]
    exact C.read_bound i
  have cap (i : Ten) : (support N i).card ≤ 2 := le_trans (Nat.le_add_right ..) (read i)
  have hidden {i : Ten} (member : i ∈ group N 2) : reads (output N) (.inr i) = 0 := by
    have this := read i
    rw [in_group.mp member] at this
    omega
  have rawOne {i : Ten} (member : i ∈ group N 1) : reads (output N) (.inr i) ≤ 1 := by
    have this := read i
    rw [in_group.mp member] at this
    omega
  have cnt : (group N 0).card + (group N 1).card + (group N 2).card = 10 := by
    simpa only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one, card_univ, Fintype.card_fin]
      using group_sum N cap (fun _ => 1)
  have mass : 4 * (group N 0).card + 2 * (group N 1).card + (group N 2).card ≤ 16 := by
    have split := group_sum N cap (fun i => 2 ^ (2 - (support N i).card))
    rw [group_weights, group_weights, group_weights] at split
    have bound := packing_small C read
    rw [← split] at bound
    simpa only [show (2 : ℕ) ^ (2 - 0) = 4 by rfl, show (2 : ℕ) ^ (2 - 1) = 2 by rfl,
      Nat.sub_self, pow_zero, Nat.mul_one, Nat.mul_comm 4, Nat.mul_comm 2] using bound
  have doubleInj : Set.InjOn (support N) (group N 2 : Set Ten) := by
    intro i hi j _ same
    by_contra ne
    exact C.hidden_no_superset ne (hidden hi) same.subset
  have allDoubles : Set.MapsTo (support N) (group N 2 : Set Ten)
      ((univ : Finset Flag).powersetCard 2 : Set (Finset Flag)) := by
    intro i hi
    exact mem_powersetCard.mpr ⟨subset_univ _, in_group.mp hi⟩
  have capD := card_le_card_of_injOn (support N) allDoubles doubleInj
  rw [double_universe_card] at capD
  have witness (k : Flag) : ∃ i ∈ group N 2, k ∈ support N i := by
    by_contra! missing
    have target : Set.MapsTo (support N) (group N 2 : Set Ten)
        (((univ : Finset Flag).erase k).powersetCard 2 : Set (Finset Flag)) := by
      intro i hi
      refine mem_powersetCard.mpr ⟨?_, in_group.mp hi⟩
      intro t ht
      exact mem_erase.mpr ⟨fun eq => missing i hi (eq ▸ ht), mem_univ t⟩
    have small := card_le_card_of_injOn (support N) target doubleInj
    rw [doubles_avoiding_card] at small
    omega
  have singleInj : Set.InjOn (support N) (group N 1 : Set Ten) := by
    intro i hi j hj same
    by_contra ne
    obtain ⟨k, only⟩ := card_eq_one.mp (in_group.mp hi)
    obtain ⟨a, ha, contains⟩ := witness k
    have different {b : Ten} (s : b ∈ group N 1) : b ≠ a := by
      intro eq
      have one := in_group.mp s
      have two := in_group.mp ha
      rw [eq] at one
      omega
    have within : support N i ⊆ support N a := by
      rw [only]
      exact singleton_subset_iff.mpr contains
    exact C.repeated_no_superset ne (different hi) (different hj) same within (rawOne hi) (rawOne hj)
  have capS := card_le_card_of_injOn (support N)
    (show Set.MapsTo (support N) (group N 1 : Set Ten)
        ((univ : Finset Flag).powersetCard 1 : Set (Finset Flag)) from
      fun _ h => mem_powersetCard.mpr ⟨subset_univ _, in_group.mp h⟩) singleInj
  rw [card_powersetCard, card_univ, four_flags, Nat.choose_one_right] at capS
  obtain ⟨s, d⟩ := numbers _ _ _ cnt mass capS capD
  have every : (group N 2).image (support N) = (univ : Finset Flag).powersetCard 2 := by
    apply eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨i, hi, rfl⟩ := mem_image.mp ha
      exact allDoubles hi
    · rw [card_image_of_injOn doubleInj, double_universe_card, d]
  obtain ⟨a, ha⟩ := card_pos.mp (Nat.zero_lt_of_lt s)
  obtain ⟨k, one⟩ := card_eq_one.mp (in_group.mp ha)
  apply C.incident_at a k one _ (rawOne ha)
  intro l ne
  have has : ({k, l} : Finset Flag) ∈ (univ : Finset Flag).powersetCard 2 :=
    mem_powersetCard.mpr ⟨subset_univ _, by simp [ne.symm]⟩
  rw [← every] at has
  obtain ⟨i, hi, same⟩ := mem_image.mp has
  exact ⟨i, same, hidden hi⟩

theorem requiresLink {N : Network Ten} (C : Case N) : ∃ s t, 0 < N.readsFlag s t := by
  by_contra! none
  exact impossible C fun s t => Nat.eq_zero_of_le_zero (none s t)

theorem crownTenRequiresLink (small : RepSizeAtMost (fun u v : Ten => decide (u ≠ v)) 33) :
    ∃ N : Network Ten, Case N ∧ ∃ s t, 0 < N.readsFlag s t := by
  obtain ⟨N, C⟩ := of_orPrefix (CrownFourthCounts.crownTenOnlyOr small)
  exact ⟨N, C, requiresLink C⟩

end CrownIndependentOr
