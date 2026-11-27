import CrownOrOrigins

namespace CrownOrOriginGroups

open CrownForks CrownFourNetwork CrownFourNormal CrownAllOrModel CrownOrSupport CrownOrGraph
open CrownOrOrigins CrownVisibility CrownProfiles CrownPairFormula Finset

variable {N : Network Ten}

def labels (N : Network Ten) (s : Origin) : Finset Ten := univ.filter (fun i => origin N i = s)

@[simp] theorem mem_labels (N : Network Ten) (i : Ten) (s : Origin) :
    i ∈ labels N s ↔ origin N i = s := by simp [labels]

private def key : Origin → Unit ⊕ (Fin 4 ⊕ Fin 6)
  | .cold => .inl ()
  | .single r => .inr (.inl r)
  | .pair k => .inr (.inr k)

theorem sum_labels (N : Network Ten) (w : Ten → ℕ) :
    (∑ i ∈ labels N .cold, w i) + ((∑ t : Fin 4, ∑ i ∈ labels N (.single t), w i) +
      (∑ k : Fin 6, ∑ i ∈ labels N (.pair k), w i)) = ∑ i : Ten, w i := by
  let code (i : Ten) := key (origin N i)
  have cold (a : Unit) : (univ.filter (fun i => code i = .inl a)) = labels N .cold := by
    cases a
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_labels, code]
    cases origin N i <;> simp [key]
  have single (t : Fin 4) : (univ.filter (fun i => code i = .inr (.inl t))) = labels N (.single t) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_labels, code]
    cases origin N i <;> simp [key]
  have paired (k : Fin 6) : (univ.filter (fun i => code i = .inr (.inr k))) = labels N (.pair k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_labels, code]
    cases origin N i <;> simp [key]
  have sum := sum_fiberwise (univ : Finset Ten) code w
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at sum
  simpa only [cold, single, paired, Fintype.sum_unique] using sum

theorem included_iff_subset (C : Case N) {i j : Ten} {s t : Origin}
    (isI : origin N i = s) (isJ : origin N j = t) :
    CrownOrProfiles.includes (close (graph N) t) (close (graph N) s) = true ↔ support N i ⊆ support N j := by
  have first := realized C i
  have second := realized C j
  rw [isI] at first
  rw [isJ] at second
  rw [← first, ← second, included_bits]
  constructor
  · intro all k mem
    have inI := (mem_support N i k).mp mem
    have bit := all (stage k) ((actual_bits N i _).trans inI)
    exact (mem_support N j k).mpr ((actual_bits N j _).symm.trans bit)
  · intro contained t on
    let k := stageEquiv.symm t
    have index : stage k = t := stageEquiv.apply_symm_apply t
    have earlier := (actual_bits N i (stage k)).symm
    rw [index] at earlier
    have active : flagValues N (singletonInput i) k = true := by
      change activeBit N i (stage k) = true
      rw [index]
      exact earlier.trans on
    have mem := (mem_support N i k).mpr active
    have after := (actual_bits N j (stage k)).trans ((mem_support N j k).mp (contained mem))
    simpa only [index] using after

theorem pair_hidden (C : Case N) {i : Ten} {k : Fin 6} (member : i ∈ labels N (.pair k)) :
    reads (output N) (.inr i) = 0 := by
  have bound := CrownOrOrigins.read_bound C i
  rw [(mem_labels ..).mp member, Origin.count] at bound
  omega

theorem single_read (C : Case N) {i : Ten} {k : Fin 4} (member : i ∈ labels N (.single k)) :
    reads (output N) (.inr i) ≤ 1 := by
  have bound := CrownOrOrigins.read_bound C i
  rw [(mem_labels ..).mp member, Origin.count] at bound
  omega

private theorem no_hot_iff_zero {i : Ten} :
    true ∉ profile N.forest (singletonInput i) ↔ (actual N i).val = 0 := by
  have rule : ∀ a b c d : Bool, true ∉ [a, b, c, d] ↔ word4 a b c d = 0 := by decide +kernel
  exact rule _ _ _ _

theorem cold_cap (C : Case N) : (labels N .cold).card ≤ 3 := by
  apply le_trans (card_le_card (t := CrownFourNormal.emptyProfiles N.forest) ?_)
    (emptyProfileCount N.forest C.valid C.test (fun i => (C.raw i).le) (by decide))
  intro i hi
  have eq := realized C i
  rw [(mem_labels ..).mp hi, cold_closure] at eq
  exact mem_filter.mpr ⟨mem_univ _, no_hot_iff_zero.mpr eq⟩

theorem pair_cap (C : Case N) (k : Fin 6) : (labels N (.pair k)).card ≤ 1 := by
  apply card_le_one.mpr
  intro i hi j hj
  by_contra ne
  have same := ((mem_labels ..).mp hi).trans ((mem_labels ..).mp hj).symm
  exact C.hidden_no_superset ne (pair_hidden C hi) (support_of_same C same).subset

theorem single_cap (C : Case N) (k : Fin 4) : (labels N (.single k)).card ≤ 2 := by
  by_cases empty : labels N (.single k) = ∅
  · simp [empty]
  obtain ⟨a, base⟩ := nonempty_iff_ne_empty.mpr empty
  apply profileCapacity N.forest C.test (labels N (.single k)) (profile N.forest (singletonInput a))
  · intro i hi
    have same := ((mem_labels ..).mp hi).trans ((mem_labels ..).mp base).symm
    have bits := bits_eq_of_support_eq N (support_of_same C same)
    exact congrArg (fun f : Flag → Bool => [f (some 0), f (some 1), f (some 2), f none]) bits
  · exact fun i _ => (C.raw i).le
  · by_contra off
    have zero := no_hot_iff_zero.mp off
    rw [realized C a, (mem_labels ..).mp base] at zero
    exact single_nonzero (graph N) k zero

def Mandatory (N : Network Ten) : Origin → Prop
  | .cold => False
  | .single k => (labels N (.single k)).card = 2
  | .pair k => (labels N (.pair k)).Nonempty

theorem mandatory_nonempty {s : Origin} (mand : Mandatory N s) : (labels N s).Nonempty := by
  cases s with
  | cold => exact mand.elim
  | single k =>
    change (labels N (.single k)).card = 2 at mand
    exact card_pos.mp (by omega)
  | pair k => exact mand

theorem mandatory_forbids (C : Case N) {s t : Origin} (mand : Mandatory N s)
    (different : s ≠ t) (used : (labels N t).Nonempty) :
    CrownOrProfiles.includes (close (graph N) t) (close (graph N) s) = false := by
  obtain ⟨j, hj⟩ := used
  have atJ := (mem_labels N j t).mp hj
  have neq (i : Ten) (atI : origin N i = s) : i ≠ j := by
    intro same
    rw [same, atJ] at atI
    exact different atI.symm
  apply Bool.eq_false_of_not_eq_true
  intro incl
  cases s with
  | cold => exact mand
  | pair k =>
    obtain ⟨i, hi⟩ := mand
    have atI := (mem_labels ..).mp hi
    exact C.hidden_no_superset (neq i atI) (pair_hidden C hi)
      ((included_iff_subset C atI atJ).mp incl)
  | single k =>
    change (labels N (.single k)).card = 2 at mand
    obtain ⟨i, hi, a, ha, ia⟩ := one_lt_card.mp (by omega : 1 < (labels N (.single k)).card)
    have atI := (mem_labels ..).mp hi
    have atA := (mem_labels ..).mp ha
    exact C.repeated_no_superset ia (neq i atI) (neq a atA) (support_of_same C (atI.trans atA.symm))
      ((included_iff_subset C atI atJ).mp incl) (single_read C hi) (single_read C ha)

end CrownOrOriginGroups
