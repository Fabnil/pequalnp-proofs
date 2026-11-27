import CrownFourthStructure
import CrownSignalReads

namespace CrownFourthStructure.Case

open CrownForks CrownForest CrownFourNetwork CrownFourNormal CrownVisibility CrownFirstAnd
open CrownOrStages CrownOrReaders CrownProfiles Finset
open CrownProfileThree.Network (ones)

variable {N : Network Ten} (C : CrownFourthStructure.Case N)

theorem early_cases (k : Fin 3) : k = C.p ∨ k = C.q ∨ k = C.missing := by
  have pk := C.p.isLt
  have qk := C.q.isLt
  have mk := C.missing.isLt
  have pq : C.p.val ≠ C.q.val := fun eq => C.pq (Fin.ext eq)
  have pm : C.p.val ≠ C.missing.val := fun eq => C.pm (Fin.ext eq)
  have qm : C.q.val ≠ C.missing.val := fun eq => C.qm (Fin.ext eq)
  have options : k.val = C.p.val ∨ k.val = C.q.val ∨ k.val = C.missing.val := by
    have range := k.isLt
    omega
  rcases options with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

include C in
theorem prior_pure (k : Fin 3) : orPrefix N.forest (k.castSucc.val + 1) :=
  orPrefix_mono N.forest (by
    change k.val + 1 ≤ 3
    have range := k.isLt
    omega) C.early

include C in
theorem link_implies {s t : Fin 3} (used : N.link s t) (x : Ten → Bool) :
    signal N.forest s.val x ≤ signal N.forest t.val x :=
  N.or_flag_implies s t.castSucc (C.prior_pure t) used x

theorem possible_links {s t : Fin 3} (used : N.link s t) : s = C.missing ∧ (t = C.p ∨ t = C.q) := by
  have forward : s.val < t.val := N.readsFlag_forward s t.castSucc used
  rcases C.early_cases s with hs | hs | hs
  · subst s
    rcases C.early_cases t with ht | ht | ht
    · subst t
      exact (Nat.lt_irrefl _ forward).elim
    · subst t
      exact (C.pNotQ (C.link_implies used)).elim
    · subst t
      exact (C.p_not_implies_missing (C.link_implies used)).elim
  · subst s
    rcases C.early_cases t with ht | ht | ht
    · subst t
      exact (C.qNotP (C.link_implies used)).elim
    · subst t
      exact (Nat.lt_irrefl _ forward).elim
    · subst t
      exact (C.q_not_implies_missing (C.link_implies used)).elim
  · subst s
    refine ⟨rfl, ?_⟩
    rcases C.early_cases t with ht | ht | ht
    · exact Or.inl ht
    · exact Or.inr ht
    · subst t
      exact (Nat.lt_irrefl _ forward).elim

theorem no_two_links : ¬ (N.link C.missing C.p ∧ N.link C.missing C.q) := by
  rintro ⟨p, q⟩
  exact C.missing_not_implies_both ⟨C.link_implies p, C.link_implies q⟩

include C in
theorem direct_on (t : Fin 3) (i : Ten) (read : 0 < N.stages.rawAt t.castSucc i) :
    signal N.forest t.val (singletonInput i) = true :=
  N.direct_or_on t.castSucc i (C.prior_pure t) read

include C in
theorem no_input_no_signal (t : Fin 3) (i : Ten) (raw : N.stages.rawAt t.castSucc i = 0)
    (noRise : ∀ s, N.link s t → signal N.forest s.val (singletonInput i) = false) :
    signal N.forest t.val (singletonInput i) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro on
  rcases N.or_stage_reason t.castSucc (C.prior_pure t) i on with pos | ⟨s, used, active⟩
  · rw [raw] at pos
    omega
  · rw [noRise s used] at active
    contradiction

theorem missing_ne_last : C.missing.castSucc ≠ (3 : Fin 4) := by
  intro eq
  have range := C.missing.isLt
  have val : C.missing.val = 3 := congrArg Fin.val eq
  omega

theorem missing_ne_p : C.missing.castSucc ≠ C.p.castSucc := fun h =>
  C.pm (Fin.ext (congrArg Fin.val h).symm)

theorem missing_ne_q : C.missing.castSucc ≠ C.q.castSucc := fun h =>
  C.qm (Fin.ext (congrArg Fin.val h).symm)

theorem hidden_second {i : Ten} (ia : i ≠ C.a) (absent : outputWeight N.forest (ones i) = 0) :
    0 < N.stages.rawAt C.p.castSucc i ∨ 0 < N.stages.rawAt C.q.castSucc i ∨
      0 < N.stages.rawAt 3 i := by
  have missing := C.hidden_reads_missing ia absent
  have total := N.rawTotal i
  rw [absent, Nat.add_zero, C.raw] at total
  have other : ∃ k : Fin 4, k ≠ C.missing.castSucc ∧ 0 < N.stages.rawAt k i := by
    by_contra! none
    have weight : ∑ k : Fin 4, N.stages.rawAt k i = N.stages.rawAt C.missing.castSucc i := by
      apply sum_eq_single_of_mem _ (mem_univ _)
      intro k _ ne
      exact Nat.eq_zero_of_le_zero (none k ne)
    omega
  obtain ⟨t, tm, used⟩ := other
  by_cases last : t = 3
  · exact Or.inr (Or.inr (last ▸ used))
  have early : t.val < 3 := by
    have range := t.isLt
    have ne : t.val ≠ 3 := fun h => last (Fin.ext h)
    omega
  let k : Fin 3 := ⟨t.val, early⟩
  have kt : k.castSucc = t := Fin.ext rfl
  rcases C.early_cases k with kp | kq | km
  · exact Or.inl (by rw [← kp, kt]; exact used)
  · exact Or.inr (Or.inl (by rw [← kq, kt]; exact used))
  · exact (tm (kt.symm.trans (congrArg Fin.castSucc km))).elim

theorem hidden_missing_and_blocks {i j : Ten} (ia : i ≠ C.a) (ne : i ≠ j)
    (hidden : outputWeight N.forest (ones i) = 0) {t : Fin 4} (different : C.missing.castSucc ≠ t)
    (readT : 0 < N.stages.rawAt t i) (onM : signal N.forest C.missing.val (singletonInput j) = true)
    (onT : signal N.forest t.val (singletonInput j) = true) : False :=
  N.hidden_blocks C.test ne (C.raw i).le hidden different
    (by rw [C.hidden_reads_missing ia hidden]; decide) readT onM onT

theorem last_read_rules_out_last {i j : Ten} (ia : i ≠ C.a) (ne : i ≠ j)
    (hidden : outputWeight N.forest (ones i) = 0) (lastRead : 0 < N.stages.rawAt 3 i)
    (onM : signal N.forest C.missing.val (singletonInput j) = true) :
    N.last (singletonInput j) = false :=
  Bool.eq_false_of_not_eq_true fun last =>
    C.hidden_missing_and_blocks ia ne hidden C.missing_ne_last lastRead onM last

theorem hidden_last_pair_profile {i j : Ten} (ia : i ≠ C.a) (ja : j ≠ C.a) (ne : i ≠ j)
    (hi : outputWeight N.forest (ones i) = 0) (hj : outputWeight N.forest (ones j) = 0)
    (ri : 0 < N.stages.rawAt 3 i) (rj : 0 < N.stages.rawAt 3 j) :
    profile N.forest (singletonInput i) = profile N.forest (singletonInput j) := by
  have onI := C.hidden_activates_missing ia hi
  have onJ := C.hidden_activates_missing ja hj
  have reads (k : Ten) (ka : k ≠ C.a) (h : outputWeight N.forest (ones k) = 0)
      (last : 0 < N.stages.rawAt 3 k) :=
    (N.stages.rawAtTwo C.missing_ne_last (N.stageBudget k (C.raw k).le)
      (show 0 < N.stages.rawAt C.missing.castSucc k by rw [C.hidden_reads_missing ka h]; decide) last).2
  have early := (N.early_eq_for_two ne C.missing.castSucc
    ((N.signal_prior _ C.missing_ne_last _).symm.trans onI)
    ((N.signal_prior _ C.missing_ne_last _).symm.trans onJ) (reads i ia hi ri) (reads j ja hj rj)).1
  have offI := C.last_read_rules_out_last ja ne.symm hj rj onI
  have offJ := C.last_read_rules_out_last ia ne hi ri onJ
  rw [N.profile_eq, N.profile_eq, early, offI, offJ]

end CrownFourthStructure.Case
