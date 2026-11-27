import CrownOrReaders

namespace CrownFourNetwork

open CrownForks CrownForest CrownProfiles CrownVisibility CrownPairFormula
open CrownForestCost CrownFourProfiles CrownFirstAnd PnpResearch Finset
open CrownProfileThree.Network (ones flag)

structure Network (I : Type) where
  stages : CrownProfileThree.Network I
  out : Formula (Option (Option (Option (Option I))))

namespace Network

variable {I : Type}

def forest (N : Network I) : SharedFormula I :=
  .share N.stages.first 1 (.share N.stages.second 1 (.share N.stages.third 1
    (.share N.stages.output 1 (.tree N.out))))

def last (N : Network I) (x : I → Bool) : Bool :=
  signal N.forest 3 x

theorem numShared_eq (N : Network I) : numShared N.forest = 4 := rfl

theorem twoReads_valid (N : Network I) : twoReads N.forest :=
  ⟨rfl, rfl, rfl, rfl, trivial⟩

theorem profile_eq (N : Network I) (x : I → Bool) :
    profile N.forest x =
      [(N.stages.bits x).1, (N.stages.bits x).2.1, (N.stages.bits x).2.2, N.last x] := rfl

theorem signal_prior (N : Network I) (k : Fin 4) (early : k ≠ 3) (x : I → Bool) :
    signal N.forest k.val x = flag (N.stages.bits x) k := by
  fin_cases k <;> first | rfl | contradiction

theorem last_eval (N : Network I) (x : I → Bool) :
    N.last x = N.stages.atProfile 3 (N.stages.bits x) x := rfl

theorem last_mono (N : Network I) {x y : I → Bool} (le : ∀ i, x i ≤ y i) : N.last x ≤ N.last y :=
  evalMono N.stages.output (N.stages.signals_mono le)

theorem prior_full_mono (N : Network I) {x y : I → Bool} (le : ∀ i, x i ≤ y i)
    (full : N.stages.bits x = (true, true, true)) : N.stages.bits y = (true, true, true) := by
  have on (k : Fin 4) (ne : k ≠ 3) : flag (N.stages.bits y) k = true := by
    apply Bool.le_iff_imp.mp (N.stages.profileMono le k)
    rw [full]
    fin_cases k <;> first | rfl | contradiction
  exact Prod.ext (on 0 (by decide)) (Prod.ext (on 1 (by decide)) (on 2 (by decide)))

theorem firstHot_le (N : Network I) (x : I → Bool) : firstHot N.forest x ≤ 4 := by
  have bound := List.findIdx_le_length (p := id) (xs := profile N.forest x)
  simpa only [firstHot, profile_length, N.numShared_eq] using bound

theorem hot_of_firstHot_lt (N : Network I) (x : I → Bool) (before : firstHot N.forest x < 4) :
    true ∈ profile N.forest x := by
  have before' : firstHot N.forest x < (profile N.forest x).length := by
    simpa only [profile_length, N.numShared_eq] using before
  rcases List.findIdx_lt_length.mp before' with ⟨b, member, yes⟩
  exact (show b = true from yes) ▸ member

theorem firstHot_flags (N : Network I) (x : I → Bool) {k : ℕ} (inside : k < 4)
    (first : firstHot N.forest x = k) :
    signal N.forest k x = true ∧ ∀ t < k, signal N.forest t x = false := by
  have atK : k < (profile N.forest x).length := by
    simpa only [profile_length, N.numShared_eq] using inside
  have rule := (List.findIdx_eq (p := id) atK).mp first
  refine ⟨?_, fun t lt => ?_⟩
  · simpa only [signal, bitAt, List.getElem?_eq_getElem atK, Option.getD_some, id_eq] using rule.1
  · have atT := lt.trans atK
    simpa only [signal, bitAt, List.getElem?_eq_getElem atT, Option.getD_some, id_eq] using rule.2 t lt

variable [DecidableEq I]

theorem rawAt_eq (N : Network I) (k : Fin 4) (i : I) :
    N.stages.rawAt k i = stageWeight N.forest (ones i) k.val := by
  obtain ⟨p, q, r, s⟩ := N.stages.raw_eq i
  fin_cases k <;> first | exact p | exact q | exact r | exact s

theorem rawTotal (N : Network I) (i : I) :
    (∑ k : Fin 4, N.stages.rawAt k i) + outputWeight N.forest (ones i) =
      N.forest.weight (ones i) := by
  rw [N.stages.rawTotal, N.stages.weight_eq]
  simp only [forest, SharedFormula.weight, outputWeight, CrownProfileThree.Network.firstRaw,
    CrownProfileThree.Network.secondRaw, CrownProfileThree.Network.thirdRaw,
    CrownProfileThree.Network.outputRaw]
  omega

theorem stageBudget (N : Network I) (i : I) (raw : N.forest.weight (ones i) ≤ 2) :
    N.stages.forest.weight (ones i) ≤ 2 := by
  have total := N.rawTotal i
  rw [N.stages.rawTotal] at total
  omega

theorem output_eq_of_same_profile (N : Network I) {i j : I} (ne : i ≠ j)
    (absent : outputWeight N.forest (ones i) = 0)
    (same : profile N.forest (pairInput i j) = profile N.forest (singletonInput j)) :
    N.forest.eval (pairInput i j) = N.forest.eval (singletonInput j) := by
  let b := profile N.forest (singletonInput j)
  let x := CrownVisibility.supply b (singletonInput j)
  let y := CrownVisibility.supply b (pairInput i j)
  have mono (k : I ⊕ ℕ) : x k ≤ y k := by
    cases k with
    | inl a => exact TwoShared.otherSingleton_pair i j a
    | inr k => exact le_rfl
  have mass : (fun k => rise (x k) (y k)) = ones (Sum.inl i) := by
    funext k
    cases k with
    | inl k =>
      simpa [x, y, CrownVisibility.supply, ones, singletonInput] using
        congrFun (TwoShared.addedInputRise i j ne) k
    | inr k => simp [x, y, CrownVisibility.supply, rise, ones, singletonInput]
  have equal : (CrownVisibility.output N.forest).evalWith x =
      (CrownVisibility.output N.forest).evalWith y := by
    apply eqOfNoRise _ mono
    rw [mass]
    change reads (CrownVisibility.output N.forest) (Sum.inl i) = 0
    rwa [output_read]
  rw [← output_eval N.forest (pairInput i j), same, ← output_eval N.forest (singletonInput j)]
  exact equal.symm

theorem pair_changes_last (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j : I} (ne : i ≠ j) (absent : outputWeight N.forest (ones i) = 0)
    (early : N.stages.bits (pairInput i j) = N.stages.bits (singletonInput j)) :
    N.last (pairInput i j) ≠ N.last (singletonInput j) := by
  intro sameLast
  have same : profile N.forest (pairInput i j) = profile N.forest (singletonInput j) := by
    rw [N.profile_eq, N.profile_eq, early, sameLast]
  have eq := N.output_eq_of_same_profile ne absent same
  rw [test.2 i j ne, test.1 j] at eq
  contradiction

/-- If two inputs start at the same earlier stage and can affect the first
    three stages only there, their first three bits agree on both singletons
    and on their pair. -/
theorem early_eq_for_two (N : Network I) {i j : I} (ne : i ≠ j) (t : Fin 4)
    (onI : flag (N.stages.bits (singletonInput i)) t = true)
    (onJ : flag (N.stages.bits (singletonInput j)) t = true)
    (readI : ∀ k, k ≠ t → k ≠ 3 → N.stages.rawAt k i = 0)
    (readJ : ∀ k, k ≠ t → k ≠ 3 → N.stages.rawAt k j = 0) :
    N.stages.bits (singletonInput i) = N.stages.bits (singletonInput j) ∧
      N.stages.bits (pairInput i j) = N.stages.bits (singletonInput j) := by
  let M := N.stages
  let a := M.bits (singletonInput i)
  let b := M.bits (singletonInput j)
  let c := M.bits (pairInput i j)
  have same (k : Fin 4) : flag a k = flag b k ∧ flag c k = flag b k := by
    refine (measure (fun k : Fin 4 => k.val)).wf.induction
      (C := fun k => flag a k = flag b k ∧ flag c k = flag b k) k ?_
    intro k ih
    by_cases last : k = 3
    · subst k
      exact ⟨rfl, rfl⟩
    by_cases first : k = t
    · subst k
      have pairOn : flag c t = true :=
        (Bool.le_iff_imp.mp (M.profileMono (TwoShared.otherSingleton_pair i j) t)) onJ
      exact ⟨onI.trans onJ.symm, pairOn.trans onJ.symm⟩
    have iAt : flag a k = M.atProfile k b (singletonInput i) :=
      (M.atActual _ k last).symm.trans (M.atSamePrefix k _ (fun q lt => (ih q lt).1))
    have jAt : flag b k = M.atProfile k b (singletonInput j) := (M.atActual _ k last).symm
    have pairAt : flag c k = M.atProfile k b (pairInput i j) :=
      (M.atActual _ k last).symm.trans (M.atSamePrefix k _ (fun q lt => (ih q lt).2))
    have ignoreI := M.zeroIgnored k b (readI k first last)
    have ignoreJ := M.zeroIgnored k b (readJ k first last)
    exact ⟨iAt.trans (ignoreI.trans (ignoreJ.symm.trans jAt.symm)),
      pairAt.trans ((M.addIgnored k b ne (readI k first last)).trans jAt.symm)⟩
  exact ⟨Prod.ext (same 0).1 (Prod.ext (same 1).1 (same 2).1),
    Prod.ext (same 0).2 (Prod.ext (same 1).2 (same 2).2)⟩

private theorem orOnly_rename {A B : Type} (f : Formula A) (map : A → B)
    (shape : CrownOrStages.orOnly f) : CrownOrStages.orOnly (rename f map) := by
  induction f with
  | var a => trivial
  | conj l r il ir => exact shape.elim
  | disj l r il ir => exact ⟨il shape.1, ir shape.2⟩

omit [DecidableEq I] in
theorem formulaAt_pure (N : Network I) (t : Fin 4)
    (early : CrownOrStages.orPrefix N.forest (t.val + 1)) :
    CrownOrStages.orOnly (N.stages.formulaAt t) := by
  fin_cases t
  · exact orOnly_rename _ _ early.1
  · exact orOnly_rename _ _ early.2.1
  · exact orOnly_rename _ _ early.2.2.1
  · exact early.2.2.2.1

omit [DecidableEq I] in
theorem stage_eval (N : Network I) (t : Fin 4) (x : I → Bool) :
    N.stages.atProfile t (N.stages.bits x) x = signal N.forest t.val x := by
  by_cases last : t = 3
  · subst t
    rfl
  · rw [N.signal_prior t last, N.stages.atActual x t last]

theorem direct_or_on (N : Network I) (t : Fin 4) (i : I)
    (early : CrownOrStages.orPrefix N.forest (t.val + 1))
    (read : 0 < N.stages.rawAt t i) :
    signal N.forest t.val (singletonInput i) = true := by
  rw [← N.stage_eval]
  exact (CrownOrReaders.orOnly_on_iff _ (N.formulaAt_pure t early) _).mpr
    ⟨CrownProfileThree.Network.rawKey i, read, by simp [CrownProfileThree.Network.supply, singletonInput]⟩

theorem hidden_blocks (N : Network I) (test : ThresholdOn N.forest.eval) {i j : I} (ne : i ≠ j)
    (budget : N.forest.weight (ones i) ≤ 2) (hidden : outputWeight N.forest (ones i) = 0)
    {s t : Fin 4} (st : s ≠ t) (readS : 0 < N.stages.rawAt s i) (readT : 0 < N.stages.rawAt t i)
    (onS : signal N.forest s.val (singletonInput j) = true)
    (onT : signal N.forest t.val (singletonInput j) = true) : False := by
  have others := (N.stages.rawAtTwo st (N.stageBudget i budget) readS readT).2
  have eq := (pairStable N.forest i j (by
    intro k pos
    change signal N.forest k (singletonInput j) = true
    by_cases first : k = s.val
    · simpa only [first] using onS
    by_cases second : k = t.val
    · simpa only [second] using onT
    have inRange := stageWeight_pos N.forest (ones i) k pos
    rw [N.numShared_eq] at inRange
    let u : Fin 4 := ⟨k, inRange⟩
    have zero := others u (fun h => first (congrArg Fin.val h)) (fun h => second (congrArg Fin.val h))
    rw [N.rawAt_eq] at zero
    change stageWeight N.forest (ones i) k = 0 at zero
    omega)).2 hidden
  rw [test.2 i j ne, test.1 j] at eq
  contradiction

end Network

end CrownFourNetwork
