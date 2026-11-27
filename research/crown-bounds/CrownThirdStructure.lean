import CrownFourNetwork
import CrownHiddenReads

namespace CrownThirdStructure

open CrownForks CrownForest CrownProfiles CrownVisibility CrownFirstAnd CrownFourProfiles
open CrownFourNetwork CrownFourNormal CrownForestCost CrownDropZero CrownOrReaders
open CrownPairFormula PnpResearch
open CrownProfileThree.Network (flag ones rawKey)

structure Case (N : Network Ten) where
  valid : N.forest.Valid
  test : ThresholdOn N.forest.eval
  raw : ∀ i, N.forest.weight (ones i) = 2
  early : CrownOrStages.orPrefix N.forest 2
  a : Ten
  anchorBefore : N.stages.bits (singletonInput a) = (true, true, true)
  anchorLast : N.last (singletonInput a) = false
  noBoth : ∀ i, i ≠ a →
    ¬ (signal N.forest 0 (singletonInput i) = true ∧ signal N.forest 1 (singletonInput i) = true)

theorem ofOverlap (hyp : HasOverlapAt 2) : ∃ N : Network Ten, Nonempty (Case N) := by
  obtain ⟨p, q, r, s, h, early, valid, test, raw, a, overlap, onR⟩ := hyp
  let N : Network Ten := ⟨⟨p, q, r, s⟩, h⟩
  change earlierOverlap N.forest 2 a at overlap
  obtain ⟨j, k, hj, hk, ne, onJ, onK, notJK, notKJ⟩ := overlap
  have pair : (j = 0 ∧ k = 1) ∨ (j = 1 ∧ k = 0) := by omega
  have facts := readersOfOverlap N.forest valid test (fun i => (raw i).le) N.numShared_eq
    (by decide) early hj hk ne a onJ onK onR notJK notKJ
  have offS := facts.2.2.2.1 3 (by decide) (by omega) (by omega) (by decide)
  have pOn : signal N.forest 0 (singletonInput a) = true := by
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  have qOn : signal N.forest 1 (singletonInput a) = true := by
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> assumption
  refine ⟨N, ⟨⟨valid, test, raw, early, a, Prod.ext pOn (Prod.ext qOn onR), offS, ?_⟩⟩⟩
  intro i ia on
  apply facts.2.2.2.2 i ia
  rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact on
  · exact ⟨on.2, on.1⟩

namespace Case

variable {N : Network Ten} (C : Case N)

def first (N : Network Ten) (i : Ten) : ℕ := firstHot N.forest (singletonInput i)

def visible (N : Network Ten) (i : Ten) : Prop := 0 < outputWeight N.forest (ones i)

theorem anchorProfile : profile N.forest (singletonInput C.a) = [true, true, true, false] := by
  rw [N.profile_eq, C.anchorBefore, C.anchorLast]

theorem anchorOn (k : ℕ) (early : k < 3) : signal N.forest k (singletonInput C.a) = true := by
  unfold signal
  rw [C.anchorProfile]
  interval_cases k <;> rfl

theorem visible_unique_early {i j : Ten} (ne : i ≠ j) (ia : i ≠ C.a) (ja : j ≠ C.a)
    {t : ℕ} (early : t < 3) (firstI : first N i = t) (firstJ : first N j = t)
    (seeI : visible N i) (seeJ : visible N j) : False := by
  have hotI := N.hot_of_firstHot_lt (singletonInput i) (by change first N i < 4; omega)
  have hotJ := N.hot_of_firstHot_lt (singletonInput j) (by change first N j < 4; omega)
  exact twoVisible N.forest C.test ne ia ja hotI hotJ seeI seeJ
    (C.raw i).le (C.raw j).le (firstI.trans firstJ.symm) (by
      change signal N.forest (first N i) (singletonInput C.a) = true
      rw [firstI]
      exact C.anchorOn t early)

theorem hidden_reads_last {i : Ten} (ia : i ≠ C.a) (hidden : outputWeight N.forest (ones i) = 0) :
    1 ≤ N.stages.rawAt 3 i := by
  by_contra! no
  have zero : stageWeight N.forest (ones i) 3 = 0 := by
    have eq := N.rawAt_eq 3 i
    change N.stages.rawAt 3 i = stageWeight N.forest (ones i) 3 at eq
    omega
  have equal := (pairStable N.forest i C.a (by
    intro k pos
    have range := stageWeight_pos N.forest (ones i) k pos
    rw [N.numShared_eq] at range
    have early : k < 3 := by
      by_contra! out
      have last : k = 3 := by omega
      rw [last, zero] at pos
      omega
    exact C.anchorOn k early)).2 hidden
  rw [C.test.2 i C.a ia, C.test.1 C.a] at equal
  contradiction

theorem hidden_early_reads {i : Ten} (ia : i ≠ C.a) (hidden : outputWeight N.forest (ones i) = 0)
    (t : Fin 4) (early : t ≠ 3) (firstI : first N i = t.val) :
    N.stages.rawAt t i = 1 ∧ N.stages.rawAt 3 i = 1 ∧
      ∀ k, k ≠ t → k ≠ 3 → N.stages.rawAt k i = 0 := by
  have hot := N.hot_of_firstHot_lt (singletonInput i) (by
    change first N i < 4
    rw [firstI]
    exact t.isLt)
  have firstRead := (firstHotFacts N.forest (singletonInput i) hot).2
  change 1 ≤ stageWeight N.forest (ones i) (first N i) at firstRead
  rw [firstI, ← N.rawAt_eq t i] at firstRead
  have lastRead := C.hidden_reads_last ia hidden
  have bound := N.stageBudget i (C.raw i).le
  obtain ⟨oneLast, others⟩ := N.stages.rawAtTwo early bound firstRead lastRead
  exact ⟨(N.stages.rawAtTwo early.symm bound lastRead firstRead).1, oneLast, others⟩

private theorem anchor_pair_last {i : Ten} (ia : i ≠ C.a) (hidden : outputWeight N.forest (ones i) = 0) :
    N.stages.bits (pairInput i C.a) = N.stages.bits (singletonInput C.a) ∧
      N.last (pairInput i C.a) = true := by
  have early := (N.prior_full_mono (TwoShared.otherSingleton_pair i C.a) C.anchorBefore).trans
    C.anchorBefore.symm
  have flip := N.pair_changes_last C.test ia hidden early
  rw [C.anchorLast] at flip
  exact ⟨early, Bool.eq_true_of_not_eq_false flip⟩

theorem hidden_unique_early {i j : Ten} (ne : i ≠ j) (ia : i ≠ C.a) (ja : j ≠ C.a)
    (t : Fin 4) (early : t ≠ 3) (firstI : first N i = t.val) (firstJ : first N j = t.val)
    (hiddenI : outputWeight N.forest (ones i) = 0) (hiddenJ : outputWeight N.forest (ones j) = 0) :
    False := by
  obtain ⟨_, lastI, readI⟩ := C.hidden_early_reads ia hiddenI t early firstI
  obtain ⟨_, lastJ, readJ⟩ := C.hidden_early_reads ja hiddenJ t early firstJ
  have onI := (N.firstHot_flags (singletonInput i) t.isLt firstI).1
  have onJ := (N.firstHot_flags (singletonInput j) t.isLt firstJ).1
  rw [N.signal_prior t early] at onI onJ
  obtain ⟨earlySingles, earlyPair⟩ := N.early_eq_for_two ne t onI onJ readI readJ
  have pairFlipJ := N.pair_changes_last C.test ne hiddenI earlyPair
  have offJ : N.last (singletonInput j) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro on
    have both := Bool.le_iff_imp.mp (N.last_mono (TwoShared.otherSingleton_pair i j)) on
    exact pairFlipJ (both.trans on.symm)
  have swap : pairInput j i = pairInput i j := by funext k; exact Bool.or_comm _ _
  have pairFlipI := N.pair_changes_last C.test ne.symm hiddenJ (by rw [swap, earlyPair, earlySingles])
  rw [swap] at pairFlipI
  have offI : N.last (singletonInput i) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro on
    have both := Bool.le_iff_imp.mp (N.last_mono (TwoShared.singleton_pair i j)) on
    exact pairFlipI (both.trans on.symm)
  have onPair : N.last (pairInput i j) = true :=
    Bool.eq_true_of_not_eq_false (fun off => pairFlipJ (off.trans offJ.symm))
  obtain ⟨earlyAI, hitI⟩ := C.anchor_pair_last ia hiddenI
  obtain ⟨earlyAJ, hitJ⟩ := C.anchor_pair_last ja hiddenJ
  let supply := @CrownProfileThree.Network.supply Ten
  let b := N.stages.bits (singletonInput j)
  let c := N.stages.bits (singletonInput C.a)
  have evaluated (x : Ten → Bool) :
      N.stages.output.evalWith (supply (N.stages.bits x) x) = N.last x := rfl
  obtain ⟨u10, u01, u11⟩ := CrownProfileThree.Network.setTwo_zero ne
  obtain ⟨v00, v10, v01⟩ := CrownProfileThree.Network.setTwo_one ia ja ne
  apply noAndToOr N.stages.output (i := rawKey i) (j := rawKey j) (by simpa using ne)
    (show N.stages.rawAt 3 i ≤ 1 from lastI.le) (show N.stages.rawAt 3 j ≤ 1 from lastJ.le)
    (supply b (fun _ => false)) (supply c (singletonInput C.a))
  · rw [CrownProfileThree.Network.supply_setTwo, u10]
    exact (congrArg (fun d => N.stages.output.evalWith (supply d (singletonInput i)))
      earlySingles.symm).trans ((evaluated _).trans offI)
  · rw [CrownProfileThree.Network.supply_setTwo, u01]
    exact (evaluated _).trans offJ
  · rw [CrownProfileThree.Network.supply_setTwo, u11]
    exact (congrArg (fun d => N.stages.output.evalWith (supply d (pairInput i j)))
      earlyPair.symm).trans ((evaluated _).trans onPair)
  · rw [CrownProfileThree.Network.supply_setTwo, v00]
    exact (evaluated _).trans C.anchorLast
  · rw [CrownProfileThree.Network.supply_setTwo, v10]
    exact (congrArg (fun d => N.stages.output.evalWith (supply d (pairInput i C.a)))
      earlyAI.symm).trans ((evaluated _).trans hitI)
  · rw [CrownProfileThree.Network.supply_setTwo, v01]
    exact (congrArg (fun d => N.stages.output.evalWith (supply d (pairInput j C.a)))
      earlyAJ.symm).trans ((evaluated _).trans hitJ)

include C in
theorem hidden_saturates {i j : Ten} (ne : i ≠ j)
    (hidden : outputWeight N.forest (ones i) = 0) (t : Fin 4) (early : t ≠ 3)
    (atT : 0 < N.stages.rawAt t i) (atLast : 0 < N.stages.rawAt 3 i)
    (onT : signal N.forest t.val (singletonInput j) = true)
    (onLast : N.last (singletonInput j) = true) : False := by
  exact N.hidden_blocks C.test ne (C.raw i).le hidden early atT atLast onT onLast

theorem last_group_profile (i : Ten) (firstI : first N i = 3) :
    profile N.forest (singletonInput i) = [false, false, false, true] := by
  have bits := N.firstHot_flags (singletonInput i) (by decide) firstI
  have off0 : (N.stages.bits (singletonInput i)).1 = false := bits.2 0 (by decide)
  have off1 : (N.stages.bits (singletonInput i)).2.1 = false := bits.2 1 (by decide)
  have off2 : (N.stages.bits (singletonInput i)).2.2 = false := bits.2 2 (by decide)
  rw [N.profile_eq, off0, off1, off2, show N.last (singletonInput i) = true from bits.1]

include C in
theorem last_cannot_mix {i j : Ten} (ne : i ≠ j) (firstI : first N i = 3) (firstJ : first N j = 3)
    (vis : visible N i) (hidden : outputWeight N.forest (ones j) = 0) : False := by
  have hot := N.hot_of_firstHot_lt (singletonInput i) (by
    change first N i < 4
    rw [firstI]
    decide)
  have lastOn := (N.firstHot_flags (singletonInput j) (by decide) firstJ).1
  have pair := addVisible N.forest (i := i) (j := j) hot vis (C.raw i).le (by
    change signal N.forest (first N i) (singletonInput j) = true
    rw [firstI]
    exact lastOn)
  have commute : pairInput j i = pairInput i j := by funext x; exact Bool.or_comm _ _
  have same : profile N.forest (pairInput j i) = profile N.forest (singletonInput i) :=
    (congrArg (profile N.forest) commute).trans
      (pair.trans ((last_group_profile j firstJ).trans (last_group_profile i firstI).symm))
  have equal := N.output_eq_of_same_profile ne.symm hidden same
  rw [C.test.2 j i ne.symm, C.test.1 i] at equal
  contradiction

theorem hidden_last_group_reads {i : Ten} (ia : i ≠ C.a) (firstI : first N i = 3)
    (hidden : outputWeight N.forest (ones i) = 0) :
    N.stages.rawAt 2 i = 1 ∧ N.stages.rawAt 3 i = 1 := by
  have firsts := N.firstHot_flags (singletonInput i) (by decide) firstI
  have off (t : Fin 4) (early : t.val < 2) : N.stages.rawAt t i = 0 := by
    by_contra! notZero
    have on := N.direct_or_on t i (orPrefix_mono N.forest (by omega) C.early) (by omega)
    have absent := firsts.2 t.val (by omega)
    rw [on] at absent
    contradiction
  have lastNeed := C.hidden_reads_last ia hidden
  have size := (fourWithTwoReadsCosts23 N.forest C.valid C.raw rfl).le
  have lastAtMost := CrownHiddenReads.hiddenStageAtMostOne N.forest C.valid C.test size i 3 (C.raw i).le hidden
  have lastEq := N.rawAt_eq 3 i
  change N.stages.rawAt 3 i = stageWeight N.forest (ones i) 3 at lastEq
  have total := N.rawTotal i
  rw [Fin.sum_univ_four, hidden, C.raw, off 0 (by decide), off 1 (by decide)] at total
  omega

end Case

end CrownThirdStructure
