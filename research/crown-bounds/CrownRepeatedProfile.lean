import CrownProfileConstraints

namespace CrownProfileThree.Network

open CrownForks CrownProfiles CrownPairFormula PnpResearch Finset

variable {I : Type} [DecidableEq I]

private abbrev Bits := Bool × Bool × Bool

private theorem pairComm (i j : I) : pairInput i j = pairInput j i := by
  funext k
  exact Bool.or_comm _ _

private theorem invisibleNeedsChange (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j : I} (ne : i ≠ j) (absent : N.rawAt 3 i = 0) :
    N.bits (pairInput i j) ≠ N.bits (singletonInput j) := by
  intro same
  have on := test.2 i j ne
  rw [← N.atOutput (pairInput i j), same, N.addIgnored 3 _ ne absent, N.atOutput, test.1] at on
  contradiction

private theorem repeatVisible (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j : I} (ne : i ≠ j) (same : N.bits (singletonInput i) = N.bits (singletonInput j))
    (warm : firstStage (N.bits (singletonInput i)) ≠ 3)
    (reads : N.forest.weight (ones i) ≤ 2) (visible : 1 ≤ N.outputRaw i) :
    1 ≤ N.outputRaw j := by
  by_contra! no
  have absent : N.rawAt 3 j = 0 := by rw [(N.raw_eq j).2.2.2]; omega
  obtain ⟨_, p, q, r⟩ := N.onlyFirstStageAndOutput i warm visible reads
  have active : flag (N.bits (singletonInput j)) (firstStage (N.bits (singletonInput i))) = true :=
    by rw [← same]; exact stageActive _ warm
  have pair := N.stableWhenAlreadyActive ne _ active p q r
  rw [pairComm i j, ← same] at pair
  exact N.invisibleNeedsChange test ne.symm absent pair

private def difference (a b : Bits) : Bits :=
  (b.1 && !a.1, b.2.1 && !a.2.1, b.2.2 && !a.2.2)

private theorem changed : ∀ a b : Bits, (∀ k, flag a k ≤ flag b k) → b ≠ a →
    let t := firstStage (difference a b)
    t ≠ 3 ∧ flag a t = false ∧ flag b t = true ∧ ∀ k < t, flag b k = flag a k :=
  by decide +kernel

private theorem equalBits : ∀ a b : Bits, (∀ k, flag a k = flag b k) → a = b :=
  by decide +kernel

private theorem singletonWarm : ∀ b : Bits, load b = 1 → firstStage b ≠ 3 :=
  by decide +kernel

private theorem doubleHasOther : ∀ (b : Bits) (t k : Fin 4),
    load b = 2 → t ≠ 3 → flag b t = false → k ≠ 3 → k ≠ t → flag b k = true :=
  by decide +kernel

private theorem stageBeforeOutput : ∀ t k : Fin 4, k < t → k ≠ 3 := by decide +kernel

private theorem firstChangeReads (N : Network I) {i j : I} (ne : i ≠ j)
    {t : Fin 4} (tSignal : t ≠ 3)
    (earlier : ∀ k < t, flag (N.bits (pairInput i j)) k = flag (N.bits (singletonInput j)) k)
    (atOne : flag (N.bits (singletonInput j)) t = false)
    (atTwo : flag (N.bits (pairInput i j)) t = true) : 1 ≤ N.rawAt t i := by
  by_contra! none
  have eq := N.atSamePrefix t (pairInput i j) earlier
  rw [N.atActual _ _ tSignal, atTwo, N.addIgnored t _ ne (by omega),
    N.atActual _ _ tSignal, atOne] at eq
  contradiction

private theorem addForMissing (N : Network I) (test : ThresholdOn N.forest.eval)
    {i a : I} (ne : i ≠ a) (absent : N.rawAt 3 i = 0) {t : Fin 4}
    (tSignal : t ≠ 3) (double : load (N.bits (singletonInput a)) = 2)
    (missing : flag (N.bits (singletonInput a)) t = false) :
    N.atProfile t (N.bits (singletonInput a)) (pairInput i a) = true := by
  let b := N.bits (singletonInput a)
  let c := N.bits (pairInput i a)
  have other (k : Fin 4) (signal : k ≠ 3) (kt : k ≠ t) : flag b k = true :=
    doubleHasOther _ _ _ double tSignal missing signal kt
  have mono (k : Fin 4) : flag b k ≤ flag c k :=
    N.profileMono (TwoShared.otherSingleton_pair i a) k
  have fixed (k : Fin 4) (signal : k ≠ 3) (kt : k ≠ t) : flag b k = flag c k :=
    (other k signal kt).trans ((Bool.le_iff_imp.mp (mono k)) (other k signal kt)).symm
  have on : flag c t = true := by
    by_contra h
    have off := Bool.eq_false_iff.mpr h
    apply N.invisibleNeedsChange test ne absent
    refine equalBits _ _ fun k => ?_
    by_cases kt : k = t
    · subst k
      exact off.trans missing.symm
    · by_cases out : k = 3
      · subst k
        rfl
      · exact (fixed k out kt).symm
  exact (N.atSamePrefix t (pairInput i a) (fun k lt =>
    fixed k (stageBeforeOutput _ _ lt) lt.ne)).trans ((N.atActual _ _ tSignal).trans on)

theorem repeatedSingletonNoDouble (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j a : I} (ne : i ≠ j)
    (same : N.bits (singletonInput i) = N.bits (singletonInput j))
    (ri : N.forest.weight (ones i) ≤ 2) (rj : N.forest.weight (ones j) ≤ 2)
    (single : load (N.bits (singletonInput i)) = 1)
    (double : load (N.bits (singletonInput a)) = 2)
    (contains : ∀ k, flag (N.bits (singletonInput i)) k ≤ flag (N.bits (singletonInput a)) k) :
    False := by
  let b := N.bits (singletonInput i)
  let c := N.bits (singletonInput a)
  let pair := N.bits (pairInput i j)
  let s := firstStage b
  have warm : s ≠ 3 := singletonWarm b single
  have active : flag b s = true := stageActive b warm
  have ia : i ≠ a := fun e => by rw [← e, single] at double; contradiction
  have ja : j ≠ a := fun e => by rw [← e, ← same, single] at double; contradiction
  by_cases iOut : 1 ≤ N.outputRaw i
  · exact N.twoAtOneStage test ne ia ja warm (congrArg firstStage same)
      ((Bool.le_iff_imp.mp (contains s)) active) iOut
      (N.repeatVisible test ne same warm ri iOut) ri rj
  have jWarm : firstStage (N.bits (singletonInput j)) ≠ 3 := by rwa [← same]
  have jOut : ¬1 ≤ N.outputRaw j := fun h => iOut (N.repeatVisible test ne.symm same.symm jWarm rj h)
  have iAbsent : N.rawAt 3 i = 0 := by rw [(N.raw_eq i).2.2.2]; omega
  have jAbsent : N.rawAt 3 j = 0 := by rw [(N.raw_eq j).2.2.2]; omega
  have diff : pair ≠ b := fun h => N.invisibleNeedsChange test ne iAbsent (h.trans same)
  let t := firstStage (difference b pair)
  obtain ⟨tSignal, tOff, tOn, earlier⟩ := changed b pair
    (N.profileMono (TwoShared.singleton_pair i j)) diff
  have iRead : 1 ≤ N.rawAt t i :=
    N.firstChangeReads ne tSignal (fun k lt => (earlier k lt).trans (congrArg (fun b => flag b k) same))
      ((congrArg (fun b => flag b t) same).symm.trans tOff) tOn
  have jRead : 1 ≤ N.rawAt t j := by
    apply N.firstChangeReads ne.symm tSignal
    · rw [pairComm j i]
      exact earlier
    · exact tOff
    · rw [pairComm j i]
      exact tOn
  have st : s ≠ t := fun e => by rw [e, tOff] at active; contradiction
  obtain ⟨iOnce, onlyI⟩ := N.rawAtTwo st ri (N.firstRawNeeded warm) iRead
  obtain ⟨jOnce, onlyJ⟩ := N.rawAtTwo st rj (by simpa only [← same] using N.firstRawNeeded jWarm) jRead
  by_cases tInC : flag c t = true
  · have dominated : ∀ k, flag pair k ≤ flag c k := by
      intro k
      refine (wellFounded_lt : WellFounded (fun a b : Fin 4 => a < b)).induction
        (C := fun z => flag pair z ≤ flag c z) k ?_
      intro k ih
      by_cases o : k = 3
      · subst k
        exact le_rfl
      by_cases h : k < t
      · exact (earlier k h).le.trans (contains k)
      by_cases e : k = t
      · exact Bool.le_iff_imp.mpr fun _ => e.symm ▸ tInC
      by_cases f : k = s
      · exact Bool.le_iff_imp.mpr fun _ => f.symm ▸ ((Bool.le_iff_imp.mp (contains s)) active)
      calc
        flag pair k = N.atProfile k pair (pairInput i j) := (N.atActual _ _ o).symm
        _ = N.atProfile k pair (singletonInput j) := N.addIgnored k _ ne (onlyI k f e)
        _ = N.atProfile k pair (fun _ => false) := N.zeroIgnored k _ (onlyJ k f e)
        _ ≤ N.atProfile k c (singletonInput a) := N.atMono k ih (fun _ => Bool.false_le _)
        _ = flag c k := N.atActual _ _ o
    have no := N.atMono 3 (b := pair) (c := c) (x := fun _ => false) (y := singletonInput a)
      (fun k _ => dominated k) (fun _ => Bool.false_le _)
    rw [N.atOutput, test.1, ← N.zeroIgnored 3 pair jAbsent, ← N.addIgnored 3 pair ne iAbsent,
      N.atOutput, test.2 i j ne] at no
    contradiction
  · have missing : flag c t = false := Bool.eq_false_iff.mpr tInC
    let u := supply b (fun _ : I => false)
    let v := supply c (singletonInput a)
    obtain ⟨u10, u01, u11⟩ := setTwo_zero ne
    obtain ⟨v00, v10, v01⟩ := setTwo_one ia ja ne
    apply noAndToOr (N.formulaAt t) (i := rawKey i) (j := rawKey j) (by simpa using ne)
      (by exact iOnce.le) (by exact jOnce.le) u v
    · rw [show u = supply b (fun _ : I => false) from rfl, supply_setTwo, u10]
      exact (N.atActual _ _ tSignal).trans tOff
    · rw [show u = supply b (fun _ : I => false) from rfl, supply_setTwo, u01, show b = _ from same]
      exact (N.atActual _ _ tSignal).trans ((congrArg (fun b => flag b t) same).symm.trans tOff)
    · rw [show u = supply b (fun _ : I => false) from rfl, supply_setTwo, u11]
      exact (N.atSamePrefix t (pairInput i j) (fun k h => (earlier k h).symm)).trans
        ((N.atActual _ _ tSignal).trans tOn)
    · rw [show v = supply c (singletonInput a) from rfl, supply_setTwo, v00]
      exact (N.atActual _ _ tSignal).trans missing
    · rw [show v = supply c (singletonInput a) from rfl, supply_setTwo, v10]
      exact N.addForMissing test ia iAbsent tSignal double missing
    · rw [show v = supply c (singletonInput a) from rfl, supply_setTwo, v01]
      exact N.addForMissing test ja jAbsent tSignal double missing

end CrownProfileThree.Network
