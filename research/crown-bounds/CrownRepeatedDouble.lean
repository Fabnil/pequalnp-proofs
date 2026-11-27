import CrownProfileConstraints

namespace CrownProfileThree.Network

open CrownForks CrownProfiles CrownPairFormula PnpResearch Finset

variable {I : Type} [DecidableEq I]

private abbrev Bits := Bool × Bool × Bool

private theorem weightOfRetained (N : Network I) (i : I) :
    ∑ k : Fin 4, (if flag (N.bits (singletonInput i)) k then 0 else N.rawAt k i) =
      keptWeight N.forest (profile N.forest (singletonInput i)) (ones i) := by
  obtain ⟨p, q, r, h⟩ := N.raw_eq i
  rw [Fin.sum_univ_four, p, q, r, h, profile_eq]
  simp [flag, forest, keptWeight, firstRaw, secondRaw, thirdRaw, outputRaw, Nat.add_assoc]

private theorem laterActiveRawZero (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j : I} (ne : i ≠ j) (same : N.bits (singletonInput i) = N.bits (singletonInput j))
    (raw : N.forest.weight (ones i) ≤ 2) (warm : firstStage (N.bits (singletonInput i)) ≠ 3)
    (t : Fin 4) (later : t ≠ firstStage (N.bits (singletonInput i)))
    (active : flag (N.bits (singletonInput i)) t = true) : N.rawAt t i = 0 := by
  let b := N.bits (singletonInput i)
  let s := firstStage b
  let acquired (k : Fin 4) := if flag b k then N.rawAt k i else 0
  let kept (k : Fin 4) := if flag b k then 0 else N.rawAt k i
  have retained : 1 ≤ ∑ k, kept k := by
    rw [show (∑ k, kept k) = _ from N.weightOfRetained i]
    apply keptReadOfPair N.forest test ne
    rw [profile_eq, profile_eq, same]
  have total : (∑ k, acquired k) + (∑ k, kept k) = N.forest.weight (ones i) := by
    rw [← sum_add_distrib, ← rawTotal]
    refine sum_congr rfl (fun k _ => ?_)
    simp only [acquired, kept]
    cases flag b k <;> simp
  have sumBound : ∑ k, acquired k ≤ 1 := by omega
  have both : ∑ k ∈ ({t, s} : Finset (Fin 4)), acquired k ≤ 1 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)).trans sumBound
  have different : t ≠ s := later
  rw [sum_insert (by simp [different]), sum_singleton] at both
  have first : 1 ≤ N.rawAt s i := N.firstRawNeeded warm
  have tActive : flag b t = true := active
  have sActive : flag b s = true := stageActive b warm
  change (if flag b t then N.rawAt t i else 0) +
    (if flag b s then N.rawAt s i else 0) ≤ 1 at both
  rw [ite_eq_left tActive, ite_eq_left sActive] at both
  omega

private theorem doublePrefix : ∀ (b : Bits) (t : Fin 4),
    load b = 2 → t ≠ firstStage b → flag b t = true →
    firstStage b ≠ 3 ∧ t ≠ 3 ∧ ∀ k < t, flag b k = true → k = firstStage b :=
  by decide +kernel

theorem repeatedDoubleImplication (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j : I} (ne : i ≠ j) (same : N.bits (singletonInput i) = N.bits (singletonInput j))
    (raw : N.forest.weight (ones i) ≤ 2) (double : load (N.bits (singletonInput i)) = 2)
    {t : Fin 4} (later : t ≠ firstStage (N.bits (singletonInput i)))
    (active : flag (N.bits (singletonInput i)) t = true) (a : I)
    (trigger : flag (N.bits (singletonInput a)) (firstStage (N.bits (singletonInput i))) = true) :
    flag (N.bits (singletonInput a)) t = true := by
  let b := N.bits (singletonInput i)
  let c := N.bits (singletonInput a)
  obtain ⟨warm, signal, prior⟩ := doublePrefix b t double later active
  have absent := N.laterActiveRawZero test ne same raw warm t later active
  have before (k : Fin 4) (hk : k < t) : flag b k ≤ flag c k :=
    Bool.le_iff_imp.mpr fun on => (prior k hk on).symm ▸ trigger
  apply Bool.le_iff_imp.mp _ active
  calc
    flag b t = N.atProfile t b (singletonInput i) := (N.atActual _ _ signal).symm
    _ = N.atProfile t b (fun _ => false) := N.zeroIgnored t _ absent
    _ ≤ N.atProfile t c (singletonInput a) := N.atMono t before (fun _ => Bool.false_le _)
    _ = flag c t := N.atActual _ _ signal

end CrownProfileThree.Network
