import CrownThresholdFrontier

namespace CrownElevenFrontier

open CrownRun CrownForks CrownForest CrownForestCost CrownFourProfiles CrownDropZero
open CrownRestriction CrownOrFrontier CrownEleven
open CrownProfileThree.Network (ones)
open CrownFirstAnd CrownOrStages PnpResearch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

structure AtMargin (E : SharedFormula (Fin 11)) : Prop where
  valid : E.Valid
  tests : ThresholdOn E.eval
  reads : ∀ i, E.weight (ones i) = 2
  extra : E.extraUses = 5
  atLeastFour : 4 ≤ numShared E
  atMostFive : numShared E ≤ 5
  allActive : CrownDropZero.allActive E (Samples.raw (Fin 11))
  prepared : Prepared (fun x => x) E
  notFull : ∀ i, ¬ full E (singletonInput i)
  tightDeletion : ∀ p, KeepsLeaves (removeInput p) E

private theorem withDeletion {E : SharedFormula (Fin 11)}
    (data : CrownThresholdFrontier.AtMargin 5 E) : AtMargin E := by
  have cost : gates E = 26 := by
    have used := gates_of_two_reads E data.valid data.reads
    have extra := data.extra
    omega
  refine ⟨data.valid, data.tests, data.reads, data.extra, data.atLeastFour, data.atMostExtra,
    data.allActive, data.prepared, data.notFull, fun p => ?_⟩
  obtain ⟨_, _, _, _, keeps⟩ :=
    tightInputDeletion (by decide : 2 ≤ 10) CrownTenExact.thresholdLowerTen
      E data.valid data.tests data.reads cost.le p
  exact keeps

theorem atMargin {s : ℕ} {F : BF 11} (test : ThresholdOn F)
    (compute : CrownLower.Computes 11 s F) (small : s ≤ 26) :
    ∃ E : SharedFormula (Fin 11), AtMargin E := by
  obtain ⟨E, data⟩ := CrownThresholdFrontier.thresholdAtMargin
    (extra := 5) (by decide) (by decide) (by decide) (by decide)
    CrownTenExact.thresholdLowerTen test compute small
  exact ⟨E, withDeletion data⟩

theorem crownBudget37 (small : RepSizeAtMost (fun u v : Fin 11 => decide (u ≠ v)) 37) :
    ∃ E : SharedFormula (Fin 11), AtMargin E := by
  obtain ⟨E, data⟩ := CrownThresholdFrontier.crownAtMargin
    (extra := 5) (by decide) (by decide) (by decide) (by decide)
    CrownTenExact.thresholdLowerTen small
  exact ⟨E, withDeletion data⟩

/-- A shared OR stage in the initial OR prefix remains satisfiable after
    deleting any one input to zero. Its OR support has at least two labels. -/
theorem twoSingletons {E : SharedFormula (Fin 11)} (data : AtMargin E) {n k : ℕ}
    (pure : orPrefix E n) (early : k < n) (inside : k < numShared E) :
    ∃ i j, i ≠ j ∧ signal E k (singletonInput i) = true ∧ signal E k (singletonInput j) = true := by
  have avoids (p : Fin 11) : ∃ i, i ≠ p ∧ signal E k (singletonInput i) = true := by
    have active := CrownThresholdFrontier.live_after_restriction E (removeInput p) (data.tightDeletion p) k inside
    have supports : singletonDisjunction (signal E k) :=
      orStage E n pure (fun x a => x a) projection k early
    obtain ⟨i, present, on⟩ :=
      (supports (assignment (removeInput p) (fun _ => true))).mp active
    refine ⟨i, ?_, on⟩
    intro same
    subst i
    simp [assignment, removeInput] at present
  obtain ⟨i, _, onI⟩ := avoids 0
  obtain ⟨j, other, onJ⟩ := avoids i
  exact ⟨i, j, other.symm, onI, onJ⟩

end CrownElevenFrontier
