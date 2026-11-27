import CrownThresholdFrontier

namespace CrownThirteenFrontier

open CrownForks CrownForest CrownForestCost CrownFourProfiles CrownFirstAnd CrownOrStages
open CrownDropZero CrownRestriction CrownThresholdFrontier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

structure AtMargin (E : SharedFormula (Fin 13)) : Prop where
  frontier : CrownThresholdFrontier.AtMargin 6 E
  doubleDeletion : ∀ (p : Fin 13) (q : Fin 12), KeepsLeaves (removeTwo p q) E

theorem crownBudget44 (floorEleven : CrownLower.LowerBound 11 27)
    (small : RepSizeAtMost (fun u v : Fin 13 => decide (u ≠ v)) 44) :
    ∃ E : SharedFormula (Fin 13), AtMargin E := by
  have floorTwelve : CrownLower.LowerBound 12 29 :=
    CrownProduct.thresholdLowerStep (by decide : 2 ≤ 11) (by decide) floorEleven
  obtain ⟨E, data⟩ := crownAtMargin (extra := 6) (by decide) (by decide) (by decide) (by decide)
    floorTwelve small
  have cost : gates E = 31 := by
    have used := CrownEleven.gates_of_two_reads E data.valid data.reads
    have extra := data.extra
    omega
  refine ⟨E, data, fun p q => ?_⟩
  obtain ⟨_, _, _, _, live⟩ := tightDoubleDeletion (by decide : 2 ≤ 11)
    floorEleven E data.valid data.tests data.reads cost.le p q
  exact live

/-- The OR stages before the first shared AND survive every two-input
    deletion. Each must therefore have at least three singleton activators. -/
theorem threeSingletons {E : SharedFormula (Fin 13)} (data : AtMargin E) {n k : ℕ}
    (pure : orPrefix E n) (early : k < n) (inside : k < numShared E) :
    ∃ i j t : Fin 13, i ≠ j ∧ i ≠ t ∧ j ≠ t ∧ signal E k (singletonInput i) = true ∧
      signal E k (singletonInput j) = true ∧ signal E k (singletonInput t) = true := by
  have avoids (p : Fin 13) (q : Fin 12) :
      ∃ i, i ≠ p ∧ i ≠ p.succAbove q ∧ signal E k (singletonInput i) = true := by
    have active := live_after_restriction E (removeTwo p q) (data.doubleDeletion p q) k inside
    have supports : singletonDisjunction (signal E k) :=
      orStage E n pure (fun x a => x a) projection k early
    obtain ⟨i, present, on⟩ :=
      (supports (assignment (removeTwo p q) (fun _ => true))).mp active
    refine ⟨i, ?_, ?_, on⟩
    · intro eq
      subst i
      simp [assignment, removeTwo, remove_at] at present
    · intro eq
      subst i
      simp [assignment, removeTwo, remove_on, remove_at] at present
  obtain ⟨i, _, _, onI⟩ := avoids 0 0
  obtain ⟨j, ji, _, onJ⟩ := avoids i 0
  obtain ⟨q, eq⟩ := Fin.exists_succAbove_eq (x := j) (y := i) ji
  obtain ⟨t, ti, tj, onT⟩ := avoids i q
  exact ⟨i, j, t, ji.symm, ti.symm, by simpa only [eq] using tj.symm, onI, onJ, onT⟩

end CrownThirteenFrontier
