import CrownGridBounds
import CrownRestriction
import CrownTenExact

namespace CrownEleven

open CrownRun CrownForks CrownForest CrownForestCost CrownDropZero CrownRestriction PnpResearch
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Finset

theorem thresholdElevenLower : CrownLower.LowerBound 11 26 :=
  CrownProduct.thresholdLowerStep (by decide : 2 ≤ 10) (by decide) CrownTenExact.thresholdLowerTen

theorem gates_of_two_reads {n : ℕ} (E : SharedFormula (Fin n)) (valid : E.Valid)
    (reads : ∀ i, E.weight (CrownProfileThree.Network.ones i) = 2) :
    gates E + 1 = 2 * n + E.extraUses := by
  have all : (fun _ : Fin n => (1 : ℕ)) =
      fun a => ∑ i : Fin n, CrownProfileThree.Network.ones i a := by
    funext a
    rw [sum_eq_single_of_mem a (mem_univ _)]
    · simp [CrownProfileThree.Network.ones, singletonInput]
    · intro i _ ne
      simp [CrownProfileThree.Network.ones, singletonInput, ne.symm]
  have count := weightGates E valid
  rw [all, weightSum] at count
  simpa [reads, Nat.mul_comm] using count.symm

/-- A 26-gate threshold network on eleven inputs has exactly five extra uses.
    Every shared signal is active on some singleton. Each deletion of an
    input to zero keeps all leaves other than the two occurrences of that input.
    An input leaf cannot feed an AND gate directly. -/
theorem thresholdElevenAtMargin {s : ℕ} {F : BF 11} (test : ThresholdOn F)
    (compute : CrownLower.Computes 11 s F) (small : s ≤ 26) :
    ∃ E : SharedFormula (Fin 11), E.Valid ∧ ThresholdOn E.eval ∧
      (∀ i, E.weight (CrownProfileThree.Network.ones i) = 2) ∧ E.extraUses = 5 ∧
      allActive E (Samples.raw (Fin 11)) ∧
      ∀ p, KeepsLeaves (removeInput p) E ∧ ¬ forestAndReads p E := by
  obtain ⟨E, valid, works, reads, budget⟩ :=
    CrownMargin.forestAtMargin (by decide : 2 ≤ 10) CrownTenExact.thresholdLowerTen small test compute
  have number := gates_of_two_reads E valid reads
  have cost : gates E ≤ 26 := by omega
  have minimum : 26 ≤ gates E :=
    thresholdElevenLower works (evaluateForest E var (fun i => ⟨i, rfl⟩))
  have extra : E.extraUses = 5 := by omega
  have active : allActive E (Samples.raw (Fin 11)) := by
    rcases activeOrCheaper E (Samples.raw (Fin 11)) valid works.1 works.2 with live | ⟨G, less, passes⟩
    · exact live
    · have lower : 26 ≤ gates G :=
        thresholdElevenLower passes (evaluateForest G var (fun i => ⟨i, rfl⟩))
      omega
  refine ⟨E, valid, works, reads, extra, active, fun p => ?_⟩
  obtain ⟨_, _, _, _, keeps⟩ :=
    tightInputDeletion (by decide : 2 ≤ 10) CrownTenExact.thresholdLowerTen E valid works reads cost p
  exact ⟨keeps, noAndReadsAtMargin thresholdElevenLower E works cost p keeps⟩

theorem crownElevenBounds : RepSizeAtMost (fun u v : Fin 11 => decide (u ≠ v)) 38 ∧
    ∀ s, RepSizeAtMost (fun u v : Fin 11 => decide (u ≠ v)) s → 37 ≤ s :=
  ⟨CrownGridBounds.crownElevenUpper, fun _ rep => CrownTenExact.crownLowerFromTen (by decide) rep⟩

end CrownEleven
