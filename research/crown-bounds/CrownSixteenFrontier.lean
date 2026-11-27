import CrownThresholdFrontier
import CrownSubsetRestriction

namespace CrownSixteenFrontier

open CrownForks CrownForest CrownForestCost CrownFourProfiles CrownFirstAnd CrownOrStages
open CrownDropZero CrownRestriction CrownSubsetRestriction CrownThresholdFrontier Finset PnpResearch
open CrownSharedCuts (weightAdd)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private theorem retained_count (removed : Finset (Fin 16)) (count : removed.card = 3) :
    (univ \ removed).card = 13 := by
  rw [card_sdiff_of_subset (subset_univ _), count]
  decide

structure AtMargin (E : SharedFormula (Fin 16)) : Prop where
  frontier : CrownThresholdFrontier.AtMargin 7 E
  tripleDeletion : ∀ (s : Finset (Fin 16)) (count : s.card = 3),
    KeepsLeaves (keepSubset (univ \ s) (retained_count s count)) E

private theorem floorFifteen (floorThirteen : CrownLower.LowerBound 13 32) :
    CrownLower.LowerBound 15 36 := by
  have floorFourteen : CrownLower.LowerBound 14 34 :=
    CrownProduct.thresholdLowerStep (by decide : 2 ≤ 13) (by decide) floorThirteen
  intro s F tests compute
  exact CrownProduct.thresholdLowerStep (by decide : 2 ≤ 14) (by decide) floorFourteen tests compute

private theorem withTripleDeletion (floorThirteen : CrownLower.LowerBound 13 32)
    {E : SharedFormula (Fin 16)} (data : CrownThresholdFrontier.AtMargin 7 E) : AtMargin E := by
  refine ⟨data, fun s count => ?_⟩
  have left := retained_count s count
  have saving : (univ \ (univ \ s)).card = 3 := by
    rw [card_sdiff_of_subset (subset_univ _), left]
    decide
  have cost : gates E ≤ 32 + 2 * (univ \ (univ \ s)).card := by
    have used := CrownEleven.gates_of_two_reads E data.valid data.reads
    have extra := data.extra
    rw [saving]
    omega
  obtain ⟨_, _, _, live⟩ := tightSubset (by decide : 2 ≤ 13) floorThirteen
    E data.valid data.tests data.reads (univ \ s) left cost
  exact live

theorem crownBudget54 (floorThirteen : CrownLower.LowerBound 13 32)
    (small : RepSizeAtMost (fun u v : Fin 16 => decide (u ≠ v)) 54) :
    ∃ E : SharedFormula (Fin 16), AtMargin E := by
  obtain ⟨E, data⟩ := crownAtMargin (extra := 7) (by decide) (by decide) (by decide) (by decide)
    (floorFifteen floorThirteen) small
  exact ⟨E, withTripleDeletion floorThirteen data⟩

theorem thresholdBudget38 (floorThirteen : CrownLower.LowerBound 13 32) {s : ℕ}
    {F : CrownRun.BF 16} (test : ThresholdOn F) (compute : CrownLower.Computes 16 s F)
    (small : s ≤ 38) : ∃ E : SharedFormula (Fin 16), AtMargin E := by
  obtain ⟨E, data⟩ := thresholdAtMargin (n := 15) (extra := 7) (by decide) (by decide) (by decide)
    (by decide) (floorFifteen floorThirteen) test compute small
  exact ⟨E, withTripleDeletion floorThirteen data⟩

theorem thresholdFloor_of_exclusion (floorThirteen : CrownLower.LowerBound 13 32)
    (excluded : ¬ ∃ E : SharedFormula (Fin 16), AtMargin E) : CrownLower.LowerBound 16 39 := by
  intro s F test compute
  by_contra! small
  exact excluded (thresholdBudget38 floorThirteen test compute (by omega))

/-- The three-input restrictions require at least four singleton activators
    for every signal in the OR prefix. -/
theorem fourSingletons {E : SharedFormula (Fin 16)} (data : AtMargin E) {n k : ℕ}
    (pure : orPrefix E n) (early : k < n) (inside : k < numShared E) :
    4 ≤ (univ.filter fun i => signal E k (singletonInput i) = true).card := by
  classical
  by_contra! few
  set active := univ.filter fun i => signal E k (singletonInput i) = true with active_eq
  obtain ⟨s, contains, _, count⟩ := exists_subsuperset_card_eq (subset_univ active)
    (show active.card ≤ 3 by omega) (show 3 ≤ (univ : Finset (Fin 16)).card by decide)
  let keep := keepSubset (univ \ s) (retained_count s count)
  have on := live_after_restriction E keep (data.tripleDeletion s count) k inside
  have support : singletonDisjunction (signal E k) :=
    orStage E n pure (fun x a => x a) projection k early
  obtain ⟨i, present, accepts⟩ := (support (assignment keep (fun _ => true))).mp on
  have inActive : i ∈ active := mem_filter.mpr ⟨mem_univ _, accepts⟩
  have outside : i ∉ univ \ s := by simp [contains inActive]
  rw [assignment_outside (retained_count s count) _ outside] at present
  contradiction

/-- Each additional input adds at least two gates to a threshold-two floor. -/
theorem thresholdFloorExtend {m c : ℕ} (width : 2 ≤ m)
    (floor : CrownLower.LowerBound m (2 * m + c)) (extra : ℕ) :
    CrownLower.LowerBound (m + extra) (2 * (m + extra) + c) := by
  induction extra with
  | zero =>
    rw [Nat.add_zero]
    exact floor
  | succ extra ih =>
    have next : CrownLower.LowerBound (m + extra + 1) (2 * (m + extra) + c + 2) :=
      CrownProduct.thresholdLowerStep (by omega : 2 ≤ m + extra)
        (by omega : 0 < 2 * (m + extra) + c) ih
    rw [Nat.add_succ, show 2 * (m + extra + 1) + c = (2 * (m + extra) + c) + 2 by omega]
    exact @next

theorem crownFloorExtend {m c n s : ℕ} (width : 2 ≤ m) (larger : m ≤ n)
    (floor : CrownLower.LowerBound m (2 * m + c))
    (rep : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) : 3 * n + c ≤ s := by
  have onN : CrownLower.LowerBound n (2 * n + c) := by
    have extended : CrownLower.LowerBound (m + (n - m)) (2 * (m + (n - m)) + c) :=
      thresholdFloorExtend width floor (n - m)
    rwa [Nat.add_sub_of_le larger] at extended
  obtain ⟨C, mono, size, yes, no⟩ :=
    PEqualNP.Outside.L_meta_18677_aux.crown_discount_18508 n s (by omega) rep
  have lower := CrownLower.circuitBound (by omega) onN mono (CrownLower.thresholdTwoTests n)
    (CrownThreshold.thresholdOfSlice mono yes no)
  omega

/-- Count actual repeated uses even if simplification has left a shared
    stage with at most one reader. -/
def remainingSurplus {A : Type} : SharedFormula A → ℕ
  | .tree _ => 0
  | .share _ _ rest => (rest.weight (withHead 1 fun _ => 0) - 1) + remainingSurplus rest

theorem gates_le_raw_and_surplus {A : Type} (E : SharedFormula A) :
    gates E + 1 ≤ E.weight (fun _ => 1) + remainingSurplus E := by
  have leaves {B : Type} (f : Formula B) : leafWeight f (fun _ => 1) = formulaGates f + 1 := by
    induction f <;> simp_all [leafWeight, formulaGates] <;> omega
  induction E with
  | tree f => simp [gates, SharedFormula.weight, remainingSurplus, leaves]
  | @share B f count rest ih =>
    have split : (fun _ : Option B => (1 : ℕ)) = fun a =>
        withHead 0 (fun _ => 1) a + withHead 1 (fun _ => 0) a := by
      funext a
      cases a <;> rfl
    rw [split, weightAdd] at ih
    simp only [gates, SharedFormula.weight, remainingSurplus, leaves]
    omega

end CrownSixteenFrontier
