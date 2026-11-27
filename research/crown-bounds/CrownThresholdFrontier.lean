import CrownEleven
import CrownOrFrontier

namespace CrownThresholdFrontier

open CrownRun CrownForks CrownForest CrownForestCost CrownFourProfiles CrownDropZero
open CrownRestriction CrownOrFrontier CrownFirstAnd PnpResearch
open CrownProfileThree.Network (ones)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

structure AtMargin {n : ℕ} (extraUses : ℕ) (E : SharedFormula (Fin n)) : Prop where
  valid : E.Valid
  tests : ThresholdOn E.eval
  reads : ∀ i, E.weight (ones i) = 2
  extra : E.extraUses = extraUses
  atLeastFour : 4 ≤ numShared E
  atMostExtra : numShared E ≤ extraUses
  allActive : CrownDropZero.allActive E (Samples.raw (Fin n))
  allPrepared : AllPrepared (fun x => x) E
  notFull : ∀ i, ¬ full E (singletonInput i)

theorem AtMargin.prepared {n extra : ℕ} {E : SharedFormula (Fin n)} (data : AtMargin extra E) :
    Prepared (fun x => x) E := data.allPrepared.first

private theorem count_le_extra {A : Type} (E : SharedFormula A) (valid : E.Valid) :
    numShared E ≤ E.extraUses := by
  induction E with
  | tree f => rfl
  | share f extra rest ih =>
    have positive := valid.1
    have bound := ih valid.2.1
    change numShared rest + 1 ≤ extra + rest.extraUses
    omega

theorem thresholdAtMargin {n lower extra s : ℕ} {F : BF (n + 1)}
    (width : 10 ≤ n + 1) (rooms : extra + 4 < n + 1)
    (balance : lower + 3 = 2 * (n + 1) + extra) (positive : 0 < lower)
    (floor : CrownLower.LowerBound n lower)
    (test : ThresholdOn F) (compute : CrownLower.Computes (n + 1) s F) (small : s ≤ lower + 2) :
    ∃ E : SharedFormula (Fin (n + 1)), AtMargin extra E := by
  have size : 2 ≤ n := by omega
  obtain ⟨E, valid, tests, reads, budget⟩ := CrownMargin.forestAtMargin size floor small test compute
  have used := CrownEleven.gates_of_two_reads E valid reads
  have next : CrownLower.LowerBound (n + 1) (lower + 2) :=
    CrownProduct.thresholdLowerStep size positive floor
  have minimum : Minimum (fun x => x) E := by
    intro G works
    have bound := next works (evaluateForest G var (fun i => ⟨i, rfl⟩))
    omega
  have cost : gates E = lower + 2 := by
    have self := next tests (evaluateForest E var (fun i => ⟨i, rfl⟩))
    omega
  obtain ⟨G, preserves, _, prepared⟩ := prepareAll (fun x => x) E valid tests minimum
  have tests' : ThresholdOn G.eval := ⟨preserves.off, preserves.on⟩
  have reads' (i : Fin (n + 1)) : G.weight (ones i) = 2 :=
    (preserves.weight _).trans (reads i)
  have cost' : gates G = lower + 2 := preserves.cost.trans cost
  have extra' : G.extraUses = extra := by
    have total := CrownEleven.gates_of_two_reads G preserves.valid reads'
    omega
  have four : 4 ≤ numShared G := by
    obtain ⟨p, u, q, v, r, w, t, z, tail, shape⟩ :=
      CrownFourNormal.atLeastFour G preserves.valid tests' (fun i => (reads' i).le)
        (by simpa only [Fintype.card_fin] using width)
    rw [shape]
    simp only [numShared]
    omega
  have cap : numShared G ≤ extra := (count_le_extra G preserves.valid).trans_eq extra'
  have active : allActive G (Samples.raw (Fin (n + 1))) := by
    rcases activeOrCheaper G (Samples.raw (Fin (n + 1))) preserves.valid tests'.1 tests'.2 with
      live | ⟨bad, cheaper, passes⟩
    · exact live
    · have bound := next passes (evaluateForest bad var (fun i => ⟨i, rfl⟩))
      omega
  have cold := CrownFourNormal.emptyProfileCount G preserves.valid tests' (fun i => (reads' i).le)
    (by rw [Fintype.card_fin]; omega)
  refine ⟨G, ⟨preserves.valid, tests', reads', extra', four, cap, active, prepared, ?_⟩⟩
  intro i fullCase
  have count := cardLeOfFull G tests' (fun i => (reads' i).le) cold fullCase
  simp only [Fintype.card_fin] at count
  omega

theorem crownAtMargin {n lower extra : ℕ}
    (width : 10 ≤ n + 1) (rooms : extra + 4 < n + 1)
    (balance : lower + 3 = 2 * (n + 1) + extra) (positive : 0 < lower)
    (floor : CrownLower.LowerBound n lower)
    (small : RepSizeAtMost (fun u v : Fin (n + 1) => decide (u ≠ v)) ((n + 1) + (lower + 2))) :
    ∃ E : SharedFormula (Fin (n + 1)), AtMargin extra E := by
  obtain ⟨C, mono, size, correct⟩ :=
    (CrownThreshold.crownIffThreshold (n := n + 1) (budget := lower + 2) (by omega)).mp small
  let F : BF (n + 1) := CrownThreshold.thresholdTwo
  have test : ThresholdOn F := CrownLower.thresholdTwoTests (n + 1)
  have notOne : F ≠ oneF := by
    intro same
    have off := test.1 0
    rw [same] at off
    simp [oneF] at off
  obtain ⟨t, used, idx, run⟩ := CrownRun.fromCircuit mono F correct
    (CrownLower.thresholdNonzero (by omega) test) notOne
  have computes : CrownLower.Computes (n + 1) t F := by
    apply CrownLower.ucOfRun run
    intro wire mem
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp mem
    exact ⟨i, rfl⟩
  exact thresholdAtMargin width rooms balance positive floor test computes (used.trans size)

private theorem eval_all_true {A : Type} (f : Formula A) : f.evalWith (fun _ => true) = true := by
  induction f <;> simp_all [Formula.evalWith]

theorem live_after_restriction {A B : Type} (E : SharedFormula A) (keep : A → Option B)
    (keeps : KeepsLeaves keep E) (k : ℕ) (inside : k < numShared E) :
    signal E k (assignment keep (fun _ => true)) = true := by
  induction E generalizing B k with
  | tree f => simp [numShared] at inside
  | share f extra rest ih =>
    have head : f.evalWith (assignment keep (fun _ => true)) = true := by
      cases hf : formulaRestrict f keep with
      | none => have h := keeps.1; simp [hf] at h
      | some g =>
        have eval := formulaRestrict_eval f keep (fun _ => true)
        simpa only [hf, formulaEval, eval_all_true] using eval.symm
    cases k with
    | zero => exact head
    | succ k =>
      have tails : assignment (keepHead keep) (fun _ => true) =
          withHead true (assignment keep (fun _ => true)) := by
        funext a
        cases a with
        | none => rfl
        | some a => cases h : keep a <;> simp [assignment, keepHead, h]
      change signal rest k (withHead (f.evalWith (assignment keep (fun _ => true)))
        (assignment keep (fun _ => true))) = true
      rw [head, ← tails]
      exact ih (keepHead keep) keeps.2.2 k (by simpa only [numShared, Nat.succ_lt_succ_iff] using inside)

end CrownThresholdFrontier
