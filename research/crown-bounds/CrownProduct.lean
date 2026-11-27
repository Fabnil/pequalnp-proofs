import CrownExact

namespace CrownProduct

open CrownRun CrownForks PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem thresholdLowerEight : CrownLower.LowerBound 8 19 := by
  intro s F test compute
  by_contra! small
  obtain ⟨p, q, r, h, valid, correct, reads⟩ :=
    CrownEight.budget18RequiresThree test compute (by omega)
  let net : CrownProfileThree.Network (Fin 8) := ⟨p, q, r, h⟩
  exact net.noEight (by decide) valid correct (fun i => (reads i).le)

theorem thresholdLowerStep {n bound : ℕ} (size : 2 ≤ n) (positive : 0 < bound)
    (floor : CrownLower.LowerBound n bound) :
    CrownLower.LowerBound (n + 1) (bound + 2) := by
  intro s F test compute
  by_contra! small
  refine CrownLower.cannotCompute size floor (budget := bound + 1) (by omega) ?_ test compute (by omega)
  intro t G idx run passes cost counts
  let p : Fin (n + 1) := 0
  have part := CrownErase.eraseProjection run p (CrownErase.restrictionNonzero size passes p)
  have smaller := floor (CrownErase.liftThreshold passes p) part
  rw [counts p] at smaller
  omega

theorem thresholdLowerFromEight (k : ℕ) : CrownLower.LowerBound (8 + k) (19 + 2 * k) := by
  induction k with
  | zero => exact thresholdLowerEight
  | succ k ih =>
    rw [show 19 + 2 * (k + 1) = (19 + 2 * k) + 2 by omega]
    exact thresholdLowerStep (by omega) (by omega) ih

theorem crownLowerFromEight {n s : ℕ} (atLeastEight : 8 ≤ n)
    (rep : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) : 3 * n + 3 ≤ s := by
  have floor : CrownLower.LowerBound n (2 * n + 3) := by
    have known : CrownLower.LowerBound (8 + (n - 8)) (19 + 2 * (n - 8)) :=
      thresholdLowerFromEight (n - 8)
    rwa [show 8 + (n - 8) = n by omega, show 19 + 2 * (n - 8) = 2 * n + 3 by omega] at known
  obtain ⟨C, mono, size, yes, no⟩ :=
    PEqualNP.Outside.L_meta_18677_aux.crown_discount_18508 n s (by omega) rep
  have lower := CrownLower.circuitBound (by omega) floor mono (CrownLower.thresholdTwoTests n)
    (CrownThreshold.thresholdOfSlice mono yes no)
  omega

/-- OR within each of three rows and three columns, then test each triple. -/
def nineWitness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [11, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [15, 6]⟩,
    ⟨.or, [1, 4]⟩, ⟨.or, [17, 7]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [19, 8]⟩,
    ⟨.or, [12, 14]⟩, ⟨.and, [12, 14]⟩, ⟨.and, [10, 21]⟩, ⟨.or, [22, 23]⟩,
    ⟨.or, [18, 20]⟩, ⟨.and, [18, 20]⟩, ⟨.and, [16, 25]⟩, ⟨.or, [26, 27]⟩,
    ⟨.or, [24, 28]⟩], 29⟩

set_option maxRecDepth 8192 in
private theorem nineWitnessCorrect :
    ∀ x : Fin 9 → Bool, nineWitness.eval (List.ofFn x) = CrownThreshold.thresholdTwo x := by
  decide +kernel

theorem crownNineExact :
    RepSizeAtMost (fun u v : Fin 9 => decide (u ≠ v)) 30 ∧
      ∀ s, RepSizeAtMost (fun u v : Fin 9 => decide (u ≠ v)) s → 30 ≤ s := by
  refine ⟨?_, fun _ h => crownLowerFromEight (by decide) h⟩
  apply (CrownThreshold.crownIffThreshold (n := 9) (budget := 21) (by decide)).mpr
  exact ⟨nineWitness, by simp [Monotone2, nineWitness], by decide, nineWitnessCorrect⟩

/-- The two inputs in the first cell are merged for the marginals and tested once as a pair. -/
def tenWitness : Circuit :=
  ⟨[⟨.or, [0, 9]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [3, 4]⟩,
    ⟨.or, [13, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [10, 3]⟩,
    ⟨.or, [17, 6]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [2, 5]⟩,
    ⟨.or, [21, 8]⟩, ⟨.or, [14, 16]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [12, 23]⟩,
    ⟨.or, [24, 25]⟩, ⟨.or, [20, 22]⟩, ⟨.and, [20, 22]⟩, ⟨.and, [18, 27]⟩,
    ⟨.or, [28, 29]⟩, ⟨.or, [26, 30]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [31, 32]⟩], 33⟩

set_option maxRecDepth 16384 in
private theorem tenWitnessCorrect :
    ∀ x : Fin 10 → Bool, tenWitness.eval (List.ofFn x) = CrownThreshold.thresholdTwo x := by
  decide +kernel

theorem crownTenBounds :
    RepSizeAtMost (fun u v : Fin 10 => decide (u ≠ v)) 34 ∧
      ∀ s, RepSizeAtMost (fun u v : Fin 10 => decide (u ≠ v)) s → 33 ≤ s := by
  refine ⟨?_, fun _ h => crownLowerFromEight (by decide) h⟩
  apply (CrownThreshold.crownIffThreshold (n := 10) (budget := 24) (by decide)).mpr
  exact ⟨tenWitness, by simp [Monotone2, tenWitness], by decide, tenWitnessCorrect⟩

end CrownProduct
