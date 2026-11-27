import CrownIndependentOr
import CrownOrCertificate
import CrownProduct

namespace CrownTenExact

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev crown (u v : Fin 10) : Bool := decide (u ≠ v)

theorem noSize33 : ¬ RepSizeAtMost crown 33 := by
  intro small
  obtain ⟨N, C, s, t, edge⟩ := CrownIndependentOr.crownTenRequiresLink small
  exact CrownOrCertificate.impossible C (CrownOrGraph.nonzero_of_link N edge)

/-- The minimum number of fan-in-two AND/OR gates for the ten-by-ten crown
    in the Desk representation model is 34. -/
theorem crownTenExact : RepSizeAtMost crown 34 ∧
    ∀ s, RepSizeAtMost crown s → 34 ≤ s := by
  refine ⟨CrownProduct.crownTenBounds.1, ?_⟩
  intro s existsCircuit
  by_contra! below
  have lower := CrownProduct.crownTenBounds.2 s existsCircuit
  have exact33 : s = 33 := by omega
  subst s
  exact noSize33 existsCircuit

/-- The lower bound uses only the rejection of singleton inputs
    and the acceptance of pairs. -/
theorem thresholdLowerTen : CrownLower.LowerBound 10 24 := by
  intro s F test compute
  by_contra! below
  have floor : CrownLower.LowerBound 9 21 := CrownProduct.thresholdLowerFromEight 1
  obtain ⟨E, valid, correct, raw, cost⟩ :=
    CrownMargin.forestAtMargin (by decide : 2 ≤ 9) floor (by omega) test compute
  have reuse : E.extraUses ≤ 4 := by omega
  obtain ⟨p, q, r, t, h, rfl⟩ :=
    CrownFourNormal.exactlyFour E valid correct (fun i => (raw i).le) (by decide) reuse
  have initial : CrownFourNormal.HasFourSharedThreshold := ⟨p, q, r, t, h, valid, correct, raw⟩
  have cases := CrownFirstAnd.threeCasesOfOrPrefix (CrownFirstOr.firstTwoOr initial)
  have allOr := (cases.resolve_left CrownThirdCounts.noOverlapAtThird).resolve_left
    CrownFourthCounts.noOverlapAtFourth
  obtain ⟨N, C⟩ := CrownOrSupport.of_orPrefix allOr
  obtain ⟨_, _, edge⟩ := CrownIndependentOr.requiresLink C
  exact CrownOrCertificate.impossible C (CrownOrGraph.nonzero_of_link N edge)

theorem thresholdLowerFromTen (k : ℕ) : CrownLower.LowerBound (10 + k) (24 + 2 * k) := by
  induction k with
  | zero => exact thresholdLowerTen
  | succ k ih =>
    rw [show 24 + 2 * (k + 1) = (24 + 2 * k) + 2 by omega]
    exact CrownProduct.thresholdLowerStep (by omega) (by omega) ih

theorem crownLowerFromTen {n s : ℕ} (atLeastTen : 10 ≤ n)
    (rep : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) : 3 * n + 4 ≤ s := by
  have floor : CrownLower.LowerBound n (2 * n + 4) := by
    have known : CrownLower.LowerBound (10 + (n - 10)) (24 + 2 * (n - 10)) :=
      thresholdLowerFromTen (n - 10)
    rwa [show 10 + (n - 10) = n by omega, show 24 + 2 * (n - 10) = 2 * n + 4 by omega] at known
  obtain ⟨C, mono, size, yes, no⟩ :=
    PEqualNP.Outside.L_meta_18677_aux.crown_discount_18508 n s (by omega) rep
  have lower := CrownLower.circuitBound (by omega) floor mono (CrownLower.thresholdTwoTests n)
    (CrownThreshold.thresholdOfSlice mono yes no)
  omega

end CrownTenExact
