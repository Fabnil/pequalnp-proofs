import CrownConditionalCuts
import CrownPairFormula

namespace CrownElevenCases

open CrownForks CrownPairFormula PnpResearch Finset

/-- The three one-flag inputs and their pairwise joins require one more
    reading than a once-read formula allows. -/
theorem noThresholdOnThreeOnce {A : Type} [DecidableEq A] (f : Formula A) (key : Fin 3 → A)
    (off : ∀ i, f.evalWith (singletonInput (key i)) = false)
    (on : ∀ i j, i ≠ j → f.evalWith (pairInput (key i) (key j)) = true)
    (once : ∀ i, reads f (key i) ≤ 1) : False := by
  have packing := CrownConditionalCuts.packing f (univ : Finset (Fin 3)) (fun _ => false)
    (fun i => singletonInput (key i)) (fun _ => 1) 1 (fun _ _ _ => Bool.false_le _)
    (fun i _ => off i) (fun i _ j _ ne => on i j ne)
    (fun i _ => by simpa [rise, reads] using once i) (fun _ _ => le_rfl)
  simp at packing

end CrownElevenCases
