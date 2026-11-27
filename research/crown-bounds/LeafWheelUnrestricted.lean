import PEqualNP.Outside.L_meta_29220

namespace LeafWheelUnrestricted

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_29220

/-- The accepted certificate at size 13 covers every positive number of NOTs. -/
theorem signedLower (gates : List Gate) (out : ℕ) (fit : FanInTwo ⟨gates, out⟩)
    (correct : ∀ x, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = f x)
    (signed : ∃ g ∈ gates, g.op = .not) : 14 ≤ gates.length := by
  have lower := final gates.length ⟨⟨gates, out⟩, fit, le_rfl, correct⟩
  by_contra! small
  have tight : gates.length = 13 := by omega
  rcases bridge_not gates out fit signed correct with smaller | ⟨t, positive, S, subset, live⟩
  · exact iroot _ (by omega) smaller
  · rw [tight] at live
    exact iroot_pos positive subset live

/-- In the graph of L-meta-29220, AND/OR can replace any AND/OR/NOT circuit
of fan-in at most two at the same size or smaller. -/
theorem replaceNegations (gates : List Gate) (out : ℕ) (fit : FanInTwo ⟨gates, out⟩)
    (correct : ∀ x, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = f x) :
    ∃ gates' output,
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x, Circuit.eval ⟨gates', output⟩ (List.ofFn x) = f x := by
  by_cases signed : ∃ g ∈ gates, g.op = .not
  · exact ⟨onWit, 21, onWitBasis, signedLower gates out fit correct signed, onWitCorrect⟩
  · refine ⟨gates, out, ?_, le_rfl, correct⟩
    intro g mem
    obtain ⟨op, arity⟩ := fit g mem
    have basis : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using op
    have noNot : g.op ≠ .not := fun neg => signed ⟨g, mem, neg⟩
    exact ⟨by simpa only [noNot, or_false] using basis, arity⟩

end LeafWheelUnrestricted
