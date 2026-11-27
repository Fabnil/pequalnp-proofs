import PEqualNP.Defs.MetaComplexity

namespace TwoLit23430

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 8]⟩,
    ⟨.or, [6, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩], 13⟩

theorem eightGates :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (2114461 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h <;> subst g <;> simp

end TwoLit23430
