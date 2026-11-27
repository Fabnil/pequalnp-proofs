import PEqualNP.Defs

namespace LeafWheel29220

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) ||
  (x 1 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) ||
  (x 1 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)

def restricted (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 1 && x 5) ||
  (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) ||
  (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)

def insertFalse (x : Fin 7 → Bool) : Fin 8 → Bool :=
  ![x 0, x 1, false, x 2, x 4, x 3, x 5, x 6]

/-- Clearing leaf 2 and permuting inputs yields the graph of L-meta-10890. -/
theorem restriction : ∀ x : Fin 7 → Bool, target (insertFalse x) = restricted x := by
  decide +kernel

def circuit : Circuit := ⟨
  [⟨.or, [0, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [5, 10]⟩,
   ⟨.or, [1, 3]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [0, 1]⟩,
   ⟨.or, [4, 7]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [4, 7]⟩, ⟨.or, [11, 14]⟩,
   ⟨.or, [17, 18]⟩, ⟨.or, [19, 20]⟩], 21⟩

theorem upper : Monotone2 circuit ∧ circuit.size = 14 ∧
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) = target x := by
  refine ⟨?_, rfl, ?_⟩
  · simp [circuit, Monotone2]
  · decide +kernel

end LeafWheel29220
