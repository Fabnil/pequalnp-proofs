import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs.MetaComplexityLgpMono

namespace PEqualNP.Outside.L_meta_48488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev X := Fin 6 → Bool
abbrev F := X → Bool

def target : F := fun x => Nat.testBit 18368186892755183744
  (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.and, [5, 7]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [6, 13]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [1, 17]⟩,
    ⟨.and, [15, 18]⟩], 19⟩

theorem witness_mono : Monotone2 witness := by simp [Monotone2, witness]

theorem witness_size : witness.size = 14 := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem witness_eval : ∀ x : X, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem upper14 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 14 ∧
    ∀ x : X, C.eval (List.ofFn x) = target x :=
  ⟨witness, witness_mono, witness_size.le, witness_eval⟩

end PEqualNP.Outside.L_meta_48488
