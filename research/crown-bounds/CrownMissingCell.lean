import PEqualNP.Defs.Represents

namespace CrownMissingCell

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

/-- The matrix in L-meta-25467, in the Desk's input order. -/
def adj (u v : Fin 5) : Bool :=
  (32435687 : ℕ).testBit (5 * u.val + v.val)

def normalAdj (u v : Fin 5) : Bool :=
  decide (u ≠ v ∧ ¬ (u = 0 ∧ v = 1))

def columnIndex : Fin 5 → Fin 5 := ![3, 4, 2, 1, 0]

theorem agreesWithNormal : ∀ u v, adj u (columnIndex v) = normalAdj u v := by
  decide +kernel

theorem rowNeighborhoodInclusion : ∀ i j : Fin 5,
    (∀ c, normalAdj i c = true → normalAdj j c = true) ↔ i = j ∨ (i = 0 ∧ j = 1) := by
  decide +kernel

theorem colNeighborhoodInclusion : ∀ i j : Fin 5,
    (∀ r, normalAdj r i = true → normalAdj r j = true) ↔ i = j ∨ (i = 1 ∧ j = 0) := by
  decide +kernel

/-- The three ordinary labels use a threshold-two test. A separate product
    covers ordinary-to-special cells, and one AND covers the last edge. -/
def witness : Circuit :=
  ⟨[⟨.or, [2, 7]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [10, 11]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [14, 15]⟩,
    ⟨.or, [13, 12]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [18, 19]⟩,
    ⟨.and, [17, 20]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [23, 22]⟩], 24⟩

private def allowed (gate : Gate) : Bool :=
  match gate.op with
  | .and | .or => decide (gate.inputs.length ≤ 2)
  | _ => false

private theorem witnessMonotone : Monotone2 witness := by
  intro g hg
  have all : witness.gates.all allowed = true := by decide
  have hg' := List.all_eq_true.mp all g hg
  cases op : g.op <;> simp [allowed, op] at hg' ⊢ <;> exact hg'

theorem upper15 : RepSizeAtMost adj 15 :=
  ⟨witness, witnessMonotone, by decide, by decide +kernel⟩

end CrownMissingCell
