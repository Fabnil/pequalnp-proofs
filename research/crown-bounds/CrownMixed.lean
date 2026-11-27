import CrownBlocks

/-! Mixed disjoint unions of edges and three- and four-by-four crowns. -/

namespace CrownMixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def adj {edges threes fours : ℕ} (u v : Fin (edges + 3 * threes + 4 * fours)) : Bool :=
  let cut := edges + 3 * threes
  if u.val < edges then decide (u = v)
  else if u.val < cut then
    decide (edges ≤ v.val ∧ v.val < cut ∧
      (u.val - edges) / 3 = (v.val - edges) / 3 ∧ u ≠ v)
  else
    decide (cut ≤ v.val ∧ (u.val - cut) / 4 = (v.val - cut) / 4 ∧ u ≠ v)

def singleThree : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩,
    ⟨.or, [6, 7]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [9, 8]⟩, ⟨.or, [10, 11]⟩], 12⟩

def pairedThree : Circuit :=
  ⟨[⟨.or, [0, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 11]⟩,
    ⟨.or, [3, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [5, 8]⟩,
    ⟨.or, [16, 17]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [15, 16]⟩,
    ⟨.and, [12, 18]⟩, ⟨.and, [13, 19]⟩, ⟨.and, [14, 20]⟩,
    ⟨.or, [21, 22]⟩, ⟨.or, [24, 23]⟩], 25⟩

private def placeSquare (side newSide offset base : ℕ) (C : Circuit) : List Gate :=
  C.gates.map fun g =>
    ⟨g.op, g.inputs.map fun w =>
      if w < side then offset + w
      else if w < 2 * side then newSide + offset + (w - side)
      else base + (w - 2 * side)⟩

/-- One crown of each size, with any number of preceding independent edges. -/
def oneOfEach (edges : ℕ) : Circuit :=
  let side := edges + 7
  let base := 2 * side
  let crowns := placeSquare 3 side edges base singleThree ++
    placeSquare 4 side (edges + 3) (base + 7) CrownBlocks.singleLayeredWitness
  let merge := [⟨.or, [base + 6, base + 17]⟩]
  let extras := (List.range edges).flatMap fun i =>
    [⟨.and, [i, side + i]⟩, ⟨.or, [base + 18 + 2 * i, base + 19 + 2 * i]⟩]
  ⟨crowns ++ merge ++ extras, base + 18 + 2 * edges⟩

private def allowed (gate : Gate) : Bool :=
  match gate.op with
  | .and | .or => decide (gate.inputs.length ≤ 2)
  | _ => false

private theorem upper {n budget : ℕ} {A : Fin n → Fin n → Bool} (C : Circuit)
    (allAllowed : C.gates.all allowed = true) (cost : C.size ≤ budget)
    (agrees : Represents A C) : RepSizeAtMost A budget := by
  refine ⟨C, ?_, cost, agrees⟩
  intro g hg
  have h := List.all_eq_true.mp allAllowed g hg
  cases op : g.op <;> simp [allowed, op] at h ⊢ <;> exact h

theorem singleThreeUpper7 : RepSizeAtMost (adj (edges := 0) (threes := 1) (fours := 0)) 7 :=
  upper singleThree (by decide) (by decide) (by decide +kernel)

theorem pairedThreeUpper14 : RepSizeAtMost (adj (edges := 0) (threes := 2) (fours := 0)) 14 :=
  upper pairedThree (by decide) (by decide) (by decide +kernel)

theorem oneOfEachUpper19 : RepSizeAtMost (adj (edges := 0) (threes := 1) (fours := 1)) 19 :=
  upper (oneOfEach 0) (by decide) (by decide) (by decide +kernel)

theorem oneOfEachWithEdgeUpper21 : RepSizeAtMost
    (adj (edges := 1) (threes := 1) (fours := 1)) 21 :=
  upper (oneOfEach 1) (by decide) (by decide) (by decide +kernel)

theorem singleEdgeUpper0 : RepSizeAtMost (adj (edges := 1) (threes := 0) (fours := 0)) 0 :=
  upper ⟨[], 0⟩ (by decide) (by decide) (by decide +kernel)

end CrownMixed
