import PEqualNP.Defs.Represents

/-! Representative circuits for bipartite cycles on the one-row/one-column promise. -/

namespace CyclePromise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def adj {half copies : ℕ} (u v : Fin (half * copies)) : Bool :=
  decide (u.val / half = v.val / half ∧
    (v.val % half = u.val % half ∨ v.val % half = (u.val % half + 1) % half))

/-- Join the two cycles with the second copy in the opposite cyclic order. -/
def paired (half : ℕ) : Circuit :=
  let rev := fun i => (half - i) % half
  let q := (List.range half).map fun i => ⟨.or, [i, 3 * half + rev i]⟩
  let z := (List.range half).map fun i => ⟨.or, [half + rev i, 2 * half + i]⟩
  let neighbors := (List.range half).map fun i =>
    ⟨.or, [5 * half + i, 5 * half + (i + 1) % half]⟩
  let products := (List.range half).map fun i => ⟨.and, [4 * half + i, 6 * half + i]⟩
  let combine := (List.range (half - 1)).map fun i =>
    let left := if i = 0 then 7 * half else 8 * half + i - 1
    ⟨.or, [left, 7 * half + i + 1]⟩
  ⟨q ++ z ++ neighbors ++ products ++ combine, 9 * half - 2⟩

def eight : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [7, 4]⟩,
    ⟨.and, [0, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.and, [3, 11]⟩,
    ⟨.or, [12, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

/-- Merge column labels shifted by three, then test the resulting five-cycle. -/
def ten : Circuit :=
  ⟨[⟨.or, [0, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 7]⟩,
    ⟨.or, [12, 13]⟩, ⟨.or, [12, 11]⟩, ⟨.and, [10, 15]⟩, ⟨.and, [14, 16]⟩,
    ⟨.and, [13, 11]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩

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

theorem eightUpper11 : RepSizeAtMost (adj (half := 4) (copies := 1)) 11 :=
  upper eight (by decide) (by decide) (by decide +kernel)

theorem twoEightUpper19 : RepSizeAtMost (adj (half := 4) (copies := 2)) 19 :=
  upper (paired 4) (by decide) (by decide) (by decide +kernel)

theorem tenUpper12 : RepSizeAtMost (adj (half := 5) (copies := 1)) 12 :=
  upper ten (by decide) (by decide) (by decide +kernel)

/-- The cycle with `4 * r` vertices for `r ≥ 3`, in the order used by `adj`. -/
def evenWitness (r : ℕ) : Circuit :=
  let base := 4 * r
  let p := 5 * r - 2
  let q := 5 * r - 1
  let lastInternal := 3 * r - 1
  let bridge := 4 * r - 1
  let merged := (List.range (r - 2)).map (fun j =>
      ⟨.or, [r + j + 1, 2 * r + j + 1]⟩) ++
    [⟨.or, [r, 2 * r]⟩, ⟨.or, [2 * r - 1, 3 * r]⟩]
  let side := (List.range r).map fun j =>
    let second := if j < r - 2 then 3 * r + 1 + j else bridge
    ⟨.or, [j, second]⟩
  let neighbors := (List.range r).map fun j =>
    let operands := if j = 0 then [p, base]
      else if j < r - 2 then [base + j - 1, base + j]
      else if j = r - 2 then [base + r - 3, lastInternal]
      else [q, lastInternal]
    ⟨.or, operands⟩
  let products := (List.range r).map (fun j => ⟨.and, [5 * r + j, 6 * r + j]⟩) ++
    [⟨.and, [p, q]⟩]
  let combine := (List.range r).map fun i =>
    let left := if i = 0 then 7 * r else 8 * r + i
    ⟨.or, [left, 7 * r + i + 1]⟩
  ⟨merged ++ side ++ neighbors ++ products ++ combine, 9 * r⟩

theorem evenWitnessSize (r : ℕ) (hr : 3 ≤ r) : (evenWitness r).size = 5 * r + 1 := by
  simp [evenWitness, Circuit.size]
  omega

theorem twelveUpper16 : RepSizeAtMost (adj (half := 6) (copies := 1)) 16 :=
  upper (evenWitness 3) (by decide) (by decide) (by decide +kernel)

theorem sixteenUpper21 : RepSizeAtMost (adj (half := 8) (copies := 1)) 21 :=
  upper (evenWitness 4) (by decide) (by decide) (by decide +kernel)

end CyclePromise
