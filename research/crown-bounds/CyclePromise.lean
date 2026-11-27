import PEqualNP.Defs.Represents
import PEqualNP.MetaComplexity.Helpers.TableSearch

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

private def oddGates (side offset base r : ℕ) : List Gate :=
  let n := 2 * r + 1
  let d := r + 1
  let merged := (List.range n).map fun i =>
    ⟨.or, [offset + (d * i) % n, side + offset + (d * (i + 1)) % n]⟩
  let neighbors := (List.range r).map fun i =>
    let left := if i = 0 then 2 * r else 2 * i - 1
    ⟨.or, [base + left, base + 2 * i + 1]⟩
  let products := (List.range r).map (fun i => ⟨.and, [base + 2 * i, base + n + i]⟩) ++
    [⟨.and, [base + 2 * r, base + 2 * r - 1]⟩]
  let combine := (List.range r).map fun i =>
    let left := if i = 0 then base + n + r else base + n + 2 * r + i
    ⟨.or, [left, base + n + r + i + 1]⟩
  merged ++ neighbors ++ products ++ combine

/-- Four pairwise different cycle lengths, all congruent to two modulo four. -/
def mixedOdd : Circuit :=
  ⟨oddGates 24 0 48 1 ++ oddGates 24 3 55 2 ++ oddGates 24 8 67 3 ++
    oddGates 24 15 84 4 ++ [⟨.or, [54, 66]⟩, ⟨.or, [83, 105]⟩, ⟨.or, [106, 107]⟩], 108⟩

private def mixedNext : ℕ → ℕ
  | 2 => 0
  | 7 => 3
  | 14 => 8
  | 23 => 15
  | i => i + 1

/-- Adjacency for the disjoint union of `C₆`, `C₁₀`, `C₁₄`, and `C₁₈`. -/
def mixedOddAdj (u v : Fin 24) : Bool :=
  decide (v = u ∨ v.val = mixedNext u.val)

open PEqualNP.MetaComplexity.Helpers

private def rowInputs (u : Fin 24) : List ℕ :=
  (List.ofFn fun i : Fin 24 => if i = u then 2 ^ 24 - 1 else 0) ++
    List.ofFn fun j : Fin 24 => 2 ^ j.val

private theorem mixedOnes : ∀ v : Fin 24, (2 ^ 24 - 1 : ℕ).testBit v.val = true := by
  decide +kernel

private theorem rowInputsBits (u v : Fin 24) :
    (rowInputs u).map (fun t => t.testBit v.val) = oneEach u v := by
  simp only [rowInputs, oneEach, List.map_append, List.map_ofFn]
  congr 1
  · congr 1
    funext i
    by_cases eq : i = u
    · simpa [eq] using mixedOnes v
    · simp [eq]
  · congr 1
    funext j
    simp [Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

private def mixedMask (u : Fin 24) : ℕ :=
  2 ^ u.val + 2 ^ mixedNext u.val

private def mixedTable (u : Fin 24) : ℕ :=
  (TableSearch.tabs (2 ^ 24 - 1) (rowInputs u) mixedOdd.gates).getD mixedOdd.output 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 600000 in
private theorem mixedRows (u : Fin 24) : mixedTable u = mixedMask u := by
  fin_cases u <;> decide +kernel

private theorem mixedBits : ∀ u v : Fin 24, (mixedMask u).testBit v.val = mixedOddAdj u v := by
  decide +kernel

theorem mixedOddUpper61 : RepSizeAtMost mixedOddAdj 61 := by
  have all : mixedOdd.gates.all allowed = true := by decide
  apply upper mixedOdd all (by decide)
  intro u v
  have pos := mixedOnes v
  have gok (g : Gate) (hg : g ∈ mixedOdd.gates) : TableSearch.GOk g := by
    have h := List.all_eq_true.mp all g hg
    cases op : g.op <;> simp [allowed, TableSearch.GOk, op] at h ⊢ <;> exact h
  have wires := TableSearch.wires_tabs (2 ^ 24 - 1) v.val pos mixedOdd.gates (rowInputs u) gok
  rw [rowInputsBits] at wires
  change (mixedOdd.wires (oneEach u v)).getD mixedOdd.output false = _
  rw [Circuit.wires, wires, TableSearch.getD_map_testBit]
  change (mixedTable u).testBit v.val = _
  rw [mixedRows, mixedBits]

end CyclePromise
