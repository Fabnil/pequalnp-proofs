import CrownDropZero
import PEqualNP.MetaComplexity.Helpers.TableSearch

/-! Bounds for disjoint unions of four-by-four crowns in the Desk model. -/

namespace CrownBlocks

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_18677_aux
open PEqualNP.MetaComplexity.Helpers
open CrownRun CrownForest CrownForestCost

def adj {blocks : ℕ} (u v : Fin (4 * blocks)) : Bool :=
  decide (u.val / 4 = v.val / 4 ∧ u.val % 4 ≠ v.val % 4)

private def blockGates (blocks block : ℕ) : List Gate :=
  let raw := 4 * block
  let base := 8 * blocks + 11 * block
  [⟨.or, [raw, 4 * blocks + raw]⟩,
   ⟨.or, [raw + 1, 4 * blocks + raw + 1]⟩,
   ⟨.or, [raw + 2, 4 * blocks + raw + 2]⟩,
   ⟨.or, [raw + 3, 4 * blocks + raw + 3]⟩,
   ⟨.or, [base, base + 1]⟩,
   ⟨.or, [base + 2, base + 3]⟩,
   ⟨.and, [base + 4, base + 5]⟩,
   ⟨.and, [base, base + 1]⟩,
   ⟨.and, [base + 2, base + 3]⟩,
   ⟨.or, [base + 7, base + 8]⟩,
   ⟨.or, [base + 6, base + 9]⟩]

private def joinGate (blocks preceding : ℕ) : Gate :=
  let first := if preceding = 0 then 8 * blocks + 10 else 19 * blocks + preceding - 1
  ⟨.or, [first, 8 * blocks + 11 * (preceding + 1) + 10]⟩

def witness (blocks : ℕ) : Circuit :=
  ⟨(List.range blocks).flatMap (blockGates blocks) ++
    (List.range (blocks - 1)).map (joinGate blocks), 20 * blocks - 2⟩

private theorem witnessMonotone (blocks : ℕ) : Monotone2 (witness blocks) := by
  intro g hg
  simp only [witness, List.mem_append, List.mem_flatMap, List.mem_map] at hg
  rcases hg with ⟨b, _, member⟩ | ⟨b, _, rfl⟩
  · simp only [blockGates, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · change ioOK (joinGate blocks b)
    simp [ioOK, joinGate]

private def rowTables {n : ℕ} (u : Fin n) : List ℕ :=
  (List.ofFn fun i : Fin n => if i = u then 2 ^ n - 1 else 0) ++
    List.ofFn fun j : Fin n => 2 ^ j.val

private theorem rowTableBits {n : ℕ} (u v : Fin n) :
    (rowTables u).map (fun t => t.testBit v.val) = oneEach u v := by
  simp only [rowTables, oneEach, List.map_append, List.map_ofFn]
  congr 1
  · congr 1
    funext i
    by_cases eq : i = u <;> simp [eq, v.isLt]
  · congr 1
    funext j
    simp [Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

private def rowOutput {blocks : ℕ} (C : Circuit) (u : Fin (4 * blocks)) : ℕ :=
  (TableSearch.tabs (2 ^ (4 * blocks) - 1) (rowTables u) C.gates).getD C.output 0

private def rowTarget {blocks : ℕ} (u : Fin (4 * blocks)) : ℕ :=
  (15 - 2 ^ (u.val % 4)) <<< (4 * (u.val / 4))

private theorem representsOfChecks {blocks : ℕ} (C : Circuit) (monotone : Monotone2 C)
    (checks : ∀ u : Fin (4 * blocks), rowOutput C u = rowTarget u)
    (bits : ∀ u v : Fin (4 * blocks), (rowTarget u).testBit v.val = adj u v) :
    Represents (adj (blocks := blocks)) C := by
  intro u v
  let mask := 2 ^ (4 * blocks) - 1
  have pos : mask.testBit v.val = true := by simp [mask, v.isLt]
  have allowed (g : Gate) (hg : g ∈ C.gates) : TableSearch.GOk g := by
    obtain ⟨op, arity⟩ := monotone g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    exact ⟨op.imp_right Or.inl, arity⟩
  have wires := TableSearch.wires_tabs mask v.val pos C.gates (rowTables u) allowed
  rw [rowTableBits u v] at wires
  change (C.wires (oneEach u v)).getD C.output false = _
  rw [Circuit.wires, wires, TableSearch.getD_map_testBit]
  change (rowOutput C u).testBit v.val = _
  rw [checks u, bits]

private theorem upperOfChecks {blocks size : ℕ} (C : Circuit) (monotone : Monotone2 C)
    (cost : C.size ≤ size) (checks : ∀ u : Fin (4 * blocks), rowOutput C u = rowTarget u)
    (bits : ∀ u v : Fin (4 * blocks), (rowTarget u).testBit v.val = adj u v) :
    RepSizeAtMost (adj (blocks := blocks)) size :=
  ⟨C, monotone, cost, representsOfChecks C monotone checks bits⟩

private theorem rowTargetBits {blocks : ℕ} (u v : Fin (4 * blocks)) :
    (rowTarget u).testBit v.val = adj u v := by
  have residue (i : Fin 4) (j : Fin 4) :
      (15 - 2 ^ i.val).testBit j.val = decide (i ≠ j) := by
    fin_cases i <;> fin_cases j <;> decide
  have outside (i : Fin 4) (j : ℕ) (large : 4 ≤ j) :
      (15 - 2 ^ i.val).testBit j = false := by
    apply Nat.testBit_lt_two_pow
    have bound : 16 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) large
    exact (Nat.sub_le _ _).trans_lt ((by decide : 15 < 16).trans_le bound)
  rw [rowTarget, Nat.testBit_shiftLeft]
  by_cases below : v.val < 4 * (u.val / 4)
  · have diff : v.val / 4 ≠ u.val / 4 := by omega
    simp [adj, Nat.not_le.mpr below, Ne.symm diff]
  · have above : 4 * (u.val / 4) ≤ v.val := by omega
    simp only [above, decide_true, Bool.true_and]
    by_cases same : v.val / 4 = u.val / 4
    · have eq : v.val - 4 * (u.val / 4) = v.val % 4 := by omega
      rw [eq]
      exact (residue ⟨u.val % 4, by omega⟩ ⟨v.val % 4, by omega⟩).trans
        (by simp [adj, same, Fin.ext_iff])
    · have high : 4 ≤ v.val - 4 * (u.val / 4) := by omega
      exact (outside ⟨u.val % 4, by omega⟩ _ high).trans (by simp [adj, Ne.symm same])

set_option maxRecDepth 32768 in
theorem twoUpper : RepSizeAtMost (adj (blocks := 2)) 23 :=
  upperOfChecks (witness 2) (witnessMonotone 2) (by decide)
    (by intro u; fin_cases u <;> decide +kernel) rowTargetBits

set_option maxRecDepth 32768 in
theorem fourUpper : RepSizeAtMost (adj (blocks := 4)) 47 :=
  upperOfChecks (witness 4) (witnessMonotone 4) (by decide)
    (by intro u; fin_cases u <;> decide +kernel) rowTargetBits

/-- Each AND checks a left input against the three other right inputs.
    The two right-hand pair ORs each serve two of the tests. -/
private def quotientGates : List Gate :=
  [⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩,
   ⟨.or, [5, 9]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [6, 8]⟩,
   ⟨.and, [0, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [3, 13]⟩,
   ⟨.or, [14, 15]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩]

private def pairGates (pairs pair : ℕ) : List Gate :=
  let left := 8 * pair
  let right := 8 * pairs + left
  let base := 16 * pairs + 21 * pair
  ((List.range 4).map fun i => ⟨.or, [left + i, right + 4 + i]⟩) ++
    ((List.range 4).map fun i => ⟨.or, [left + 4 + i, right + i]⟩) ++
    shiftGates base quotientGates

def pairedWitness (pairs : ℕ) : Circuit :=
  ⟨(List.range pairs).flatMap (pairGates pairs) ++
    (List.range (pairs - 1)).map (fun i =>
      let first := if i = 0 then 16 * pairs + 20 else 37 * pairs + i - 1
      ⟨.or, [first, 16 * pairs + 21 * (i + 1) + 20]⟩),
    38 * pairs - 2⟩

private def allowedBinary (g : Gate) : Bool :=
  match g.op with
  | .and | .or => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem monotoneOfGateCheck {C : Circuit} (all : C.gates.all allowedBinary = true) :
    Monotone2 C := by
  intro g hg
  have gate := List.all_eq_true.mp all g hg
  cases op : g.op <;> simp [allowedBinary, op] at gate ⊢ <;> exact gate

set_option maxRecDepth 32768 in
theorem twoUpper21 : RepSizeAtMost (adj (blocks := 2)) 21 :=
  upperOfChecks (pairedWitness 1) (monotoneOfGateCheck (by decide)) (by decide)
    (by intro u; fin_cases u <;> decide +kernel) rowTargetBits

set_option maxRecDepth 32768 in
theorem fourUpper43 : RepSizeAtMost (adj (blocks := 4)) 43 :=
  upperOfChecks (pairedWitness 2) (monotoneOfGateCheck (by decide)) (by decide)
    (by intro u; fin_cases u <;> decide +kernel) rowTargetBits

/-- The ORs of inputs 3 and 7 meet indirectly through wires 12 and 13. -/
def crownFourWithoutFourthPair : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩,
    ⟨.and, [8, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [3, 12]⟩,
    ⟨.and, [9, 13]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 13]⟩,
    ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩], 18⟩

set_option maxRecDepth 32768 in
theorem crownFourWithoutFourthPair_correct :
    Monotone2 crownFourWithoutFourthPair ∧
      crownFourWithoutFourthPair.size = 11 ∧
      Represents (adj (blocks := 1)) crownFourWithoutFourthPair ∧
      (∀ i : Fin 8, (crownFourWithoutFourthPair.gates.flatMap Gate.inputs).count i.val = 1) ∧
      (∀ g ∈ crownFourWithoutFourthPair.gates, g.inputs ≠ [3, 7] ∧ g.inputs ≠ [7, 3]) := by
  have monotone : Monotone2 crownFourWithoutFourthPair := monotoneOfGateCheck (by decide)
  refine ⟨monotone, by decide, representsOfChecks crownFourWithoutFourthPair monotone ?_ rowTargetBits,
    ?_, ?_⟩
  · intro u
    fin_cases u <;> decide +kernel
  · intro i
    fin_cases i <;> decide
  · intro g hg
    simp only [crownFourWithoutFourthPair, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

namespace AfterThreePairs

private def half (overlap : Bool) (r c : ℕ) : Bool :=
  decide (¬(r = 1 ∧ c = 2) ∧ ¬(overlap = true ∧ r = 0 ∧ c = 1))

/-- The remaining two-by-three block and its transpose, with cross cells rejected. -/
def adj (overlap : Bool) (u v : Fin 5) : Bool :=
  if u.val < 2 then
    if v.val < 3 then half overlap u.val v.val else false
  else
    if 3 ≤ v.val then half overlap (v.val - 3) (u.val - 2) else false

def remainingRows (overlap : Bool) : Fin 5 → Fin 8 :=
  if overlap then ![2, 3, 5, 6, 7] else ![2, 3, 4, 5, 7]

def remainingColumns (overlap : Bool) : Fin 5 → Fin 8 :=
  if overlap then ![1, 2, 3, 6, 7] else ![0, 1, 3, 6, 7]

theorem adj_restrict (overlap : Bool) (u v : Fin 5) :
    adj overlap u v = CrownBlocks.adj (blocks := 2) (remainingRows overlap u) (remainingColumns overlap v) := by
  cases overlap <;> fin_cases u <;> fin_cases v <;> decide +kernel

private def witness (overlap : Bool) : Circuit :=
  ⟨[⟨.or, [0, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [4, 7]⟩] ++
    (if overlap then
      [⟨.or, [12, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [10, 15]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [17, 18]⟩]
    else
      [⟨.or, [10, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [15, 16]⟩, ⟨.and, [10, 14]⟩, ⟨.or, [17, 18]⟩]), 19⟩

set_option maxRecDepth 8192 in
theorem upperTen (overlap : Bool) : RepSizeAtMost (adj overlap) 10 := by
  refine ⟨witness overlap, monotoneOfGateCheck (by cases overlap <;> decide), ?_, ?_⟩
  · cases overlap <;> decide
  · intro u v
    cases overlap <;> fin_cases u <;> fin_cases v <;> decide +kernel

private theorem required (overlap : Bool) : ∀ i ∈ Finset.range 10, PnpResearch.Bipartite.Needed (adj overlap) i := by
  have check (i : Fin 10) : PnpResearch.Bipartite.Needed (adj overlap) i.val := by
    cases overlap <;> fin_cases i <;> unfold PnpResearch.Bipartite.Needed <;> decide +kernel
  intro i hi
  exact check ⟨i, Finset.mem_range.mp hi⟩

theorem noNine (overlap : Bool) : ¬ RepSizeAtMost (adj overlap) 9 := by
  apply PnpResearch.Bipartite.not_rep_size_of_path (a := 0) (b := 1) (c := 0) (d := 2)
    (Finset.range 10) (required overlap) (by decide)
  all_goals cases overlap <;> decide

end AfterThreePairs

/-- Compile a monotone run while keeping the wires for earlier functions available. -/
private theorem realizeRun {n s : ℕ} {A : BF n → Prop} {F : BF n}
    (trace : UC gF MonoA s A F) (earlier : List Gate)
    (present : ∀ f, A f → ∃ wire < n + earlier.length, ∀ x : Fin n → Bool,
      (ioRun earlier (List.ofFn x)).getD wire false = f x) :
    ∃ (tail : List Gate) (wire : ℕ), tail.length ≤ s ∧
      (∀ g ∈ tail, ioOK g) ∧ wire < n + (earlier ++ tail).length ∧
      ∀ x : Fin n → Bool, (ioRun (earlier ++ tail) (List.ofFn x)).getD wire false = F x := by
  induction s generalizing A earlier with
  | zero =>
    obtain ⟨wire, bound, eval⟩ := present F trace
    exact ⟨[], wire, by simp, by simp, by simpa using bound, by simpa using eval⟩
  | succ s ih =>
    rcases trace with faster | ⟨op, l, r, allowed, left, right, rest⟩
    · obtain ⟨tail, wire, cost, mono, bound, eval⟩ := ih faster earlier present
      exact ⟨tail, wire, by omega, mono, bound, eval⟩
    · obtain ⟨a, ab, ae⟩ := present l left
      obtain ⟨b, bb, be⟩ := present r right
      let g : Gate := ⟨if op = 0 then .and else .or, [a, b]⟩
      let next := earlier ++ [g]
      have length : next.length = earlier.length + 1 := by simp [next]
      have ready (f : BF n) (hf : f = gF op l r ∨ A f) : ∃ wire < n + next.length,
          ∀ x : Fin n → Bool, (ioRun next (List.ofFn x)).getD wire false = f x := by
        rcases hf with rfl | old
        · refine ⟨n + earlier.length, by omega, ?_⟩
          intro x
          have wires : (ioRun earlier (List.ofFn x)).length = n + earlier.length := by
            simp [ioLen]
          change (ioRun (earlier ++ [g]) (List.ofFn x)).getD (n + earlier.length) false = _
          rw [ioSnoc, ← wires, ioLast]
          rcases mono_cases op allowed with rfl | rfl
          · simpa [g, GateOp.eval, gF_and, List.getD_eq_getElem?_getD] using
              congrArg₂ (· && ·) (ae x) (be x)
          · simpa [g, GateOp.eval, gF_or, List.getD_eq_getElem?_getD] using
              congrArg₂ (· || ·) (ae x) (be x)
        · obtain ⟨wire, bound, eval⟩ := present f old
          refine ⟨wire, by omega, fun x => ?_⟩
          change (ioRun (earlier ++ [g]) (List.ofFn x)).getD wire false = _
          rw [ioPrefix, eval]
          simpa using bound
      obtain ⟨tail, wire, cost, mono, bound, eval⟩ := ih rest next ready
      refine ⟨g :: tail, wire, by simp; omega, ?_, ?_, ?_⟩
      · intro h member
        rcases List.mem_cons.mp member with rfl | member
        · rcases mono_cases op allowed with rfl | rfl <;> simp [g, ioOK]
        · exact mono h member
      · simpa [next, List.append_assoc] using bound
      · simpa [next, List.append_assoc] using eval

theorem runToCircuit {n s : ℕ} {F : BF n}
    (trace : CrownLower.Computes n s F) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x := by
  have present (f : BF n) (hf : ∃ i : Fin n, f = var i) :
      ∃ wire < n + ([] : List Gate).length, ∀ x : Fin n → Bool,
      (ioRun [] (List.ofFn x)).getD wire false = f x := by
    obtain ⟨i, rfl⟩ := hf
    refine ⟨i, i.isLt, fun x => ?_⟩
    simp [ioRun, var, List.getD_eq_getElem?_getD, i.isLt]
  obtain ⟨gates, wire, cost, mono, _, eval⟩ := realizeRun trace [] present
  exact ⟨⟨gates, wire⟩, fun g hg => by simpa [ioOK] using mono g hg, cost,
    fun x => by simpa [Circuit.eval, Circuit.wires, ioRun] using eval x⟩

end CrownBlocks
