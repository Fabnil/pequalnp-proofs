import CrownThreshold

namespace CrownGridBounds

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open CrownThreshold Finset

/-- Row and column ORs of a three-by-four grid with its last cell empty. -/
private def witness11 : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [14, 6]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [17, 10]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [19, 8]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [21, 9]⟩,
    ⟨.or, [2, 6]⟩, ⟨.or, [23, 10]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [13, 16]⟩,
    ⟨.or, [13, 16]⟩, ⟨.and, [27, 18]⟩, ⟨.or, [26, 28]⟩, ⟨.and, [20, 22]⟩,
    ⟨.or, [20, 22]⟩, ⟨.and, [31, 24]⟩, ⟨.or, [30, 32]⟩, ⟨.or, [31, 24]⟩,
    ⟨.and, [34, 25]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [29, 36]⟩], 37⟩

/-- Row and column ORs of a full three-by-four grid. -/
private def witness12 : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [15, 6]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [18, 10]⟩,
    ⟨.or, [19, 11]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [21, 8]⟩, ⟨.or, [1, 5]⟩,
    ⟨.or, [23, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [25, 10]⟩, ⟨.or, [3, 7]⟩,
    ⟨.or, [27, 11]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [30, 20]⟩,
    ⟨.or, [29, 31]⟩, ⟨.and, [22, 24]⟩, ⟨.or, [22, 24]⟩, ⟨.and, [34, 26]⟩,
    ⟨.or, [33, 35]⟩, ⟨.or, [34, 26]⟩, ⟨.and, [37, 28]⟩, ⟨.or, [36, 38]⟩,
    ⟨.or, [32, 39]⟩], 40⟩

/-- A full three-by-four grid with two labels sharing the first cell. -/
private def witness13 : Circuit :=
  ⟨[⟨.or, [0, 12]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [15, 3]⟩,
    ⟨.or, [4, 5]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [8, 9]⟩,
    ⟨.or, [20, 10]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [23, 8]⟩,
    ⟨.or, [1, 5]⟩, ⟨.or, [25, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [27, 10]⟩,
    ⟨.or, [3, 7]⟩, ⟨.or, [29, 11]⟩, ⟨.and, [16, 19]⟩, ⟨.or, [16, 19]⟩,
    ⟨.and, [32, 22]⟩, ⟨.or, [31, 33]⟩, ⟨.and, [24, 26]⟩, ⟨.or, [24, 26]⟩,
    ⟨.and, [36, 28]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [36, 28]⟩, ⟨.and, [39, 30]⟩,
    ⟨.or, [38, 40]⟩, ⟨.or, [34, 41]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [42, 43]⟩], 44⟩

/-- Row and column ORs of a full four-by-four grid. -/
private def witness16 : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [16, 2]⟩, ⟨.or, [17, 3]⟩, ⟨.or, [4, 5]⟩,
    ⟨.or, [19, 6]⟩, ⟨.or, [20, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [22, 10]⟩,
    ⟨.or, [23, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [26, 15]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [28, 8]⟩, ⟨.or, [29, 12]⟩, ⟨.or, [1, 5]⟩,
    ⟨.or, [31, 9]⟩, ⟨.or, [32, 13]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [34, 10]⟩,
    ⟨.or, [35, 14]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [37, 11]⟩, ⟨.or, [38, 15]⟩,
    ⟨.and, [18, 21]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [41, 24]⟩, ⟨.or, [40, 42]⟩,
    ⟨.or, [41, 24]⟩, ⟨.and, [44, 27]⟩, ⟨.or, [43, 45]⟩, ⟨.and, [30, 33]⟩,
    ⟨.or, [30, 33]⟩, ⟨.and, [48, 36]⟩, ⟨.or, [47, 49]⟩, ⟨.or, [48, 36]⟩,
    ⟨.and, [51, 39]⟩, ⟨.or, [50, 52]⟩, ⟨.or, [46, 53]⟩], 54⟩

private def allowedGate (g : Gate) : Bool :=
  match g.op with
  | .or | .and => decide (g.inputs.length ≤ 2)
  | _ => false

private theorem monotoneOfAll {C : Circuit} (h : C.gates.all allowedGate = true) : Monotone2 C := by
  intro g hg
  have pass := List.all_eq_true.mp h g hg
  cases op : g.op <;> simp [allowedGate, op] at pass ⊢ <;> exact pass

private def inputSupport {n : ℕ} (x : Fin n → Bool) : Finset (Fin n) :=
  univ.filter fun i => x i = true

private theorem inputSupport_injective {n : ℕ} : Function.Injective (@inputSupport n) := by
  intro x y eq
  funext i
  have same : x i = true ↔ y i = true := by
    simpa [inputSupport] using Iff.of_eq (congrArg (i ∈ ·) eq)
  cases hx : x i <;> cases hy : y i <;> simp_all

private theorem support_pair {n : ℕ} (i j : Fin n) : inputSupport (pairInput i j) = {i, j} := by
  ext k
  simp [inputSupport, pairInput]

private def pairChecks (n : ℕ) (C : Circuit) (i : Fin n) : Bool :=
  (List.finRange n).all fun j => C.eval (List.ofFn (pairInput i j)) == decide (i ≠ j)

private theorem crownUpperOfPairTests {n budget : ℕ} (hn : 2 ≤ n) (C : Circuit)
    (mono : C.gates.all allowedGate = true) (size : C.size ≤ budget)
    (zero : C.eval (List.ofFn (fun _ : Fin n => false)) = false)
    (checks : ∀ i, pairChecks n C i = true) :
    RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) (n + budget) := by
  have monotone := monotoneOfAll mono
  have pairs (i j : Fin n) : C.eval (List.ofFn (pairInput i j)) = decide (i ≠ j) := by
    exact beq_iff_eq.mp (List.all_eq_true.mp (checks i) j (List.mem_finRange j))
  apply (crownIffThreshold hn).mpr
  refine ⟨C, monotone, size, thresholdOfSlice monotone ?_ ?_⟩
  · intro x two
    have count : (inputSupport x).card = 2 := by
      simpa [List.count_ofFn, inputSupport] using two
    obtain ⟨i, j, ne, support⟩ := card_eq_two.mp count
    have same := inputSupport_injective (support.trans (support_pair i j).symm)
    simp [same, pairs, ne]
  · intro x few
    have count : (inputSupport x).card ≤ 1 := by
      simpa [List.count_ofFn, inputSupport] using few
    rcases Nat.eq_zero_or_pos (inputSupport x).card with h | h
    · have same : x = (fun _ => false) := inputSupport_injective
        ((card_eq_zero.mp h).trans (by simp [inputSupport]))
      simpa only [same] using zero
    · obtain ⟨i, support⟩ := card_eq_one.mp (show (inputSupport x).card = 1 by omega)
      have same : x = pairInput i i := inputSupport_injective
        (support.trans (by simp [support_pair]))
      simp [same, pairs]

set_option maxRecDepth 32768 in
theorem crownElevenUpper : RepSizeAtMost (fun u v : Fin 11 => decide (u ≠ v)) 38 :=
  crownUpperOfPairTests (budget := 27) (by decide) witness11
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro i; fin_cases i <;> decide +kernel)

set_option maxRecDepth 32768 in
theorem crownTwelveUpper : RepSizeAtMost (fun u v : Fin 12 => decide (u ≠ v)) 41 :=
  crownUpperOfPairTests (budget := 29) (by decide) witness12
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro i; fin_cases i <;> decide +kernel)

set_option maxRecDepth 32768 in
theorem crownThirteenUpper : RepSizeAtMost (fun u v : Fin 13 => decide (u ≠ v)) 45 :=
  crownUpperOfPairTests (budget := 32) (by decide) witness13
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro i; fin_cases i <;> decide +kernel)

set_option maxRecDepth 32768 in
theorem crownSixteenUpper : RepSizeAtMost (fun u v : Fin 16 => decide (u ≠ v)) 55 :=
  crownUpperOfPairTests (budget := 39) (by decide) witness16
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro i; fin_cases i <;> decide +kernel)

end CrownGridBounds
