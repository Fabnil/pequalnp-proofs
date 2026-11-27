import PEqualNP.Outside.L_meta_18677
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace CrownThreshold

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_18677_aux

def thresholdTwo {n : ℕ} (x : Fin n → Bool) : Bool :=
  decide (2 ≤ (List.ofFn x).count true)

def HasThresholdTwo (n budget : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ budget ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = thresholdTwo x

def pairInput {n : ℕ} (u v : Fin n) (i : Fin n) : Bool :=
  decide (i = u ∨ i = v)

theorem pairCount {n : ℕ} (u v : Fin n) :
    (List.ofFn (pairInput u v)).count true = if u = v then 1 else 2 := by
  rw [List.count_ofFn]
  have support : (Finset.univ.filter fun a => pairInput u v a = true) = {u, v} := by
    ext a
    simp [pairInput]
  rw [support]
  split_ifs with eq
  · subst v
    simp
  · exact Finset.card_pair eq

theorem thresholdOfSlice {n : ℕ} {C : Circuit} (mono : Monotone2 C)
    (pos : ∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true)
    (neg : ∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = thresholdTwo x := by
  intro x
  by_cases enough : 2 ≤ (List.ofFn x).count true
  · rw [thresholdTwo, decide_eq_true enough]
    have count := enough
    rw [List.count_ofFn] at count
    obtain ⟨u, hu, v, hv, ne⟩ :=
      Finset.one_lt_card.mp (show 1 < (Finset.univ.filter fun i => x i = true).card from count)
    have pairSize : (List.ofFn (pairInput u v)).count true = 2 := by
      rw [pairCount]
      simp [ne]
    have value : C.eval (List.ofFn (pairInput u v)) = true := pos _ pairSize
    have order : LowMergeProof.LeL (List.ofFn (pairInput u v)) (List.ofFn x) := by
      intro i hi
      by_cases inside : i < n
      · have same : x ⟨i, inside⟩ = true := by
          have occurs : (⟨i, inside⟩ : Fin n) = u ∨ (⟨i, inside⟩ : Fin n) = v := by
            simpa [List.getD_eq_getElem?_getD, inside, pairInput] using hi
          rcases occurs with h | h
          · rw [h]; exact (Finset.mem_filter.mp hu).2
          · rw [h]; exact (Finset.mem_filter.mp hv).2
        simpa [List.getD_eq_getElem?_getD, inside] using same
      · simp [List.getD_eq_getElem?_getD, inside] at hi
    exact LowMergeProof.wires_mono C
      (fun g hg => by simpa using (mono g hg).1) _ _ (by simp) order C.output value
  · have few : (List.ofFn x).count true ≤ 1 := by omega
    rw [thresholdTwo, decide_eq_false enough]
    exact neg x few

theorem crownIffThreshold {n budget : ℕ} (hn : 2 ≤ n) :
    RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) (n + budget) ↔
      HasThresholdTwo n budget := by
  constructor
  · intro hc
    obtain ⟨C, mono, size, pos, neg⟩ := crown_discount_18508 n (n + budget) hn hc
    exact ⟨C, mono, by omega, thresholdOfSlice mono pos neg⟩
  · rintro ⟨D, mono, size, comp⟩
    let C : Circuit :=
      ⟨pairOrGates n ++ shiftGates (2 * n) D.gates, 2 * n + D.output⟩
    have cm : Monotone2 C := by
      intro g hg
      simp only [C, List.mem_append] at hg
      rcases hg with h | h
      · simpa using pairOrGates_mon n g h
      · simp only [shiftGates, List.mem_map] at h
        obtain ⟨g, hg, rfl⟩ := h
        simpa using mono g hg
    have cs : C.size ≤ n + budget := by
      simpa [C, Circuit.size, pairOrGates, shiftGates] using Nat.add_le_add_left size n
    refine ⟨C, cm, cs, ?_⟩
    intro u v
    have len : (oneEach u v).length = 2 * n := by
      simp [oneEach]
      omega
    have run : C.wires (oneEach u v) =
        oneEach u v ++ ioRun D.gates (List.ofFn (pairInput u v)) := by
      change ioRun (pairOrGates n ++ shiftGates (2 * n) D.gates) (oneEach u v) = _
      rw [ioRun, List.foldl_append]
      change ioRun (shiftGates (2 * n) D.gates)
        (ioRun (pairOrGates n) (oneEach u v)) = _
      rw [pairOrGates_eval, ioRun_shift _ _ _ _ len]
      rfl
    change (C.wires (oneEach u v)).getD (2 * n + D.output) false = _
    rw [run, List.getD_append_right _ _ _ _ (by omega), len, Nat.add_sub_cancel_left]
    change D.eval (List.ofFn (pairInput u v)) = _
    rw [comp, thresholdTwo, pairCount]
    by_cases huv : u = v <;> simp [huv]

theorem crownSevenTwentyTwo :
    RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 22 ↔ HasThresholdTwo 7 15 :=
  crownIffThreshold (n := 7) (budget := 15) (by decide)

section Packing

open Finset
open scoped BigOperators

-- The cube construction adapts the one in L_meta_18242. The bound
-- allows a different limit on the number of fixed coordinates per label.
def completionCube {K : Type} [Fintype K] [DecidableEq K] (pattern : K → Option Bool) :
    Finset (K → Bool) :=
  Fintype.piFinset fun i => (pattern i).elim univ singleton

def fixedCoordinates {K : Type} [Fintype K] (pattern : K → Option Bool) : Finset K :=
  univ.filter fun i => (pattern i).isSome

theorem completionCube_volume {K : Type} [Fintype K] [DecidableEq K] (pattern : K → Option Bool) :
    (completionCube pattern).card * 2 ^ (fixedCoordinates pattern).card =
      2 ^ Fintype.card K := by
  classical
  have size : (completionCube pattern).card =
      ∏ i : K, if (pattern i).isSome then 1 else 2 := by
    rw [completionCube, Fintype.card_piFinset]
    apply prod_congr rfl
    intro i _
    cases pattern i <;> simp
  have fixed : 2 ^ (fixedCoordinates pattern).card =
      ∏ i : K, if (pattern i).isSome then 2 else 1 := by
    rw [Finset.prod_ite]
    simp [fixedCoordinates]
  rw [size, fixed, ← prod_mul_distrib]
  calc
    _ = ∏ _ : K, (2 : ℕ) := by
      apply prod_congr rfl
      intro i _
      cases pattern i <;> simp
    _ = _ := by simp

theorem weightedPacking {V K : Type} [Fintype K] [DecidableEq K] (S : Finset V)
    (code : V → K → Option Bool) (b : V → ℕ) (B : ℕ)
    (separated : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ∃ k, (code i k = some false ∧ code j k = some true) ∨
        (code i k = some true ∧ code j k = some false))
    (degree : ∀ i ∈ S, (fixedCoordinates (code i)).card ≤ b i)
    (bounded : ∀ i ∈ S, b i ≤ B) : ∑ i ∈ S, 2 ^ (B - b i) ≤ 2 ^ B := by
  classical
  have disjointCubes : (S : Set V).PairwiseDisjoint (fun i => completionCube (code i)) := by
    intro i hi j hj ne
    apply disjoint_left.mpr
    intro f hf hg
    obtain ⟨k, h⟩ := separated i hi j hj ne
    change f ∈ Fintype.piFinset (fun k => (code i k).elim univ singleton) at hf
    change f ∈ Fintype.piFinset (fun k => (code j k).elim univ singleton) at hg
    have a := Fintype.mem_piFinset.mp hf k
    have c := Fintype.mem_piFinset.mp hg k
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
  let M := 2 ^ Fintype.card K
  have cap : ∑ i ∈ S, (completionCube (code i)).card ≤ M := by
    rw [← card_biUnion disjointCubes]
    simpa [M] using card_le_univ (S.biUnion fun i => completionCube (code i))
  have each (i : V) (hi : i ∈ S) :
      2 ^ (B - b i) * M ≤ (completionCube (code i)).card * 2 ^ B := by
    have base : M ≤ (completionCube (code i)).card * 2 ^ b i :=
      (completionCube_volume (code i)).symm.le.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (degree i hi)))
    calc
      _ ≤ 2 ^ (B - b i) * ((completionCube (code i)).card * 2 ^ b i) :=
        Nat.mul_le_mul_left _ base
      _ = _ := by
        rw [Nat.mul_left_comm, ← pow_add, Nat.sub_add_cancel (bounded i hi)]
  have sum : (∑ i ∈ S, 2 ^ (B - b i)) * M ≤ 2 ^ B * M := by
    calc
      _ = ∑ i ∈ S, 2 ^ (B - b i) * M := Finset.sum_mul S _ _
      _ ≤ ∑ i ∈ S, (completionCube (code i)).card * 2 ^ B := sum_le_sum each
      _ = (∑ i ∈ S, (completionCube (code i)).card) * 2 ^ B := (Finset.sum_mul S _ _).symm
      _ ≤ M * 2 ^ B := Nat.mul_le_mul_right _ cap
      _ = _ := Nat.mul_comm _ _
  by_contra! h
  exact (not_lt_of_ge sum) (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _))

theorem twoForkCapacity (cold left right both : ℕ) (l : left ≤ 2) (r : right ≤ 2)
    (b : both ≤ 2) (linked : both = 2 → left = 0)
    (packing : 4 * cold + 2 * left + 2 * right + both ≤ 16) :
    cold + left + right + both ≤ 6 := by
  by_cases h : both = 2
  · have := linked h
    omega
  · omega

theorem twoForkCodeCapacity {V K : Type} [Fintype K] [DecidableEq K] (S : Finset V)
    (p q : V → Bool) (code : V → K → Option Bool)
    (separated : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      ∃ k, (code i k = some false ∧ code j k = some true) ∨
        (code i k = some true ∧ code j k = some false))
    (degree : ∀ i ∈ S, (fixedCoordinates (code i)).card ≤ 2 + (p i).toNat + (q i).toNat)
    (left : (S.filter fun i => p i = true ∧ q i = false).card ≤ 2)
    (right : (S.filter fun i => p i = false ∧ q i = true).card ≤ 2)
    (both : (S.filter fun i => p i = true ∧ q i = true).card ≤ 2)
    (linked : (S.filter fun i => p i = true ∧ q i = true).card = 2 →
      (S.filter fun i => p i = true ∧ q i = false).card = 0) : S.card ≤ 6 := by
  let cold := (S.filter fun i => p i = false ∧ q i = false).card
  let a := (S.filter fun i => p i = true ∧ q i = false).card
  let b := (S.filter fun i => p i = false ∧ q i = true).card
  let d := (S.filter fun i => p i = true ∧ q i = true).card
  have count : S.card = cold + a + b + d := by
    calc
      _ = ∑ i ∈ S, (1 : ℕ) := by simp
      _ = ∑ i ∈ S, ((if p i = false ∧ q i = false then 1 else 0) +
          (if p i = true ∧ q i = false then 1 else 0) +
          (if p i = false ∧ q i = true then 1 else 0) +
          (if p i = true ∧ q i = true then 1 else 0)) := by
        apply sum_congr rfl
        intro i _
        cases p i <;> cases q i <;> simp
      _ = _ := by simp [sum_add_distrib, cold, a, b, d]
  have weight (i : V) : 2 ^ (4 - (2 + (p i).toNat + (q i).toNat)) =
      (if p i = false ∧ q i = false then 4 else 0) +
      (if p i = true ∧ q i = false then 2 else 0) +
      (if p i = false ∧ q i = true then 2 else 0) +
      (if p i = true ∧ q i = true then 1 else 0) := by
    cases p i <;> cases q i <;> decide
  have limit := weightedPacking S code (fun i => 2 + (p i).toNat + (q i).toNat) 4
    separated degree (fun i _ => by cases p i <;> cases q i <;> decide)
  simp only [weight] at limit
  have cap : 4 * cold + 2 * a + 2 * b + d ≤ 16 := by
    simpa [sum_add_distrib, sum_ite, cold, a, b, d, Nat.mul_comm] using limit
  rw [count]
  exact twoForkCapacity cold a b d left right both linked cap

end Packing

end CrownThreshold
