import CrownConditionalCuts
import CrownRestriction

namespace CrownMajorityFive

open CrownForks CrownForest CrownForestCost CrownDropZero CrownRestriction CrownPairFormula
open PnpResearch Finset

private abbrev Bit := Fin 5

def majority (x : Bit → Bool) : Bool := decide (3 ≤ (List.ofFn x).count true)

private def dual {A : Type} : Formula A → Formula A
  | .var a => .var a
  | .conj l r => .disj (dual l) (dual r)
  | .disj l r => .conj (dual l) (dual r)

private theorem dual_eval {A : Type} (f : Formula A) (x : A → Bool) :
    (dual f).evalWith x = !f.evalWith (fun a => !x a) := by
  induction f <;> simp_all [dual, Formula.evalWith, Bool.not_and, Bool.not_or]

private theorem dual_weight {A : Type} (f : Formula A) (w : A → ℕ) :
    leafWeight (dual f) w = leafWeight f w := by
  induction f <;> simp_all [dual, leafWeight]

private theorem selfDual : ∀ x : Bit → Bool, (!majority (fun i => !x i)) = majority x := by
  decide +kernel

private def erase (p i : Bit) : Option Bit := if i = p then none else some i

private theorem erase_missing (p : Bit) : missing (erase p) = fun a => (singletonInput p a).toNat := by
  funext a
  by_cases h : a = p <;> simp [singletonInput, missing, erase, h]

private def countReads {A : Type} [DecidableEq A] (f : Option (Formula A)) (i : A) : ℕ :=
  match f with
  | none => 0
  | some f => reads f i

private theorem restrict_reads {A B : Type} [DecidableEq B] (f : Formula A)
    (keep : A → Option B) (i : B) :
    countReads (formulaRestrict f keep) i ≤
      leafWeight f (fun a => ((keep a).map fun k => (singletonInput i k).toNat).getD 0) := by
  induction f with
  | var a =>
    cases h : keep a <;> simp [formulaRestrict, h, countReads, reads, leafWeight]
  | conj l r il ir | disj l r il ir =>
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [hl, hr, formulaRestrict, countReads, reads, leafWeight] at * <;> omega

private theorem erase_reads (f : Formula Bit) {p i : Bit} (ne : i ≠ p) :
    countReads (formulaRestrict f (erase p)) i ≤ reads f i := by
  have kept : (fun a => ((erase p a).map fun k => (singletonInput i k).toNat).getD 0) =
      fun a => (singletonInput i a).toNat := by
    funext a
    by_cases h : a = p <;> simp [erase, singletonInput, h, ne.symm]
  simpa only [kept, reads] using restrict_reads f (erase p) i

private theorem sum_reads (f : Formula Bit) : ∑ i : Bit, reads f i = formulaGates f + 1 := by
  have all : (fun _ : Bit => (1 : ℕ)) = fun a => ∑ i : Bit, (singletonInput i a).toNat := by
    funext a
    rw [sum_eq_single_of_mem a (mem_univ _)]
    · simp [singletonInput]
    · intro i _ ne
      simp [singletonInput, ne.symm]
  have h := weightGates (SharedFormula.tree f) trivial
  rw [all, weightSum] at h
  simpa [SharedFormula.weight, SharedFormula.extraUses, gates, reads] using h

private theorem enoughWhenAllRemainingOn :
    ∀ p : Bit, majority (assignment (erase p) (fun _ => true)) = true := by decide +kernel

private theorem enoughWhenOneRemainingOff :
    ∀ p i : Bit, i ≠ p → majority (assignment (erase p) (fun j => !singletonInput i j)) = true := by
  decide +kernel

private theorem notEnoughWhenTwoRemainingOff :
    ∀ p i j : Bit, i ≠ p → j ≠ p → i ≠ j →
      majority (assignment (erase p) (fun k => !pairInput i j k)) = false := by decide +kernel

/-- Setting one input to zero leaves a formula that must still use each of
    the other four inputs twice. This follows by dualizing and packing the
    singleton cuts for the resulting two-of-four function. -/
private theorem cofactor_reads (f : Formula Bit) (correct : f.evalWith = majority)
    (cap : ∀ i, reads f i ≤ 2) (p : Bit) :
    ∃ g, formulaRestrict f (erase p) = some g ∧ ∀ i, i ≠ p → reads g i = 2 := by
  cases eq : formulaRestrict f (erase p) with
  | none =>
    have value := formulaRestrict_eval f (erase p) (fun _ => true)
    rw [eq, formulaEval, correct, enoughWhenAllRemainingOn] at value
    contradiction
  | some g =>
    refine ⟨g, rfl, ?_⟩
    let S := (univ : Finset Bit).erase p
    have remaining (i : Bit) (ne : i ≠ p) : reads g i ≤ 2 := by
      have h := erase_reads f ne
      rw [eq] at h
      exact h.trans (cap i)
    have card : S.card = 4 := by simp [S]
    have off (i : Bit) (hi : i ∈ S) : (dual g).evalWith (singletonInput i) = false := by
      rw [dual_eval]
      have value := formulaRestrict_eval f (erase p) (fun j => !singletonInput i j)
      rw [eq, formulaEval, correct, enoughWhenOneRemainingOff p i (mem_erase.mp hi).1] at value
      simp [value]
    have on (i : Bit) (hi : i ∈ S) (j : Bit) (hj : j ∈ S) (ne : i ≠ j) :
        (dual g).evalWith (pairInput i j) = true := by
      rw [dual_eval]
      have value := formulaRestrict_eval f (erase p) (fun k => !pairInput i j k)
      rw [eq, formulaEval, correct,
        notEnoughWhenTwoRemainingOff p i j (mem_erase.mp hi).1 (mem_erase.mp hj).1 ne] at value
      simp [value]
    have readDual (i : Bit) : reads (dual g) i = reads g i := dual_weight g _
    have packing := CrownConditionalCuts.packing (dual g) S (fun _ => false)
      singletonInput (reads g) 2 (fun _ _ _ => Bool.false_le _) off on
      (fun i _ => by simpa [rise, reads] using (readDual i).le)
      (fun i hi => remaining i (mem_erase.mp hi).1)
    intro i ne
    have hi : i ∈ S := mem_erase.mpr ⟨ne, mem_univ _⟩
    by_contra! notTwo
    have low : reads g i ≤ 1 := by have h := remaining i ne; omega
    have bound (j : Bit) : 1 ≤ 2 ^ (2 - reads g j) := Nat.pow_pos (by decide)
    have strict : 1 < 2 ^ (2 - reads g i) := by interval_cases reads g i <;> decide
    have sum := sum_lt_sum (fun j _ => bound j) ⟨i, hi, strict⟩
    simp only [sum_const, Nat.nsmul_eq_mul, Nat.mul_one, card] at sum
    omega

private theorem tight_cofactor (f : Formula Bit) (correct : f.evalWith = majority)
    (cap : ∀ i, reads f i ≤ 2) (p : Bit) : FormulaKeepsLeaves (erase p) f := by
  have exactReads (i : Bit) : reads f i = 2 := by
    obtain ⟨j, ne⟩ := exists_ne i
    obtain ⟨g, eq, full⟩ := cofactor_reads f correct cap j
    have le := erase_reads f ne.symm
    rw [eq, countReads, full i ne.symm] at le
    exact le_antisymm (cap i) le
  have total := sum_reads f
  simp [exactReads] at total
  obtain ⟨g, eq, full⟩ := cofactor_reads f correct cap p
  let S := (univ : Finset Bit).erase p
  have four : (∑ i ∈ S, reads g i) = 8 := by
    rw [sum_congr rfl (fun i hi => full i (mem_erase.mp hi).1)]
    simp
  have atLeast := sum_le_sum_of_subset (f := reads g) (subset_univ S)
  rw [four, sum_reads] at atLeast
  have atMost := formulaRestrict_leaves f (erase p)
  rw [eq, formulaLeaves, erase_missing] at atMost
  change formulaGates g + 1 + reads f p ≤ formulaGates f + 1 at atMost
  apply formula_tight_keeps_leaves f (erase p)
  rw [eq, formulaLeaves, erase_missing]
  change formulaGates g + 1 + reads f p = formulaGates f + 1
  rw [exactReads] at atMost ⊢
  omega

private def oneKey (i : Bit) : Formula Bit → Prop
  | .var j => i = j
  | .conj l r | .disj l r => oneKey i l ∧ oneKey i r

private theorem oneKey_dual {i : Bit} {f : Formula Bit} (h : oneKey i f) : oneKey i (dual f) := by
  induction f <;> simp_all [oneKey, dual]

private theorem oneKey_erases {i : Bit} {f : Formula Bit} (h : oneKey i f) (p : Bit) :
    (formulaRestrict f (erase p)).isNone = decide (i = p) := by
  induction f with
  | var j =>
    obtain rfl : i = j := h
    by_cases eq : i = p <;> simp [formulaRestrict, erase, eq]
  | conj l r il ir | disj l r il ir =>
    change oneKey i l ∧ oneKey i r at h
    have left := il h.1
    have right := ir h.2
    cases hl : formulaRestrict l (erase p) <;> cases hr : formulaRestrict r (erase p) <;>
      simp_all [formulaRestrict]

private theorem oneKey_evaluates {i : Bit} {f : Formula Bit} (h : oneKey i f) (x : Bit → Bool) :
    f.evalWith x = x i := by
  induction f with
  | var j => obtain rfl : i = j := h; rfl
  | conj l r il ir | disj l r il ir =>
    change oneKey i l ∧ oneKey i r at h
    simp [Formula.evalWith, il h.1, ir h.2]

private theorem one_key_of_tight_duals (f : Formula Bit)
    (direct : ∀ i, FormulaKeepsLeaves (erase i) f)
    (opposite : ∀ i, FormulaKeepsLeaves (erase i) (dual f)) : ∃ i, oneKey i f := by
  induction f with
  | var i => exact ⟨i, rfl⟩
  | conj l r il ir =>
    obtain ⟨i, left⟩ := il (fun i => (direct i).1) (fun i => (opposite i).1)
    obtain ⟨j, right⟩ := ir (fun i => (direct i).2.1) (fun i => (opposite i).2)
    have same := (direct i).2.2
    rw [oneKey_erases left i, oneKey_erases right i, decide_eq_true rfl] at same
    have eq : j = i := of_decide_eq_true same.symm
    subst j
    exact ⟨i, left, right⟩
  | disj l r il ir =>
    obtain ⟨i, left⟩ := il (fun i => (direct i).1) (fun i => (opposite i).1)
    obtain ⟨j, right⟩ := ir (fun i => (direct i).2) (fun i => (opposite i).2.1)
    have same := (opposite i).2.2
    rw [oneKey_erases (oneKey_dual left) i, oneKey_erases (oneKey_dual right) i, decide_eq_true rfl] at same
    have eq : j = i := of_decide_eq_true same.symm
    subst j
    exact ⟨i, left, right⟩

theorem noReadTwiceMajority (f : Formula Bit) (correct : f.evalWith = majority)
    (cap : ∀ i, reads f i ≤ 2) : False := by
  have dualCorrect : (dual f).evalWith = majority := by
    funext x
    rw [dual_eval, correct, selfDual]
  have dualCap (i : Bit) : reads (dual f) i ≤ 2 := (dual_weight f _).trans_le (cap i)
  obtain ⟨i, one⟩ := one_key_of_tight_duals f (tight_cofactor f correct cap)
    (tight_cofactor (dual f) dualCorrect dualCap)
  have value := oneKey_evaluates one (singletonInput i)
  have off : ∀ i : Bit, majority (singletonInput i) = false := by decide +kernel
  rw [correct, off] at value
  simp [singletonInput] at value

private theorem critical_subsets :
    ∀ x : Bit → Bool,
      (majority x = false → ∃ y : Bit → Bool,
        (List.ofFn y).count true = 2 ∧ ∀ i, x i ≤ y i) ∧
      (majority x = true → ∃ y : Bit → Bool,
        (List.ofFn y).count true = 3 ∧ ∀ i, y i ≤ x i) := by decide +kernel

/-- An output formula whose restrictions with two flags on and three flags on
    separate the two slices already needs a flag more than twice. -/
theorem noOutputForTwoAndThreeFlags {I : Type} [DecidableEq I] (f : Formula (Bit ⊕ I))
    (cap : ∀ i : Bit, reads f (.inl i) ≤ 2)
    (two : ∀ x : Bit → Bool, (List.ofFn x).count true = 2 →
      f.evalWith (Sum.elim x (fun _ => false)) = false)
    (three : ∀ x : Bit → Bool, (List.ofFn x).count true = 3 →
      f.evalWith (Sum.elim x (fun _ => false)) = true) : False := by
  let keep : Bit ⊕ I → Option Bit := Sum.elim some (fun _ => none)
  have leafValues (x : Bit → Bool) : assignment keep x = Sum.elim x (fun _ => false) := by
    funext a
    cases a <;> rfl
  cases eq : formulaRestrict f keep with
  | none =>
    let x (i : Bit) := decide (i.val < 3)
    have threeBits : (List.ofFn x).count true = 3 := by decide +kernel
    have value := formulaRestrict_eval f keep x
    rw [eq, formulaEval, leafValues, three x threeBits] at value
    contradiction
  | some g =>
    apply noReadTwiceMajority g
    · funext x
      cases hx : majority x with
      | false =>
        obtain ⟨y, count, above⟩ := (critical_subsets x).1 hx
        have bound := evalMono g above
        have value := formulaRestrict_eval f keep y
        rw [eq, formulaEval, leafValues, two y count] at value
        rw [value] at bound
        exact Bool.eq_false_of_le_false bound
      | true =>
        obtain ⟨y, count, inside⟩ := (critical_subsets x).2 hx
        have bound := evalMono g inside
        have value := formulaRestrict_eval f keep y
        rw [eq, formulaEval, leafValues, three y count] at value
        rw [value] at bound
        exact Bool.eq_true_of_true_le bound
    · intro i
      have retained := restrict_reads f keep i
      have weights : (fun a => ((keep a).map fun k => (singletonInput i k).toNat).getD 0) =
          fun a => (singletonInput (Sum.inl i) a).toNat := by
        funext a
        cases a <;> simp [keep, singletonInput]
      rw [eq, countReads, weights] at retained
      exact retained.trans (cap i)

end CrownMajorityFive
