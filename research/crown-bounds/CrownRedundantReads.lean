import CrownDropZero
import CrownPairFormula

namespace CrownRedundantReads

open CrownForks CrownForest CrownForestCost CrownDropZero CrownPairFormula PnpResearch
open CrownProfileThree.Network (ones)

variable {A J : Type} [DecidableEq A]

theorem evalMonoOnReads (f : Formula A) {x y : A → Bool}
    (le : ∀ a, 0 < reads f a → x a ≤ y a) : f.evalWith x ≤ f.evalWith y := by
  induction f with
  | var a => exact le a (by simp [reads, leafWeight, singletonInput])
  | conj l r il ir | disj l r il ir =>
    have left := il fun a used => le a (by change 0 < reads l a + reads r a; omega)
    have right := ir fun a used => le a (by change 0 < reads l a + reads r a; omega)
    first
    | exact Bool.le_and (le_trans (Bool.and_le_left _ _) left) (le_trans (Bool.and_le_right _ _) right)
    | exact Bool.or_le (le_trans left (Bool.left_le_or _ _)) (le_trans right (Bool.right_le_or _ _))

/-- If each live reading of `p` has a dominating explanation with `p` off,
    one can remove every occurrence of `p` and save a gate. -/
theorem cheaper_of_cover (f : Formula A) (p : A) (value : J → A → Bool)
    (used : 0 < reads f p) (live : ∃ q, f.evalWith (value q) = true)
    (cover : ∀ q, value q p = true → ∃ r, value r p = false ∧ f.evalWith (value r) = true ∧
      ∀ a, a ≠ p → 0 < reads f a → value r a ≤ value q a) :
    ∃ g : Formula A, formulaGates g < formulaGates f ∧ ∀ q, g.evalWith (value q) = f.evalWith (value q) := by
  let keep (a : A) : Option A := if a = p then none else some a
  have agrees (q : J) : f.evalWith (assignment keep (value q)) = f.evalWith (value q) := by
    apply le_antisymm
    · apply evalMono f
      intro a
      by_cases eq : a = p <;> simp [assignment, keep, eq]
    · apply Bool.le_iff_imp.mpr
      intro accepts
      cases bit : value q p with
      | false =>
        have unchanged : assignment keep (value q) = value q := by
          funext a
          by_cases eq : a = p <;> simp [assignment, keep, eq, bit]
        rwa [unchanged]
      | true =>
        obtain ⟨r, off, on, dominates⟩ := cover q bit
        apply Bool.le_iff_imp.mp (evalMonoOnReads f ?_) on
        intro a readsA
        by_cases eq : a = p
        · simp [assignment, keep, eq, off]
        · simpa [assignment, keep, eq] using dominates a eq readsA
  have mass : missing keep = ones p := by
    funext a
    by_cases eq : a = p <;> simp [missing, keep, ones, singletonInput, eq]
  have size := formulaRestrict_leaves f keep
  rw [mass] at size
  obtain ⟨q, on⟩ := live
  cases result : formulaRestrict f keep with
  | none =>
    have same := (formulaRestrict_eval f keep (value q)).trans (agrees q)
    simp [result, formulaEval, on] at same
  | some g =>
    simp only [result, formulaLeaves] at size
    change 0 < leafWeight f (ones p) at used
    refine ⟨g, by omega, fun r => ?_⟩
    simpa only [result, formulaEval] using (formulaRestrict_eval f keep (value r)).trans (agrees r)

/-- An AND/OR formula over pointwise ordered arguments selects one of its
    leaves on the entire domain. -/
theorem selects_leaf_of_chain (f : Formula A) (value : J → A → Bool)
    (chain : ∀ a b, 0 < reads f a → 0 < reads f b →
      (∀ x, value x a ≤ value x b) ∨ (∀ x, value x b ≤ value x a)) :
    ∃ a, 0 < reads f a ∧ ∀ x, f.evalWith (value x) = value x a := by
  have smaller_and {a b : Bool} (le : a ≤ b) : (a && b) = a :=
    Bool.le_antisymm (Bool.and_le_left _ _) (Bool.le_and le_rfl le)
  have larger_or {a b : Bool} (le : a ≤ b) : (a || b) = b :=
    Bool.le_antisymm (Bool.or_le le le_rfl) (Bool.right_le_or _ _)
  induction f with
  | var a => exact ⟨a, by simp [reads, leafWeight, singletonInput], fun _ => rfl⟩
  | conj l r il ir | disj l r il ir =>
    obtain ⟨a, useA, evalA⟩ := il fun s t hs ht => chain s t
      (by change 0 < reads l s + reads r s; omega) (by change 0 < reads l t + reads r t; omega)
    obtain ⟨b, useB, evalB⟩ := ir fun s t hs ht => chain s t
      (by change 0 < reads l s + reads r s; omega) (by change 0 < reads l t + reads r t; omega)
    have comparisons := chain a b
      (by change 0 < reads l a + reads r a; omega) (by change 0 < reads l b + reads r b; omega)
    rcases comparisons with ab | ba
    · first
      | exact ⟨a, by change 0 < reads l a + reads r a; omega,
          fun x => by simpa only [Formula.evalWith, evalA, evalB] using smaller_and (ab x)⟩
      | exact ⟨b, by change 0 < reads l b + reads r b; omega,
          fun x => by simpa only [Formula.evalWith, evalA, evalB] using larger_or (ab x)⟩
    · first
      | exact ⟨b, by change 0 < reads l b + reads r b; omega, fun x => by
          simpa only [Formula.evalWith, evalA, evalB, Bool.and_comm] using smaller_and (ba x)⟩
      | exact ⟨a, by change 0 < reads l a + reads r a; omega, fun x => by
          simpa only [Formula.evalWith, evalA, evalB, Bool.or_comm] using larger_or (ba x)⟩

end CrownRedundantReads
