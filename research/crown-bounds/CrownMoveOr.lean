import CrownForestCost

namespace CrownMoveOr

open CrownForks CrownForest CrownForestCost PnpResearch

/-- Disjoin a formula in the available arguments with the eventual output. -/
def appendOr {A : Type} : SharedFormula A → Formula A → SharedFormula A
  | .tree g, f => .tree (.disj g f)
  | .share g extra rest, f => .share g extra (appendOr rest (rename f some))

theorem appendOr_eval {A : Type} (E : SharedFormula A) (f : Formula A) (x : A → Bool) :
    (appendOr E f).eval x = (E.eval x || f.evalWith x) := by
  induction E with
  | tree g => rfl
  | share g extra rest ih =>
    simp only [appendOr, SharedFormula.eval, ih, eval_rename]
    rfl

private theorem gates_rename {A B : Type} (f : Formula A) (map : A → B) :
    formulaGates (rename f map) = formulaGates f := by
  induction f <;> simp_all [rename, formulaGates]

theorem appendOr_gates {A : Type} (E : SharedFormula A) (f : Formula A) :
    gates (appendOr E f) = gates E + formulaGates f + 1 := by
  induction E with
  | tree g => rfl
  | share g extra rest ih =>
    simp only [appendOr, gates, ih, gates_rename]
    omega

theorem appendOr_weight {A : Type} (E : SharedFormula A) (f : Formula A) (w : A → ℕ) :
    (appendOr E f).weight w = E.weight w + leafWeight f w := by
  induction E with
  | tree g => rfl
  | share g extra rest ih =>
    have old : withHead 0 w ∘ some = w := rfl
    simp only [appendOr, SharedFormula.weight, ih, weight_rename, old]
    omega

theorem appendOr_extra {A : Type} (E : SharedFormula A) (f : Formula A) :
    (appendOr E f).extraUses = E.extraUses := by
  induction E with
  | tree g => rfl
  | share g extra rest ih => simp only [appendOr, SharedFormula.extraUses, ih]

private theorem zeroWeight {A : Type} (f : Formula A) :
    leafWeight f (fun _ => 0) = 0 := by
  simpa [stock] using stock_zero [f]

theorem appendOr_valid {A : Type} (E : SharedFormula A) (f : Formula A) (valid : E.Valid) :
    (appendOr E f).Valid := by
  induction E with
  | tree g => trivial
  | share g extra rest ih =>
    refine ⟨valid.1, ih (rename f some) valid.2.1, ?_⟩
    rw [appendOr_weight, valid.2.2, weight_rename]
    change extra + 1 + leafWeight f (fun _ => 0) = extra + 1
    rw [zeroWeight, Nat.add_zero]

def moveOr {A : Type} (p q : Formula A) (extra : ℕ) (rest : SharedFormula (Option A)) :
    SharedFormula A :=
  .share p extra (appendOr rest (rename q some))

theorem moveOr_eval {A : Type} (p q : Formula A) (extra : ℕ) (rest : SharedFormula (Option A))
    (x : A → Bool) :
    (moveOr p q extra rest).eval x =
      (rest.eval (withHead (p.evalWith x) x) || q.evalWith x) := by
  simp only [moveOr, SharedFormula.eval, appendOr_eval, eval_rename]
  rfl

/-- Moving a disjunct that is false on singleton samples preserves the tests. -/
theorem moveOr_samples {I A : Type} (s : Samples I A) (p q : Formula A) (extra : ℕ)
    (rest : SharedFormula (Option A)) (passive : ∀ i, q.evalWith (s.one i) = false)
    (off : ∀ i, (SharedFormula.share (.disj p q) extra rest).eval (s.one i) = false)
    (on : ∀ i j, i ≠ j → (SharedFormula.share (.disj p q) extra rest).eval (s.two i j) = true) :
    (∀ i, (moveOr p q extra rest).eval (s.one i) = false) ∧
    ∀ i j, i ≠ j → (moveOr p q extra rest).eval (s.two i j) = true := by
  constructor
  · intro i
    simpa only [moveOr_eval, passive i, Bool.or_false, SharedFormula.eval, Formula.evalWith]
      using off i
  · intro i j ne
    cases h : q.evalWith (s.two i j) with
    | false =>
      simpa only [moveOr_eval, h, Bool.or_false, SharedFormula.eval, Formula.evalWith]
        using on i j ne
    | true =>
      rw [moveOr_eval, h, Bool.or_true]

theorem moveOr_gates {A : Type} (p q : Formula A) (extra : ℕ) (rest : SharedFormula (Option A)) :
    gates (moveOr p q extra rest) = gates (.share (.disj p q) extra rest) := by
  simp only [moveOr, gates, appendOr_gates, gates_rename, formulaGates]
  omega

theorem moveOr_weight {A : Type} (p q : Formula A) (extra : ℕ) (rest : SharedFormula (Option A))
    (w : A → ℕ) :
    (moveOr p q extra rest).weight w = (SharedFormula.share (.disj p q) extra rest).weight w := by
  have old : withHead 0 w ∘ some = w := rfl
  simp only [moveOr, SharedFormula.weight, appendOr_weight, weight_rename, old, leafWeight]
  omega

theorem moveOr_valid {A : Type} (p q : Formula A) (extra : ℕ) (rest : SharedFormula (Option A))
    (valid : (SharedFormula.share (.disj p q) extra rest).Valid) :
    (moveOr p q extra rest).Valid := by
  refine ⟨valid.1, appendOr_valid rest _ valid.2.1, ?_⟩
  rw [appendOr_weight, valid.2.2, weight_rename]
  change extra + 1 + leafWeight q (fun _ => 0) = extra + 1
  rw [zeroWeight, Nat.add_zero]

end CrownMoveOr
