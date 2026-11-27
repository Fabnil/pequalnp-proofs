import CrownFactorAnd
import CrownDropZero
import CrownOrStages

namespace CrownSeparateOr

open CrownForks CrownForest CrownForestCost CrownFactorAnd CrownOrStages PnpResearch
open CrownDropZero (formulaEval formulaLeaves)

variable {A I : Type}

private def join : Option (Formula A) → Option (Formula A) → Option (Formula A)
  | none, r => r
  | l, none => l
  | some l, some r => some (.disj l r)

private def optionalWeight : Option (Formula A) → (A → ℕ) → ℕ
  | none, _ => 0
  | some f, w => leafWeight f w

private theorem eval_join (l r : Option (Formula A)) (x : A → Bool) :
    formulaEval (join l r) x = (formulaEval l x || formulaEval r x) := by
  cases l <;> cases r <;> simp [join, formulaEval, Formula.evalWith]

private theorem leaves_join (l r : Option (Formula A)) :
    formulaLeaves (join l r) = formulaLeaves l + formulaLeaves r := by
  cases l <;> cases r <;> simp [join, formulaLeaves, formulaGates, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem weight_join (l r : Option (Formula A)) (w : A → ℕ) :
    optionalWeight (join l r) w = optionalWeight l w + optionalWeight r w := by
  cases l <;> cases r <;> simp [join, optionalWeight, leafWeight]

/-- Split the terms under the top-level OR into variable leaves and terms
    rooted at an AND, keeping each AND term intact. -/
def splitTop : Formula A → Option (Formula A) × Option (Formula A)
  | .var a => (some (.var a), none)
  | .conj l r => (none, some (.conj l r))
  | .disj l r =>
    let p := splitTop l
    let q := splitTop r
    (join p.1 q.1, join p.2 q.2)

theorem splitTop_eval (f : Formula A) (x : A → Bool) :
    (formulaEval (splitTop f).1 x || formulaEval (splitTop f).2 x) = f.evalWith x := by
  induction f with
  | var a => simp [splitTop, formulaEval, Formula.evalWith]
  | conj l r il ir => simp [splitTop, formulaEval]
  | disj l r il ir =>
    simp only [splitTop, eval_join, Formula.evalWith, ← il, ← ir]
    have reorder : ∀ a b c d : Bool, ((a || c) || (b || d)) = ((a || b) || (c || d)) := by decide
    exact reorder _ _ _ _

theorem splitTop_leaves (f : Formula A) :
    formulaLeaves (splitTop f).1 + formulaLeaves (splitTop f).2 = formulaGates f + 1 := by
  induction f with
  | var a => rfl
  | conj l r il ir => simp [splitTop, formulaLeaves]
  | disj l r il ir =>
    simp only [splitTop, leaves_join, formulaGates]
    omega

private theorem splitTop_weight (f : Formula A) (w : A → ℕ) :
    optionalWeight (splitTop f).1 w + optionalWeight (splitTop f).2 w = leafWeight f w := by
  induction f with
  | var a => simp [splitTop, optionalWeight, leafWeight]
  | conj l r il ir => simp [splitTop, optionalWeight]
  | disj l r il ir =>
    simp only [splitTop, weight_join, leafWeight]
    omega

private theorem splitTop_orOnly (f : Formula A) (p : Formula A) (left : (splitTop f).1 = some p) :
    orOnly p := by
  induction f generalizing p with
  | var a => simp [splitTop] at left; subst p; trivial
  | conj l r il ir => simp [splitTop] at left
  | disj l r il ir =>
    have form : join (splitTop l).1 (splitTop r).1 = some p := left
    cases hl : (splitTop l).1 with
    | none =>
      exact ir p (by simpa [hl, join] using form)
    | some l' =>
      cases hr : (splitTop r).1 with
      | none =>
        exact il p (by simpa [hl, hr, join] using form)
      | some r' =>
        have eq : Formula.disj l' r' = p := by simpa [hl, hr, join] using form
        subst p
        exact ⟨il l' hl, ir r' hr⟩

theorem splitTop_off (f : Formula A) (x : A → Bool) (off : andsOff f x) :
    formulaEval (splitTop f).2 x = false := by
  induction f with
  | var a => rfl
  | conj l r il ir => exact off.1
  | disj l r il ir =>
    change formulaEval (join (splitTop l).2 (splitTop r).2) x = false
    rw [eval_join, il off.1, ir off.2]
    rfl

def retime (p : Formula A) (terms : Option (Formula A)) (extra : ℕ)
    (rest : SharedFormula (Option A)) : SharedFormula A :=
  match terms with
  | none => .share p extra rest
  | some q => CrownMoveOr.moveOr p q extra rest

structure Preserves (s : Samples I A) (before after : SharedFormula A) : Prop where
  valid : after.Valid
  cost : gates after = gates before
  weight : ∀ w, after.weight w = before.weight w
  off : ∀ i, after.eval (s.one i) = false
  on : ∀ i j, i ≠ j → after.eval (s.two i j) = true

theorem Preserves.under (s : Samples I A) (f : Formula A) (extra : ℕ)
    {before after : SharedFormula (Option A)} (keeps : Preserves (s.add f) before after)
    (valid : (SharedFormula.share f extra before).Valid) :
    Preserves s (.share f extra before) (.share f extra after) := by
  refine ⟨⟨valid.1, keeps.valid, ?_⟩, ?_, ?_, keeps.off, keeps.on⟩
  · rw [keeps.weight]
    exact valid.2.2
  · simp only [gates, keeps.cost]
  · intro w
    change leafWeight f w + after.weight (withHead 0 w) =
      leafWeight f w + before.weight (withHead 0 w)
    rw [keeps.weight]

/-- Separate inactive top-level AND terms and move them to the output OR.
    The head that remains is a formula of OR gates and leaves. -/
theorem movePassiveAnds (s : Samples I A) (f : Formula A) (extra : ℕ)
    (rest : SharedFormula (Option A))
    (passive : ∀ i, formulaEval (splitTop f).2 (s.one i) = false)
    (active : ∃ i, f.evalWith (s.one i) = true)
    (valid : (SharedFormula.share f extra rest).Valid)
    (off : ∀ i, (SharedFormula.share f extra rest).eval (s.one i) = false)
    (on : ∀ i j, i ≠ j → (SharedFormula.share f extra rest).eval (s.two i j) = true) :
    ∃ p q, orOnly p ∧ Preserves s (.share f extra rest) (retime p q extra rest) := by
  cases hp : (splitTop f).1 with
  | none =>
    obtain ⟨i, yes⟩ := active
    have eq := splitTop_eval f (s.one i)
    rw [hp, formulaEval, passive i, yes] at eq
    contradiction
  | some p =>
    have pure := splitTop_orOnly f p hp
    cases hq : (splitTop f).2 with
    | none =>
      have eval (x : A → Bool) : p.evalWith x = f.evalWith x := by
        simpa only [hp, hq, formulaEval, Bool.or_false] using splitTop_eval f x
      have same : formulaGates p = formulaGates f := by
        have counts := splitTop_leaves f
        simp only [hp, hq, formulaLeaves] at counts
        omega
      have weight (w : A → ℕ) : leafWeight p w = leafWeight f w := by
        simpa only [hp, hq, optionalWeight, Nat.add_zero] using splitTop_weight f w
      refine ⟨p, none, pure, ⟨valid, by simp only [retime, gates, same], ?_, ?_, ?_⟩⟩
      · intro w
        simp only [retime, SharedFormula.weight, weight]
      · intro i
        simpa only [retime, SharedFormula.eval, eval] using off i
      · intro i j ne
        simpa only [retime, SharedFormula.eval, eval] using on i j ne
    | some q =>
      have eval (x : A → Bool) : (Formula.disj p q).evalWith x = f.evalWith x := by
        simpa only [hp, hq, formulaEval, Formula.evalWith] using splitTop_eval f x
      have same : formulaGates (.disj p q) = formulaGates f := by
        have counts := splitTop_leaves f
        simp only [hp, hq, formulaLeaves] at counts
        simp only [formulaGates]
        omega
      have weight (w : A → ℕ) : leafWeight (Formula.disj p q) w = leafWeight f w := by
        simpa only [hp, hq, optionalWeight, leafWeight] using splitTop_weight f w
      have idle (i : I) : q.evalWith (s.one i) = false := by
        simpa only [hq, formulaEval] using passive i
      have tests := CrownMoveOr.moveOr_samples s p q extra rest idle
        (fun i => by simpa only [SharedFormula.eval, eval] using off i)
        (fun i j ne => by simpa only [SharedFormula.eval, eval] using on i j ne)
      refine ⟨p, some q, pure, ⟨CrownMoveOr.moveOr_valid p q extra rest valid, ?_, ?_,
        tests.1, tests.2⟩⟩
      · simp only [retime, CrownMoveOr.moveOr_gates, gates, same]
      · intro w
        simp only [retime, CrownMoveOr.moveOr_weight, SharedFormula.weight, weight]

end CrownSeparateOr
