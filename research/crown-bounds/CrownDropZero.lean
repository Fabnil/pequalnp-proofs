import CrownMoveOr

namespace CrownDropZero

open CrownForks CrownForest CrownSharedCuts CrownForestCost CrownMoveOr PnpResearch

variable {A B : Type}

/-- An absent image in the substitution sets the old variable to zero. -/
def assignment (keep : A → Option B) (x : B → Bool) (a : A) : Bool :=
  ((keep a).map x).getD false

def missing (keep : A → Option B) (a : A) : ℕ :=
  (keep a).isNone.toNat

def keepHead (keep : A → Option B) : Option A → Option (Option B) :=
  withHead (some none) (fun a => (keep a).map some)

def formulaRestrict : Formula A → (A → Option B) → Option (Formula B)
  | .var a, keep => (keep a).map Formula.var
  | .conj l r, keep => (formulaRestrict l keep).bind fun l' =>
      (formulaRestrict r keep).map (Formula.conj l')
  | .disj l r, keep =>
    match formulaRestrict l keep, formulaRestrict r keep with
    | none, t => t
    | t, none => t
    | some l', some r' => some (.disj l' r')

def formulaEval (f : Option (Formula B)) (x : B → Bool) : Bool :=
  match f with
  | none => false
  | some f => f.evalWith x

def formulaLeaves (f : Option (Formula B)) : ℕ :=
  match f with
  | none => 0
  | some f => formulaGates f + 1

theorem formulaRestrict_eval (f : Formula A) (keep : A → Option B) (x : B → Bool) :
    formulaEval (formulaRestrict f keep) x = f.evalWith (assignment keep x) := by
  induction f with
  | var a => cases h : keep a <;> simp [formulaRestrict, h, formulaEval, Formula.evalWith, assignment]
  | conj l r il ir | disj l r il ir =>
    rw [Formula.evalWith, ← il, ← ir]
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [formulaRestrict, hl, hr, formulaEval, Formula.evalWith]

theorem formulaRestrict_leaves (f : Formula A) (keep : A → Option B) :
    formulaLeaves (formulaRestrict f keep) + leafWeight f (missing keep) ≤ formulaGates f + 1 := by
  induction f with
  | var a =>
    cases h : keep a <;> simp [formulaRestrict, h, formulaLeaves, missing, leafWeight, formulaGates]
  | conj l r il ir | disj l r il ir =>
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [formulaRestrict, hl, hr, formulaLeaves, formulaGates, leafWeight] at * <;> omega

/-- Restrict a forest, omitting each shared formula that becomes zero. -/
def restrict {A B : Type} : SharedFormula A → (A → Option B) → Option (SharedFormula B)
  | .tree f, keep => (formulaRestrict f keep).map SharedFormula.tree
  | .share f extra rest, keep =>
    match formulaRestrict f keep with
    | none => restrict rest (withHead none keep)
    | some g => (restrict rest (keepHead keep)).map (SharedFormula.share g extra)

def forestEval (E : Option (SharedFormula B)) (x : B → Bool) : Bool :=
  match E with
  | none => false
  | some E => E.eval x

def forestCost (E : Option (SharedFormula B)) : ℕ :=
  match E with
  | none => 0
  | some E => gates E + 1

private theorem assignment_drop (keep : A → Option B) (x : B → Bool) :
    assignment (withHead none keep) x = withHead false (assignment keep x) := by
  funext a
  cases a <;> rfl

private theorem assignment_lift (keep : A → Option B) (x : B → Bool) (bit : Bool) :
    assignment (keepHead keep) (withHead bit x) = withHead bit (assignment keep x) := by
  funext a
  cases a with
  | none => rfl
  | some a => cases h : keep a <;> simp [assignment, keepHead, h]

theorem restrict_eval (E : SharedFormula A) (keep : A → Option B) (x : B → Bool) :
    forestEval (restrict E keep) x = E.eval (assignment keep x) := by
  induction E generalizing B with
  | tree f =>
    have main := formulaRestrict_eval f keep x
    cases h : formulaRestrict f keep <;>
      simpa [restrict, h, forestEval, formulaEval, SharedFormula.eval] using main
  | share f extra rest ih =>
    have main := formulaRestrict_eval f keep x
    cases h : formulaRestrict f keep with
    | none =>
      have head : f.evalWith (assignment keep x) = false := by
        simpa [h, formulaEval] using main.symm
      simpa only [restrict, h, assignment_drop, SharedFormula.eval, head]
        using ih (withHead none keep) x
    | some g =>
      have head : f.evalWith (assignment keep x) = g.evalWith x := by
        simpa [h, formulaEval] using main.symm
      have tail := ih (keepHead keep) (withHead (g.evalWith x) x)
      cases ht : restrict rest (keepHead keep) <;>
        simpa [restrict, h, ht, forestEval, assignment_lift, SharedFormula.eval, head] using tail

private theorem missing_drop (keep : A → Option B) :
    missing (withHead none keep) = fun a =>
      withHead 0 (missing keep) a + withHead 1 (fun _ => 0) a := by
  funext a
  cases a <;> simp [missing]

private theorem missing_lift (keep : A → Option B) :
    missing (keepHead keep) = withHead 0 (missing keep) := by
  funext a
  cases a with
  | none => rfl
  | some a => cases h : keep a <;> simp [keepHead, missing, h]

/-- Every reference to a deleted argument saves one gate when the output
    survives. If the output vanishes, its last leaf also counts. -/
theorem restrict_cost (E : SharedFormula A) (valid : E.Valid) (keep : A → Option B) :
    forestCost (restrict E keep) + E.weight (missing keep) ≤ gates E + 1 := by
  induction E generalizing B with
  | tree f =>
    have main := formulaRestrict_leaves f keep
    cases h : formulaRestrict f keep <;>
      simpa [restrict, h, forestCost, formulaLeaves, gates, SharedFormula.weight] using main
  | share f extra rest ih =>
    have main := formulaRestrict_leaves f keep
    cases h : formulaRestrict f keep with
    | none =>
      have tail := ih valid.2.1 (withHead none keep)
      rw [missing_drop, weightAdd, valid.2.2] at tail
      simp only [h, formulaLeaves] at main
      simp only [restrict, h, SharedFormula.weight, gates]
      omega
    | some g =>
      have tail := ih valid.2.1 (keepHead keep)
      rw [missing_lift] at tail
      simp only [h, formulaLeaves] at main
      cases ht : restrict rest (keepHead keep) <;>
        simp only [restrict, h, ht, forestCost, Option.map_some, Option.map_none,
          SharedFormula.weight, gates] at * <;> omega

def moveShared (f : Formula A) (rest : SharedFormula (Option A)) : SharedFormula A :=
  match restrict rest (withHead none some) with
  | none => .tree f
  | some reduced => appendOr reduced f

theorem moveShared_eval (f : Formula A) (rest : SharedFormula (Option A)) (x : A → Bool) :
    (moveShared f rest).eval x = (rest.eval (withHead false x) || f.evalWith x) := by
  have h := restrict_eval rest (withHead none some) x
  have sub : assignment (withHead none (some : A → Option A)) x = withHead false x := by
    funext a
    cases a <;> rfl
  rw [sub] at h
  rw [← h]
  cases ht : restrict rest (withHead none some) <;>
    simp [moveShared, ht, forestEval, SharedFormula.eval, appendOr_eval]

theorem moveShared_gates (f : Formula A) (extra : ℕ) (rest : SharedFormula (Option A))
    (valid : (SharedFormula.share f extra rest).Valid) :
    gates (moveShared f rest) < gates (.share f extra rest) := by
  have h := restrict_cost rest valid.2.1 (withHead none some)
  have sub : missing (withHead none (some : A → Option A)) = withHead 1 (fun _ => 0) := by
    funext a
    cases a <;> rfl
  rw [sub, valid.2.2] at h
  have positive := valid.1
  cases ht : restrict rest (withHead none some) <;>
    simp only [moveShared, ht, forestCost, appendOr_gates, gates] at h ⊢ <;> omega

theorem moveShared_samples {I : Type} (s : Samples I A) (f : Formula A) (extra : ℕ)
    (rest : SharedFormula (Option A)) (passive : ∀ i, f.evalWith (s.one i) = false)
    (off : ∀ i, (SharedFormula.share f extra rest).eval (s.one i) = false)
    (on : ∀ i j, i ≠ j → (SharedFormula.share f extra rest).eval (s.two i j) = true) :
    (∀ i, (moveShared f rest).eval (s.one i) = false) ∧
    ∀ i j, i ≠ j → (moveShared f rest).eval (s.two i j) = true := by
  constructor
  · intro i
    simpa only [moveShared_eval, passive i, Bool.or_false, SharedFormula.eval] using off i
  · intro i j ne
    cases h : f.evalWith (s.two i j) with
    | false => simpa only [moveShared_eval, h, Bool.or_false, SharedFormula.eval] using on i j ne
    | true => rw [moveShared_eval, h, Bool.or_true]

/-- Every shared formula is on for some singleton sample in its own context. -/
def allActive {I A : Type} : SharedFormula A → Samples I A → Prop
  | .tree _, _ => True
  | .share f _ rest, s => (∃ i, f.evalWith (s.one i) = true) ∧ allActive rest (s.add f)

theorem activeOrCheaper {I : Type} (E : SharedFormula A) (s : Samples I A) (valid : E.Valid)
    (off : ∀ i, E.eval (s.one i) = false)
    (on : ∀ i j, i ≠ j → E.eval (s.two i j) = true) :
    allActive E s ∨ ∃ F : SharedFormula A, gates F < gates E ∧
      (∀ i, F.eval (s.one i) = false) ∧ (∀ i j, i ≠ j → F.eval (s.two i j) = true) := by
  classical
  induction E with
  | tree f => exact Or.inl trivial
  | share f extra rest ih =>
    by_cases active : ∃ i, f.evalWith (s.one i) = true
    · rcases ih (s.add f) valid.2.1 off on with every | ⟨F, lower, off', on'⟩
      · exact Or.inl ⟨active, every⟩
      · exact Or.inr ⟨.share f extra F, Nat.add_lt_add_left lower _, off', on'⟩
    · have passive (i : I) : f.evalWith (s.one i) = false :=
        Bool.eq_false_of_not_eq_true fun h => active ⟨i, h⟩
      exact Or.inr ⟨moveShared f rest, moveShared_gates f extra rest valid,
        moveShared_samples s f extra rest passive off on⟩

theorem tenAllActive (E : SharedFormula (Fin 10)) (valid : E.Valid) (test : ThresholdOn E.eval)
    (cost : gates E ≤ 23) : allActive E (Samples.raw (Fin 10)) := by
  rcases activeOrCheaper E (Samples.raw (Fin 10)) valid test.1 test.2 with every | ⟨F, less, tf⟩
  · exact every
  · have floor := tenRequires23 F tf
    omega

end CrownDropZero
