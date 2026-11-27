import CrownFactorAnd

namespace CrownReadSupport

open CrownForks CrownForestCost CrownFactorAnd PnpResearch

variable {A J : Type}

/-- A formula reads a key when its copy alone contributes to every assignment
    of nonnegative leaf weights. -/
def Uses (f : Formula A) (a : A) : Prop := ∀ w, w a ≤ leafWeight f w

private def attach {P : A → Prop} : (f : Formula A) →
    (∀ a, Uses f a → P a) → Formula {a // P a}
  | .var a, tags => .var ⟨a, tags a (fun _ => le_rfl)⟩
  | .conj l r, tags => .conj (attach l fun a read => tags a fun w => (read w).trans (Nat.le_add_right ..))
      (attach r fun a read => tags a fun w => (read w).trans (Nat.le_add_left ..))
  | .disj l r, tags => .disj (attach l fun a read => tags a fun w => (read w).trans (Nat.le_add_right ..))
      (attach r fun a read => tags a fun w => (read w).trans (Nat.le_add_left ..))

private theorem detach {P : A → Prop} (f : Formula A) (tags : ∀ a, Uses f a → P a) :
    rename (attach f tags) Subtype.val = f := by
  induction f <;> simp [attach, rename, *]

private theorem rename_cost {A B : Type} (f : Formula A) (map : A → B) :
    formulaGates (rename f map) = formulaGates f := by
  induction f <;> simp [rename, formulaGates, *]

private theorem rename_andsOff {A B : Type} (f : Formula A) (map : A → B) (x : B → Bool) :
    andsOff (rename f map) x ↔ andsOff f (x ∘ map) := by
  induction f <;> simp [rename, andsOff, Formula.evalWith, eval_rename, *]

/-- Argument comparability is only required for pairs of keys that the
    formula actually reads. -/
theorem normalizeUsed (val : J → A → Bool) (sample : J → Prop) (f : Formula A)
    (compare : ∀ t, sample t → ∀ a b, Uses f a → Uses f b → val t a = true → val t b = true →
      (∀ q, val q a ≤ val q b) ∨ (∀ q, val q b ≤ val q a)) :
    ∃ g : Formula A, (∀ q, g.evalWith (val q) = f.evalWith (val q)) ∧
      (formulaGates g < formulaGates f ∨
        (formulaGates g = formulaGates f ∧ (∀ w, leafWeight g w = leafWeight f w) ∧
          ∀ t, sample t → andsOff g (val t))) := by
  let tagged := attach f (P := Uses f) (fun _ => id)
  let restrict (x : J) : {a // Uses f a} → Bool := val x ∘ Subtype.val
  have forget : rename tagged Subtype.val = f := detach f _
  have sameCost : formulaGates tagged = formulaGates f := by
    rw [← rename_cost tagged Subtype.val, forget]
  obtain ⟨g, correct, size⟩ := normalize restrict sample
    (fun t ht a b => compare t ht a.val b.val a.property b.property) tagged
  refine ⟨rename g Subtype.val, ?_, ?_⟩
  · intro x
    rw [eval_rename]
    change g.evalWith (restrict x) = _
    rw [correct x, ← eval_rename, forget]
  · rw [rename_cost, ← sameCost]
    rcases size with smaller | ⟨equal, weight, off⟩
    · exact Or.inl smaller
    · refine Or.inr ⟨equal, ?_, ?_⟩
      · intro w
        rw [weight_rename, weight, ← weight_rename, forget]
      · intro t ht
        exact (rename_andsOff g Subtype.val (val t)).mpr (off t ht)

end CrownReadSupport
