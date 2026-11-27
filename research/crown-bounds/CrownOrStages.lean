import CrownFourProfiles

namespace CrownOrStages

open CrownForks CrownForest CrownProfiles CrownVisibility PnpResearch

variable {A I : Type}

def orOnly : Formula A → Prop
  | .var _ => True
  | .conj _ _ => False
  | .disj l r => orOnly l ∧ orOnly r

def orPrefix {A : Type} : SharedFormula A → ℕ → Prop
  | _, 0 => True
  | .tree _, _ + 1 => False
  | .share f _ rest, k + 1 => orOnly f ∧ orPrefix rest k

/-- A Boolean function which is true exactly when one of its accepted
    singleton inputs is present. -/
def singletonDisjunction [DecidableEq I] (F : (I → Bool) → Bool) : Prop :=
  ∀ x, F x = true ↔ ∃ i, x i = true ∧ F (singletonInput i) = true

variable [DecidableEq I]

theorem projection (i : I) : singletonDisjunction (fun x => x i) := by
  intro x
  constructor
  · intro on
    exact ⟨i, on, by simp [singletonInput]⟩
  · rintro ⟨j, hj, eq⟩
    have same : i = j := by simpa [singletonInput] using eq
    exact same.symm ▸ hj

theorem disj (F G : (I → Bool) → Bool) (left : singletonDisjunction F)
    (right : singletonDisjunction G) : singletonDisjunction (fun x => F x || G x) := by
  intro x
  simp only [Bool.or_eq_true, left x, right x]
  constructor
  · rintro (⟨i, on, h⟩ | ⟨i, on, h⟩)
    · exact ⟨i, on, Or.inl h⟩
    · exact ⟨i, on, Or.inr h⟩
  · rintro ⟨i, on, h | h⟩
    · exact Or.inl ⟨i, on, h⟩
    · exact Or.inr ⟨i, on, h⟩

theorem eval_orOnly (f : Formula A) (val : (I → Bool) → A → Bool)
    (shape : orOnly f) (atoms : ∀ a, singletonDisjunction (fun x => val x a)) :
    singletonDisjunction (fun x => f.evalWith (val x)) := by
  induction f with
  | var a => exact atoms a
  | conj l r il ir => exact False.elim shape
  | disj l r il ir => exact disj _ _ (il shape.1) (ir shape.2)

theorem orStage (E : SharedFormula A) (n : ℕ) (shape : orPrefix E n)
    (val : (I → Bool) → A → Bool) (atoms : ∀ a, singletonDisjunction (fun x => val x a))
    (k : ℕ) (inside : k < n) :
    singletonDisjunction (fun x => bitAt (profile E (val x)) k) := by
  induction E generalizing n k with
  | tree f =>
    cases n with
    | zero => omega
    | succ n => exact False.elim shape
  | share f u rest ih =>
    cases n with
    | zero => omega
    | succ n =>
      have head := eval_orOnly f val shape.1 atoms
      cases k with
      | zero => exact head
      | succ k =>
        let extended (x : I → Bool) := withHead (f.evalWith (val x)) (val x)
        have facts (a : Option _) : singletonDisjunction (fun x => extended x a) := by
          cases a with
          | none => exact head
          | some a => exact atoms a
        exact ih n shape.2 extended facts k (by omega)

theorem implies_of_singletons {F G : (I → Bool) → Bool} (left : singletonDisjunction F)
    (right : singletonDisjunction G) (le : ∀ i, F (singletonInput i) ≤ G (singletonInput i))
    (x : I → Bool) : F x ≤ G x := by
  apply Bool.le_iff_imp.mpr
  intro accept
  obtain ⟨i, on, fin⟩ := (left x).mp accept
  exact (right x).mpr ⟨i, on, (Bool.le_iff_imp.mp (le i)) fin⟩

theorem pair_eq {F : (I → Bool) → Bool} (supports : singletonDisjunction F) (i j : I) :
    F (pairInput i j) = (F (singletonInput i) || F (singletonInput j)) := by
  apply Bool.le_antisymm
  · apply Bool.le_iff_imp.mpr
    intro accept
    obtain ⟨k, present, on⟩ := (supports _).mp accept
    have hk : k = i ∨ k = j := by
      simpa [pairInput, singletonInput, Bool.or_eq_true] using present
    rcases hk with rfl | rfl <;> simp [on]
  · apply Bool.le_iff_imp.mpr
    intro accept
    rw [Bool.or_eq_true] at accept
    rcases accept with fi | fj
    · exact (supports _).mpr ⟨i, by simp [pairInput, singletonInput], fi⟩
    · exact (supports _).mpr ⟨j, by simp [pairInput, singletonInput], fj⟩

theorem orStage_pair (E : SharedFormula I) (n : ℕ) (shape : orPrefix E n) (k : ℕ) (inside : k < n)
    (i j : I) :
    bitAt (profile E (pairInput i j)) k =
      (bitAt (profile E (singletonInput i)) k || bitAt (profile E (singletonInput j)) k) :=
  pair_eq (orStage E n shape (fun x a => x a) projection k inside) i j

end CrownOrStages
