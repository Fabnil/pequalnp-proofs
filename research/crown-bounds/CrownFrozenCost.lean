import CrownProfiles
import CrownForestCost
import CrownLower

namespace CrownFrozenCost

open CrownForks CrownForest CrownProfiles CrownForestCost PnpResearch
open CrownRun (var)

variable {A B : Type}

def symbolWeight : Sum Bool B → ℕ
  | .inl _ => 0
  | .inr _ => 1

def assign (subst : A → Sum Bool B) (x : B → Bool) (a : A) : Bool :=
  (subst a).elim id x

private def combine (meet : Bool) (left right : Sum Bool (Formula B)) : Sum Bool (Formula B) :=
  match left, right with
  | .inl b, r => if b = meet then r else .inl b
  | l, .inl b => if b = meet then l else .inl b
  | .inr p, .inr q => .inr (if meet then .conj p q else .disj p q)

private def foldFormula : Formula A → (A → Sum Bool B) → Sum Bool (Formula B)
  | .var a, subst => (subst a).map id Formula.var
  | .conj l r, subst => combine true (foldFormula l subst) (foldFormula r subst)
  | .disj l r, subst => combine false (foldFormula l subst) (foldFormula r subst)

private def formulaValue (f : Sum Bool (Formula B)) (x : B → Bool) : Bool :=
  f.elim id (fun p => p.evalWith x)

private def formulaMass : Sum Bool (Formula B) → ℕ
  | .inl _ => 0
  | .inr f => formulaGates f + 1

private theorem combine_eval (meet : Bool) (l r : Sum Bool (Formula B)) (x : B → Bool) :
    formulaValue (combine meet l r) x =
      if meet then formulaValue l x && formulaValue r x else formulaValue l x || formulaValue r x := by
  rcases l with a | f
  · cases a <;> cases meet <;> simp [combine, formulaValue]
  · rcases r with b | g
    · cases b <;> cases meet <;> simp [combine, formulaValue]
    · cases meet <;> rfl

private theorem combine_mass (meet : Bool) (l r : Sum Bool (Formula B)) :
    formulaMass (combine meet l r) ≤ formulaMass l + formulaMass r := by
  rcases l with a | f
  · cases a <;> cases meet <;> simp [combine, formulaMass]
  · rcases r with b | g
    · cases b <;> cases meet <;> simp [combine, formulaMass]
    · cases meet <;> simp [combine, formulaMass, formulaGates] <;> omega

private theorem foldFormula_eval (f : Formula A) (subst : A → Sum Bool B) (x : B → Bool) :
    formulaValue (foldFormula f subst) x = f.evalWith (assign subst x) := by
  induction f with
  | var a => cases h : subst a <;> simp [foldFormula, formulaValue, assign, Formula.evalWith, h]
  | conj l r il ir | disj l r il ir => simp [foldFormula, combine_eval, Formula.evalWith, il, ir]

private theorem foldFormula_mass (f : Formula A) (subst : A → Sum Bool B) :
    formulaMass (foldFormula f subst) ≤ leafWeight f (symbolWeight ∘ subst) := by
  induction f with
  | var a => cases h : subst a <;> simp [foldFormula, formulaMass, formulaGates, leafWeight, symbolWeight, h]
  | conj l r il ir | disj l r il ir =>
    exact (combine_mass _ _ _).trans (Nat.add_le_add il ir)

private def extend (subst : A → Sum Bool B) : Option A → Sum Bool (Option B) :=
  withHead (.inr none) (fun a => (subst a).map id some)

private theorem assign_fixed (b : Bool) (subst : A → Sum Bool B) (x : B → Bool) :
    assign (withHead (.inl b) subst) x = withHead b (assign subst x) := by
  funext a
  cases a <;> rfl

private theorem assign_extend (b : Bool) (subst : A → Sum Bool B) (x : B → Bool) :
    assign (extend subst) (withHead b x) = withHead b (assign subst x) := by
  funext a
  cases a with
  | none => rfl
  | some a => cases h : subst a <;> simp [extend, assign, withHead, h]

/-- Remove a stage when its prescribed or simplified value is constant. -/
def fold {A B : Type} : SharedFormula A → List (Option Bool) → (A → Sum Bool B) → Sum Bool (SharedFormula B)
  | .tree f, _, subst => (foldFormula f subst).map id SharedFormula.tree
  | .share f n rest, fixed, subst =>
    match fixed.headD none with
    | some b => fold rest fixed.tail (withHead (.inl b) subst)
    | none =>
      match foldFormula f subst with
      | .inl b => fold rest fixed.tail (withHead (.inl b) subst)
      | .inr g => (fold rest fixed.tail (extend subst)).map id (SharedFormula.share g n)

def respects {A : Type} : SharedFormula A → List (Option Bool) → (A → Bool) → Prop
  | .tree _, _, _ => True
  | .share f _ rest, fixed, x =>
    (∀ b, fixed.headD none = some b → f.evalWith x = b) ∧
      respects rest fixed.tail (withHead (f.evalWith x) x)

theorem respects_of_profile (E : SharedFormula A) (fixed : List (Option Bool)) (x : A → Bool)
    (matchingBits : ∀ k b, k < (profile E x).length →
      fixed[k]? = some (some b) → (profile E x)[k]? = some b) :
    respects E fixed x := by
  induction E generalizing fixed with
  | tree => trivial
  | share f n rest ih =>
    constructor
    · intro b chosen
      have head : fixed[0]? = some (some b) := by
        cases fixed with
        | nil => simp at chosen
        | cons a rest => simpa using chosen
      have same := matchingBits 0 b (by simp [profile]) head
      simpa [profile] using same
    · apply ih
      intro k b inTail atTail
      have selected : fixed[k + 1]? = some (some b) := by
        cases fixed with
        | nil => simp at atTail
        | cons a rest => simpa using atTail
      have previous := matchingBits (k + 1) b (by simpa [profile] using inTail) selected
      simpa [profile] using previous

def value (E : Sum Bool (SharedFormula B)) (x : B → Bool) : Bool :=
  E.elim id (fun F => F.eval x)

theorem fold_eval (E : SharedFormula A) (fixed : List (Option Bool)) (subst : A → Sum Bool B)
    (x : B → Bool) (holds : respects E fixed (assign subst x)) :
    value (fold E fixed subst) x = E.eval (assign subst x) := by
  induction E generalizing B fixed with
  | tree f =>
    have base := foldFormula_eval f subst x
    cases h : foldFormula f subst <;> simpa [fold, h, value, formulaValue, SharedFormula.eval] using base
  | share f n rest ih =>
    have head := foldFormula_eval f subst x
    cases h : fixed.headD none with
    | some b =>
      have eq := holds.1 b h
      simpa only [fold, h, SharedFormula.eval, eq, assign_fixed] using
        ih fixed.tail (withHead (Sum.inl b) subst) x (by simpa only [assign_fixed, ← eq] using holds.2)
    | none =>
      cases g : foldFormula f subst with
      | inl b =>
        have eq : f.evalWith (assign subst x) = b := by simpa [g, formulaValue] using head.symm
        simpa only [fold, h, g, SharedFormula.eval, eq, assign_fixed] using
          ih fixed.tail (withHead (Sum.inl b) subst) x (by simpa only [assign_fixed, ← eq] using holds.2)
      | inr g' =>
        have eq : f.evalWith (assign subst x) = g'.evalWith x := by simpa [g, formulaValue] using head.symm
        have later := ih fixed.tail (extend subst) (withHead (g'.evalWith x) x)
          (by simpa only [assign_extend, ← eq] using holds.2)
        cases u : fold rest fixed.tail (extend subst) <;>
          rw [fold, h, g, u] <;>
          simpa [u, value, SharedFormula.eval, eq, assign_extend] using later

def kept (E : SharedFormula A) (fixed : List (Option Bool)) (w : A → ℕ) : ℕ :=
  keptWeight E (fixed.map Option.isSome) w

@[simp] private theorem kept_tree (f : Formula A) (fixed : List (Option Bool)) (w : A → ℕ) :
    kept (.tree f) fixed w = leafWeight f w := rfl

@[simp] private theorem kept_share (f : Formula A) (n : ℕ) (rest : SharedFormula (Option A))
    (fixed : List (Option Bool)) (w : A → ℕ) :
    kept (.share f n rest) fixed w =
      (if (fixed.headD none).isSome then 0 else leafWeight f w) + kept rest fixed.tail (withHead 0 w) := by
  cases fixed <;> rfl

private theorem kept_add (E : SharedFormula A) (fixed : List (Option Bool)) (u v : A → ℕ) :
    kept E fixed (fun a => u a + v a) = kept E fixed u + kept E fixed v := by
  induction E generalizing fixed with
  | tree => simp [leafWeight_add]
  | share f n rest ih =>
    have same : withHead 0 (fun a => u a + v a) = fun a => withHead 0 u a + withHead 0 v a := by
      funext a
      cases a <;> rfl
    simp only [kept_share, same, ih, leafWeight_add]
    split <;> omega

private theorem kept_head (E : SharedFormula (Option A)) (fixed : List (Option Bool)) (w : A → ℕ) :
    kept E fixed (withHead 1 w) =
      kept E fixed (withHead 0 w) + kept E fixed (withHead 1 fun _ => 0) := by
  have same : withHead 1 w = fun a => withHead 0 w a + withHead 1 (fun _ => 0) a := by
    funext a
    cases a <;> simp
  rw [same, kept_add]

def surplus {A : Type} : SharedFormula A → List (Option Bool) → ℕ
  | .tree _, _ => 0
  | .share _ _ rest, fixed =>
    (if (fixed.headD none).isSome then 0 else kept rest fixed.tail (withHead 1 fun _ => 0) - 1) +
      surplus rest fixed.tail

def cost : Sum Bool (SharedFormula A) → ℕ
  | .inl _ => 0
  | .inr E => gates E + 1

private theorem weight_fixed (b : Bool) (subst : A → Sum Bool B) :
    symbolWeight ∘ withHead (.inl b) subst = withHead 0 (symbolWeight ∘ subst) := by
  funext a
  cases a <;> rfl

private theorem weight_extend (subst : A → Sum Bool B) :
    symbolWeight ∘ extend subst = withHead 1 (symbolWeight ∘ subst) := by
  funext a
  cases a with
  | none => rfl
  | some a => cases h : subst a <;> simp [extend, withHead, Function.comp_apply, symbolWeight, h]

/-- The folded forest pays once for each live raw occurrence and once for
    each surviving repeated read. The count includes one for the output. -/
theorem fold_cost (E : SharedFormula A) (fixed : List (Option Bool)) (subst : A → Sum Bool B) :
    cost (fold E fixed subst) ≤ kept E fixed (symbolWeight ∘ subst) + surplus E fixed := by
  induction E generalizing B fixed with
  | tree f =>
    have bound := foldFormula_mass f subst
    cases h : foldFormula f subst with
    | inl => simp [fold, h, cost, surplus]
    | inr => simpa [fold, h, cost, surplus, gates, formulaMass] using bound
  | share f n rest ih =>
    cases h : fixed.headD none with
    | some b =>
      simp only [fold, h, kept_share, surplus, Option.isSome_some, ↓reduceIte, Nat.zero_add]
      simpa only [weight_fixed] using ih fixed.tail (withHead (.inl b) subst)
    | none =>
      cases g : foldFormula f subst with
      | inl b =>
        have saved := ih fixed.tail (withHead (.inl b) subst)
        simp only [weight_fixed] at saved
        simp only [fold, h, g, kept_share, surplus, Option.isSome_none, Bool.false_eq_true, ite_false]
        omega
      | inr g' =>
        have main := foldFormula_mass f subst
        simp only [g, formulaMass] at main
        have tail := ih fixed.tail (extend subst)
        rw [weight_extend, kept_head] at tail
        cases u : fold rest fixed.tail (extend subst) <;>
          simp only [fold, h, g, u, Sum.map_inl, Sum.map_inr, cost, gates, kept_share, surplus,
            Option.isSome_none, Bool.false_eq_true, ite_false] at * <;> omega

/-- A lower bound on the surviving inputs constrains the raw and repeated
    reads left after any valid simultaneous substitution. -/
theorem threshold_budget {n lower : ℕ} (size : 2 ≤ n) (floor : CrownLower.LowerBound n lower)
    (E : SharedFormula A) (fixed : List (Option Bool)) (subst : A → Sum Bool (Fin n))
    (test : ThresholdOn (fun x => E.eval (assign subst x)))
    (single : ∀ i, respects E fixed (assign subst (singletonInput i)))
    (pair : ∀ i j, i ≠ j → respects E fixed (assign subst (pairInput i j))) :
    lower + 1 ≤ kept E fixed (symbolWeight ∘ subst) + surplus E fixed := by
  have projected : ThresholdOn (value (fold E fixed subst)) := by
    exact ⟨fun i => (fold_eval E fixed subst _ (single i)).trans (test.1 i),
      fun i j ne => (fold_eval E fixed subst _ (pair i j ne)).trans (test.2 i j ne)⟩
  have budget := fold_cost E fixed subst
  cases result : fold E fixed subst with
  | inl b =>
    rw [result] at projected
    let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    have off : b = false := projected.1 i
    have on : b = true := projected.2 i j (by intro eq; have same := congrArg Fin.val eq; exact (by decide : 0 ≠ 1) same)
    rw [off] at on
    contradiction
  | inr F =>
    rw [result] at projected
    have tests : ThresholdOn F.eval := projected
    have needed := floor tests (evaluateForest F var (fun i => ⟨i, rfl⟩))
    simp only [result, cost] at budget
    omega

end CrownFrozenCost
