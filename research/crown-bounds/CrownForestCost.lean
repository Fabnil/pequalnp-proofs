import CrownFourNormal

namespace CrownForestCost

open CrownRun CrownForks CrownForest CrownSharedCuts PnpResearch Finset

def formulaGates {A : Type} : Formula A → ℕ
  | .var _ => 0
  | .conj f g | .disj f g => formulaGates f + formulaGates g + 1

def gates {A : Type} : SharedFormula A → ℕ
  | .tree f => formulaGates f
  | .share f _ rest => formulaGates f + gates rest

private theorem binaryLeaves {A : Type} (f : Formula A) :
    leafWeight f (fun _ => 1) = formulaGates f + 1 := by
  induction f <;> simp_all [leafWeight, formulaGates] <;> omega

theorem weightGates {A : Type} (E : SharedFormula A) (valid : E.Valid) :
    E.weight (fun _ => 1) + E.extraUses = gates E + 1 := by
  induction E with
  | tree f => simpa [SharedFormula.weight, SharedFormula.extraUses, gates] using binaryLeaves f
  | @share T f u rest ih =>
    have split : (fun _ : Option T => (1 : ℕ)) =
        fun b => withHead 0 (fun _ => 1) b + withHead 1 (fun _ => 0) b := by
      funext b
      cases b <;> rfl
    have inRest := ih valid.2.1
    rw [split, weightAdd, valid.2.2] at inRest
    simp only [SharedFormula.weight, SharedFormula.extraUses, gates, binaryLeaves]
    omega

theorem weightSum {A K : Type} (E : SharedFormula A) (S : Finset K) (v : K → A → ℕ) :
    E.weight (fun a => ∑ k ∈ S, v k a) = ∑ k ∈ S, E.weight (v k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have h := weightAdd E (fun _ => 0) (fun _ => 0)
    simp only [Nat.add_zero] at h
    omega
  | insert k S hk ih =>
    have split : (fun a => ∑ j ∈ insert k S, v j a) = fun a => v k a + ∑ j ∈ S, v j a := by
      funext a
      rw [sum_insert hk]
    rw [split, weightAdd, ih, sum_insert hk]

/-- Evaluate a formula and make its output available to the remaining circuit. -/
theorem evaluateFormula {n : ℕ} {A : Type} (f : Formula A) (value : A → BF n)
    {S : BF n → Prop} {m : ℕ} {out : BF n} (available : ∀ a, S (value a))
    (later : UC gF MonoA m (fun w => w = wire value f ∨ S w) out) :
    UC gF MonoA (m + formulaGates f) S out := by
  induction f generalizing S m with
  | var a =>
    rw [formulaGates, Nat.add_zero]
    apply UC_monoS gF MonoA _ _ _ _ _ later
    intro w h
    rcases h with rfl | h
    · exact available a
    · exact h
  | conj l r il ir | disj l r il ir =>
    let a := wire value l
    let b := wire value r
    suffices binary : ∀ k : Fin 4, MonoA k →
        UC gF MonoA m (fun w => w = gF k a b ∨ S w) out →
        UC gF MonoA (m + (formulaGates l + formulaGates r + 1)) S out by
      first | exact binary 0 (by simp [MonoA]) later | exact binary 1 (by simp [MonoA]) later
    intro k hk next
    let haveLeft (w : BF n) := w = a ∨ S w
    have both : UC gF MonoA (m + 1) (fun w => w = b ∨ haveLeft w) out := by
      refine UC_gate k a b hk (Or.inr (Or.inl rfl)) (Or.inl rfl) ?_
      apply UC_monoS gF MonoA m (fun w => w = gF k a b ∨ S w)
        (fun w => w = gF k a b ∨ (w = b ∨ haveLeft w)) out _ next
      intro w hw
      exact hw.imp id (fun old => Or.inr (Or.inr old))
    have left : UC gF MonoA (m + 1 + formulaGates r) haveLeft out :=
      ir (fun x => Or.inr (available x)) both
    have result := il available left
    exact UC_le (by omega) result

theorem evaluateForest {n : ℕ} {A : Type} (E : SharedFormula A) (value : A → BF n)
    {S : BF n → Prop} (available : ∀ a, S (value a)) :
    UC gF MonoA (gates E) S (E.evalFn value) := by
  induction E generalizing S with
  | tree f =>
    have finish : UC gF MonoA 0 (fun w => w = wire value f ∨ S w) (wire value f) := Or.inl rfl
    change UC gF MonoA (formulaGates f) S (wire value f)
    simpa only [Nat.zero_add] using evaluateFormula f value available finish
  | share f extra rest ih =>
    let shifted := withHead (wire value f) value
    have ready (a : Option _) : shifted a = wire value f ∨ S (shifted a) := by
      cases a with
      | none => exact Or.inl rfl
      | some a => exact Or.inr (available a)
    have tail := ih shifted (S := fun w => w = wire value f ∨ S w) ready
    have run := evaluateFormula f value available tail
    have eval : (SharedFormula.share f extra rest).evalFn value = rest.evalFn shifted := by
      funext x
      apply congrArg rest.eval
      funext a
      cases a <;> rfl
    simpa only [gates, eval, Nat.add_comm] using run

theorem tenRequires23 (E : SharedFormula (Fin 10)) (test : ThresholdOn E.eval) : 23 ≤ gates E := by
  have bound : CrownLower.LowerBound 10 23 := CrownProduct.thresholdLowerFromEight 2
  exact bound test (evaluateForest E var (fun i => ⟨i, rfl⟩))

theorem fourWithTwoReadsCosts23 (E : SharedFormula (Fin 10)) (valid : E.Valid)
    (reads : ∀ i, E.weight (CrownProfileThree.Network.ones i) = 2) (extra : E.extraUses = 4) :
    gates E = 23 := by
  have all : (fun _ : Fin 10 => (1 : ℕ)) =
      fun a => ∑ i : Fin 10, CrownProfileThree.Network.ones i a := by
    funext a
    rw [sum_eq_single_of_mem a (mem_univ _)]
    · simp [CrownProfileThree.Network.ones, singletonInput]
    · intro i _ ne
      simp [CrownProfileThree.Network.ones, singletonInput, ne.symm]
  have count := weightGates E valid
  rw [all, weightSum, extra] at count
  simp [reads] at count
  omega

end CrownForestCost
