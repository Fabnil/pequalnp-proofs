import CrownDropZero

namespace CrownRestriction

open CrownRun CrownForks CrownForest CrownSharedCuts CrownForestCost CrownDropZero PnpResearch

/-- No conjunction discards a surviving child when the other child is
    set to zero. The condition applies recursively to every subformula. -/
def FormulaKeepsLeaves {A B : Type} (keep : A → Option B) : Formula A → Prop
  | .var _ => True
  | .disj l r => FormulaKeepsLeaves keep l ∧ FormulaKeepsLeaves keep r
  | .conj l r => FormulaKeepsLeaves keep l ∧ FormulaKeepsLeaves keep r ∧
      (formulaRestrict l keep).isNone = (formulaRestrict r keep).isNone

theorem formula_tight_keeps_leaves {A B : Type} (f : Formula A) (keep : A → Option B)
    (tight : formulaLeaves (formulaRestrict f keep) + leafWeight f (missing keep) =
      formulaGates f + 1) : FormulaKeepsLeaves keep f := by
  induction f with
  | var a => trivial
  | disj l r il ir =>
    have lessL := formulaRestrict_leaves l keep
    have lessR := formulaRestrict_leaves r keep
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [formulaRestrict, hl, hr, formulaLeaves, leafWeight, formulaGates] at tight lessL lessR <;>
      exact ⟨il (by simp [hl, formulaLeaves]; omega), ir (by simp [hr, formulaLeaves]; omega)⟩
  | conj l r il ir =>
    have lessL := formulaRestrict_leaves l keep
    have lessR := formulaRestrict_leaves r keep
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [formulaRestrict, hl, hr, formulaLeaves, leafWeight, formulaGates] at tight lessL lessR
    · exact ⟨il (by simp [hl, formulaLeaves]; omega), ir (by simp [hr, formulaLeaves]; omega), by simp [hl, hr]⟩
    · omega
    · omega
    · exact ⟨il (by simp [hl, formulaLeaves]; omega), ir (by simp [hr, formulaLeaves]; omega), by simp [hl, hr]⟩

/-- Every shared signal survives the restriction and every formula keeps
    all of the leaves not explicitly set to zero. -/
def KeepsLeaves {A B : Type} (keep : A → Option B) : SharedFormula A → Prop
  | .tree f => FormulaKeepsLeaves keep f
  | .share f _ rest => (formulaRestrict f keep).isSome ∧ FormulaKeepsLeaves keep f ∧
      KeepsLeaves (keepHead keep) rest

private theorem missing_without_head {A B : Type} (keep : A → Option B) :
    missing (withHead none keep) = fun a =>
      withHead 0 (missing keep) a + withHead 1 (fun _ => 0) a := by
  funext a
  cases a <;> simp [missing]

private theorem missing_with_head {A B : Type} (keep : A → Option B) :
    missing (keepHead keep) = withHead 0 (missing keep) := by
  funext a
  cases a with
  | none => rfl
  | some a => cases h : keep a <;> simp [keepHead, missing, h]

theorem tight_keeps_leaves {A B : Type} (E : SharedFormula A) (valid : E.Valid) (keep : A → Option B)
    (live : (restrict E keep).isSome)
    (tight : forestCost (restrict E keep) + E.weight (missing keep) = gates E + 1) :
    KeepsLeaves keep E := by
  induction E generalizing B with
  | tree f =>
    cases hf : formulaRestrict f keep with
    | none => simp [restrict, hf] at live
    | some g =>
      exact formula_tight_keeps_leaves f keep (by
        simpa [restrict, hf, forestCost, formulaLeaves, SharedFormula.weight, gates] using tight)
  | @share A f extra rest ih =>
    have main := formulaRestrict_leaves f keep
    cases hf : formulaRestrict f keep with
    | none =>
      have tail := restrict_cost rest valid.2.1 (withHead none keep)
      rw [missing_without_head, weightAdd, valid.2.2] at tail
      simp only [hf, formulaLeaves] at main
      simp only [restrict, hf, SharedFormula.weight, gates] at tight
      have positive := valid.1
      omega
    | some g =>
      have tail := restrict_cost rest valid.2.1 (keepHead keep)
      rw [missing_with_head] at tail
      have mainBound :
          formulaGates g + 1 + leafWeight f (missing keep) ≤ formulaGates f + 1 := by
        simpa [hf, formulaLeaves] using main
      cases ht : restrict rest (keepHead keep) with
      | none => simp [restrict, hf, ht] at live
      | some t =>
        simp only [restrict, hf, ht, Option.map_some, forestCost, SharedFormula.weight, gates] at tight
        simp only [ht, forestCost] at tail
        refine ⟨by simp [hf], formula_tight_keeps_leaves f keep ?_, ih valid.2.1 (keepHead keep) (by simp [ht]) ?_⟩
        · simp only [hf, formulaLeaves]
          omega
        · simp only [ht, forestCost, missing_with_head]
          omega

noncomputable def removeInput {n : ℕ} (p i : Fin (n + 1)) : Option (Fin n) :=
  if h : ∃ j, p.succAbove j = i then some h.choose else none

theorem remove_assignment {n : ℕ} (p : Fin (n + 1)) (x : Fin n → Bool) :
    assignment (removeInput p) x = CrownErase.liftBits p x := by
  funext i
  unfold removeInput CrownErase.liftBits
  split <;> simp [assignment, *]

private theorem remove_missing {n : ℕ} (p : Fin (n + 1)) :
    missing (removeInput p) = CrownProfileThree.Network.ones p := by
  funext i
  by_cases h : i = p
  · subst i
    simp [removeInput, missing, CrownProfileThree.Network.ones, singletonInput]
  · have someInput := Fin.exists_succAbove_eq (x := i) (y := p) h
    simp [removeInput, missing, CrownProfileThree.Network.ones, singletonInput, h, someInput]

/-- When the restriction meets the lower bound, every gate saving is paid
    for by a deleted input occurrence. All shared stages remain live. -/
theorem tightRestriction {A : Type} {n bound removed : ℕ} (size : 2 ≤ n)
    (floor : CrownLower.LowerBound n bound) (E : SharedFormula A) (keep : A → Option (Fin n))
    (valid : E.Valid) (test : ThresholdOn (fun x => E.eval (assignment keep x)))
    (deleted : E.weight (missing keep) = removed) (cost : gates E ≤ bound + removed) :
    gates E = bound + removed ∧ ∃ F, restrict E keep = some F ∧
      gates F = bound ∧ KeepsLeaves keep E := by
  have same : forestEval (restrict E keep) = fun x => E.eval (assignment keep x) :=
    funext (restrict_eval E keep)
  have reduced : ThresholdOn (forestEval (restrict E keep)) := by rwa [same]
  have budget := restrict_cost E valid keep
  rw [deleted] at budget
  cases h : restrict E keep with
  | none =>
    have no := CrownLower.thresholdNonzero size reduced
    rw [h] at no
    exact (no rfl).elim
  | some F =>
    rw [h] at reduced
    have tests : ThresholdOn F.eval := ⟨reduced.1, reduced.2⟩
    have lower : bound ≤ gates F := floor tests (evaluateForest F var (fun i => ⟨i, rfl⟩))
    simp only [h, forestCost] at budget
    have exactCost : gates E = bound + removed := by omega
    have reducedCost : gates F = bound := by omega
    refine ⟨exactCost, F, rfl, reducedCost, tight_keeps_leaves E valid keep (by simp [h]) ?_⟩
    simp only [h, forestCost, deleted, exactCost, reducedCost]
    omega

/-- At the two-gate extension of a checked lower bound, removing any input
    deletes exactly its two reads. In particular each shared signal survives. -/
theorem tightInputDeletion {n bound : ℕ} (size : 2 ≤ n) (floor : CrownLower.LowerBound n bound)
    (E : SharedFormula (Fin (n + 1))) (valid : E.Valid) (test : ThresholdOn E.eval)
    (reads : ∀ i, E.weight (CrownProfileThree.Network.ones i) = 2)
    (cost : gates E ≤ bound + 2) (p : Fin (n + 1)) :
    gates E = bound + 2 ∧ ∃ F, restrict E (removeInput p) = some F ∧
      gates F = bound ∧ KeepsLeaves (removeInput p) E := by
  refine tightRestriction size floor E (removeInput p) valid ?_ ?_ cost
  · simpa only [remove_assignment] using CrownErase.liftThreshold test p
  · simp only [remove_missing, reads]

theorem remove_at {n : ℕ} (p : Fin (n + 1)) : removeInput p p = none := by
  simp [removeInput]

theorem remove_on {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : removeInput p (p.succAbove i) = some i := by
  unfold removeInput
  split
  · rename_i found
    rw [Fin.succAbove_right_injective found.choose_spec]
  · rename_i impossible
    exact (impossible ⟨i, rfl⟩).elim

/-- After deleting p, q denotes the second input in the smaller coordinate
    set. Its original index is p.succAbove q. -/
noncomputable def removeTwo {n : ℕ} (p : Fin (n + 2)) (q : Fin (n + 1))
    (i : Fin (n + 2)) : Option (Fin n) :=
  (removeInput p i).bind (removeInput q)

private theorem removeTwo_assignment {n : ℕ} (p : Fin (n + 2)) (q : Fin (n + 1))
    (x : Fin n → Bool) :
    assignment (removeTwo p q) x = CrownErase.liftBits p (CrownErase.liftBits q x) := by
  rw [← remove_assignment q x, ← remove_assignment p]
  funext i
  cases h : removeInput p i <;> simp [removeTwo, assignment, h]

private theorem removeTwo_missing {n : ℕ} (p : Fin (n + 2)) (q : Fin (n + 1)) :
    missing (removeTwo p q) = fun a =>
      CrownProfileThree.Network.ones p a + CrownProfileThree.Network.ones (p.succAbove q) a := by
  funext i
  by_cases eq : i = p
  · subst i
    simp [removeTwo, remove_at, missing, CrownProfileThree.Network.ones, singletonInput,
      (Fin.succAbove_ne p q).symm]
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq (x := i) (y := p) eq
    have missing_q := congrFun (remove_missing q) j
    change ((removeInput p (p.succAbove j)).bind (removeInput q)).isNone.toNat = _
    rw [remove_on]
    simpa [missing, CrownProfileThree.Network.ones, singletonInput,
      Fin.succAbove_ne p j, Fin.succAbove_right_injective.eq_iff] using missing_q

theorem tightDoubleDeletion {n bound : ℕ} (size : 2 ≤ n) (floor : CrownLower.LowerBound n bound)
    (E : SharedFormula (Fin (n + 2))) (valid : E.Valid) (test : ThresholdOn E.eval)
    (reads : ∀ i, E.weight (CrownProfileThree.Network.ones i) = 2)
    (cost : gates E ≤ bound + 4) (p : Fin (n + 2)) (q : Fin (n + 1)) :
    gates E = bound + 4 ∧ ∃ F, restrict E (removeTwo p q) = some F ∧
      gates F = bound ∧ KeepsLeaves (removeTwo p q) E := by
  refine tightRestriction size floor E (removeTwo p q) valid ?_ ?_ cost
  · simpa only [removeTwo_assignment] using CrownErase.liftThreshold (CrownErase.liftThreshold test p) q
  · rw [removeTwo_missing, weightAdd, reads, reads]

/-- Whether a leaf labeled by this key is a direct input to a conjunction. -/
def andReads {A : Type} (p : A) : Formula A → Prop
  | .var _ => False
  | .disj l r => andReads p l ∨ andReads p r
  | .conj l r => l = .var p ∨ r = .var p ∨ andReads p l ∨ andReads p r

def forestAndReads {A : Type} (p : A) : SharedFormula A → Prop
  | .tree f => andReads p f
  | .share f _ rest => andReads p f ∨ forestAndReads (some p) rest

private theorem erased_formula_constant {A B : Type} (f : Formula A) (keep : A → Option B)
    (tight : FormulaKeepsLeaves keep f) (gone : formulaRestrict f keep = none)
    (x : A → Bool) (bit : Bool) (same : ∀ a, keep a = none → x a = bit) :
    f.evalWith x = bit := by
  induction f with
  | var a =>
    cases h : keep a with
    | none => exact same a h
    | some _ => simp [formulaRestrict, h] at gone
  | disj l r il ir =>
    have hL := tight.1
    have hR := tight.2
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [formulaRestrict, hl, hr] at gone
    simp [Formula.evalWith, il hL hl, ir hR hr]
  | conj l r il ir =>
    have hL := tight.1
    have hR := tight.2.1
    have together := tight.2.2
    cases hl : formulaRestrict l keep <;> cases hr : formulaRestrict r keep <;>
      simp [formulaRestrict, hl, hr] at gone together
    simp [Formula.evalWith, il hL hl, ir hR hr]

private theorem smaller_if_and_reads {A B : Type} (f : Formula A) (keep : A → Option B) (p : A)
    (only : ∀ a, keep a = none ↔ a = p) (tight : FormulaKeepsLeaves keep f) (hit : andReads p f) :
    ∃ g, formulaGates g < formulaGates f ∧ g.evalWith = f.evalWith := by
  induction f with
  | var a => exact (False.elim hit)
  | disj l r il ir =>
    rcases hit with left | right
    · obtain ⟨g, less, same⟩ := il tight.1 left
      refine ⟨.disj g r, by simp only [formulaGates]; omega, ?_⟩
      funext x
      simp [Formula.evalWith, same]
    · obtain ⟨g, less, same⟩ := ir tight.2 right
      refine ⟨.disj l g, by simp only [formulaGates]; omega, ?_⟩
      funext x
      simp [Formula.evalWith, same]
  | conj l r il ir =>
    have pGone : formulaRestrict (.var p) keep = none := by
      simp [formulaRestrict, (only p).2 rfl]
    have value (x : A → Bool) (a : A) (gone : keep a = none) : x a = x p :=
      congrArg x ((only a).1 gone)
    rcases hit with left | right | left | right
    · subst l
      have both := tight.2.2
      rw [pGone] at both
      have dead : formulaRestrict r keep = none := by
        cases h : formulaRestrict r keep <;> simp_all
      refine ⟨.var p, by simp [formulaGates], ?_⟩
      funext x
      simp [Formula.evalWith, erased_formula_constant r keep tight.2.1 dead x (x p) (value x)]
    · subst r
      have both := tight.2.2
      rw [pGone] at both
      have dead : formulaRestrict l keep = none := by
        cases h : formulaRestrict l keep <;> simp_all
      refine ⟨.var p, by simp [formulaGates], ?_⟩
      funext x
      simp [Formula.evalWith, erased_formula_constant l keep tight.1 dead x (x p) (value x)]
    · obtain ⟨g, less, same⟩ := il tight.1 left
      refine ⟨.conj g r, by simp only [formulaGates]; omega, ?_⟩
      funext x
      simp [Formula.evalWith, same]
    · obtain ⟨g, less, same⟩ := ir tight.2.1 right
      refine ⟨.conj l g, by simp only [formulaGates]; omega, ?_⟩
      funext x
      simp [Formula.evalWith, same]

private theorem cheaper_if_forest_and_reads {A B : Type} (E : SharedFormula A) (keep : A → Option B)
    (p : A) (only : ∀ a, keep a = none ↔ a = p)
    (tight : KeepsLeaves keep E) (hit : forestAndReads p E) :
    ∃ F, gates F < gates E ∧ F.eval = E.eval := by
  induction E generalizing B with
  | tree f =>
    obtain ⟨g, less, same⟩ := smaller_if_and_reads f keep p only tight hit
    exact ⟨.tree g, less, same⟩
  | share f extra rest ih =>
    rcases hit with here | later
    · obtain ⟨g, less, same⟩ := smaller_if_and_reads f keep p only tight.2.1 here
      refine ⟨.share g extra rest, Nat.add_lt_add_right less _, ?_⟩
      funext x
      simp [SharedFormula.eval, same]
    · have kept : ∀ a, keepHead keep a = none ↔ a = some p := by
        intro a
        cases a with
        | none => simp [keepHead]
        | some a => simpa [keepHead] using only a
      obtain ⟨G, less, same⟩ := ih (keepHead keep) (some p) kept tight.2.2 later
      refine ⟨.share f extra G, Nat.add_lt_add_left less _, ?_⟩
      funext x
      simp [SharedFormula.eval, same]

/-- For a minimum-size threshold forest at a tight deletion budget, every
    direct gate reading a raw input is an OR gate. -/
theorem noAndReadsAtMargin {n bound : ℕ} (floor : CrownLower.LowerBound (n + 1) bound)
    (E : SharedFormula (Fin (n + 1))) (test : ThresholdOn E.eval) (cost : gates E ≤ bound)
    (p : Fin (n + 1)) (tight : KeepsLeaves (removeInput p) E) :
    ¬ forestAndReads p E := by
  intro hit
  have only (a : Fin (n + 1)) : removeInput p a = none ↔ a = p := by
    by_cases eq : a = p
    · subst a
      simp [removeInput]
    · have survives := Fin.exists_succAbove_eq (x := a) (y := p) eq
      simp [removeInput, eq, survives]
  obtain ⟨F, less, same⟩ := cheaper_if_forest_and_reads E (removeInput p) p only tight hit
  have passes : ThresholdOn F.eval := by rwa [same]
  have lower : bound ≤ gates F := floor passes (evaluateForest F var (fun i => ⟨i, rfl⟩))
  omega

end CrownRestriction
