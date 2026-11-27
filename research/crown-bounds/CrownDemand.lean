import CrownBlocks

/-! A singleton position can change the answer only through its unique rule. -/

namespace CrownDemand

variable {A : Type*} [DecidableEq A]

structure AndRule (A : Type*) where
  left : A
  right : A
  destinations : Finset A

def AndRule.step (rule : AndRule A) (active : Finset A) : Finset A :=
  if rule.left ∈ active ∧ rule.right ∈ active then active ∪ rule.destinations else active

def run (rules : List (AndRule A)) (active : Finset A) : Finset A :=
  rules.foldl (fun active rule => rule.step active) active

theorem AndRule.step_contains (rule : AndRule A) (active : Finset A) :
    active ⊆ rule.step active := by
  unfold step
  split
  · exact Finset.subset_union_left
  · exact Finset.Subset.rfl

theorem run_contains (rules : List (AndRule A)) (active : Finset A) :
    active ⊆ run rules active := by
  induction rules generalizing active with
  | nil => exact Finset.Subset.rfl
  | cons rule rest ih =>
    exact (rule.step_contains active).trans (ih (rule.step active))

private theorem step_insert (rule : AndRule A) (active : Finset A) {b a : A}
    (distinct : b ≠ a) (absent : a ∉ active)
    (left : rule.left = b → rule.right = a) (right : rule.right = b → rule.left = a) :
    rule.step (insert b active) = insert b (rule.step active) := by
  by_cases hl : rule.left = b
  · simp [AndRule.step, left hl, distinct.symm, absent]
  by_cases hr : rule.right = b
  · simp [AndRule.step, right hr, distinct.symm, absent]
  by_cases enabled : rule.left ∈ active ∧ rule.right ∈ active <;>
    simp [AndRule.step, hl, hr, enabled, Finset.insert_union]

theorem run_insert_of_partner_absent (rules : List (AndRule A)) (active : Finset A)
    {b a : A} (distinct : b ≠ a)
    (unique : ∀ rule ∈ rules, (rule.left = b → rule.right = a) ∧
      (rule.right = b → rule.left = a))
    (absent : a ∉ run rules active) :
    run rules (insert b active) = insert b (run rules active) := by
  induction rules generalizing active with
  | nil => rfl
  | cons rule rest ih =>
    have none : a ∉ active := fun yes => absent (run_contains _ _ yes)
    obtain ⟨left, right⟩ := unique rule List.mem_cons_self
    change run rest (rule.step (insert b active)) = insert b (run rest (rule.step active))
    rw [step_insert rule active distinct none left right]
    exact ih (rule.step active) (fun r hr => unique r (List.mem_cons_of_mem _ hr)) absent

/-- If inserting a position changes a false output to true, its unique
    partner was already present in the run without the insertion. -/
theorem partner_of_new_output (rules : List (AndRule A)) (active : Finset A)
    {out b a : A} (distinct : b ≠ a) (outputDistinct : out ≠ b)
    (unique : ∀ rule ∈ rules, (rule.left = b → rule.right = a) ∧
      (rule.right = b → rule.left = a))
    (without : out ∉ run rules active) (withSlot : out ∈ run rules (insert b active)) :
    a ∈ run rules active := by
  by_contra absent
  rw [run_insert_of_partner_absent rules active distinct unique absent] at withSlot
  exact (Finset.mem_insert.mp withSlot).elim outputDistinct without

end CrownDemand
