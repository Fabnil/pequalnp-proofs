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

theorem run_of_terminal (rules : List (AndRule A)) (active : Finset A)
    (terminal : ∀ rule ∈ rules, ¬(rule.left ∈ active ∧ rule.right ∈ active)) :
    run rules active = active := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
    change run rest (rule.step active) = active
    have disabled := terminal rule List.mem_cons_self
    simpa [AndRule.step, disabled] using ih (fun r hr => terminal r (List.mem_cons_of_mem _ hr))

/-- If the two terminal pairs share a position and jointly accept, their
    other positions must be partners. Accepting with the first pair then
    forces a third terminal set with the same shared position to include
    the second pair. -/
theorem pairs_force_subset (rules : List (AndRule A)) (third : Finset A)
    {out common x y partner : A} (distinct : x ≠ partner) (outputDistinct : out ≠ x)
    (partnerDistinct : partner ≠ common)
    (unique : ∀ rule ∈ rules, (rule.left = x → rule.right = partner) ∧
      (rule.right = x → rule.left = partner))
    (pairTerminal : ∀ rule ∈ rules, ¬(rule.left ∈ ({common, y} : Finset A) ∧
      rule.right ∈ ({common, y} : Finset A)))
    (thirdTerminal : ∀ rule ∈ rules, ¬(rule.left ∈ third ∧ rule.right ∈ third))
    (withoutPair : out ∉ ({common, y} : Finset A)) (withoutThird : out ∉ third)
    (withPair : out ∈ run rules (insert x {common, y}))
    (withThird : out ∈ run rules (insert x third)) (contains : common ∈ third) :
    ({common, y} : Finset A) ⊆ third := by
  have inPair := partner_of_new_output rules {common, y} distinct outputDistinct unique
    (by rwa [run_of_terminal rules _ pairTerminal]) withPair
  rw [run_of_terminal rules _ pairTerminal] at inPair
  have partnerEq : partner = y := by
    simp [partnerDistinct] at inPair
    exact inPair
  have inThird := partner_of_new_output rules third distinct outputDistinct unique
    (by rwa [run_of_terminal rules _ thirdTerminal]) withThird
  rw [run_of_terminal rules _ thirdTerminal, partnerEq] at inThird
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | h
  · exact contains
  · simpa using (Finset.mem_singleton.mp h ▸ inThird : a ∈ third)

end CrownDemand
