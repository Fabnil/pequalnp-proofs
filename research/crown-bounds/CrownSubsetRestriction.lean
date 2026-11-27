import CrownRestriction
import Mathlib.Data.Finset.Sort

namespace CrownSubsetRestriction

open CrownForks CrownForest CrownForestCost CrownDropZero CrownRestriction Finset
open CrownProfileThree.Network (ones)

/-- Number the retained input coordinates in increasing order. -/
noncomputable def keepSubset {m n : ℕ} (retained : Finset (Fin m))
    (count : retained.card = n) (a : Fin m) : Option (Fin n) :=
  if h : a ∈ retained then some ((retained.orderIsoOfFin count).symm ⟨a, h⟩) else none

theorem assignment_outside {m n : ℕ} {s : Finset (Fin m)} {a : Fin m} (count : s.card = n)
    (x : Fin n → Bool) (outside : a ∉ s) : assignment (keepSubset s count) x a = false := by
  simp [assignment, keepSubset, outside]

private theorem assignment_on {m n : ℕ} {s : Finset (Fin m)} (count : s.card = n)
    (x : Fin n → Bool) (i : Fin n) :
    assignment (keepSubset s count) x (s.orderEmbOfFin count i) = x i := by
  have inside := s.orderEmbOfFin_mem count i
  simp only [assignment, keepSubset, dite_eq_left inside, Option.map_some, Option.getD_some]
  change x ((s.orderIsoOfFin count).symm (s.orderIsoOfFin count i)) = x i
  rw [OrderIso.symm_apply_apply]

private theorem assignment_singleton {m n : ℕ} {s : Finset (Fin m)}
    (count : s.card = n) (i : Fin n) :
    assignment (keepSubset s count) (singletonInput i) = singletonInput (s.orderEmbOfFin count i) := by
  funext a
  by_cases inside : a ∈ s
  · obtain ⟨j, eq⟩ := (s.orderIsoOfFin count).surjective ⟨a, inside⟩
    have same : s.orderEmbOfFin count j = a := congrArg Subtype.val eq
    rw [← same, assignment_on]
    simp [singletonInput, (s.orderEmbOfFin count).injective.eq_iff]
  · rw [assignment_outside count _ inside]
    have ne : a ≠ s.orderEmbOfFin count i := fun eq => inside (eq.symm ▸ s.orderEmbOfFin_mem count i)
    simp [singletonInput, ne]

private theorem assignment_pair {m n : ℕ} {s : Finset (Fin m)}
    (count : s.card = n) (i j : Fin n) :
    assignment (keepSubset s count) (pairInput i j) =
      pairInput (s.orderEmbOfFin count i) (s.orderEmbOfFin count j) := by
  funext a
  change assignment (keepSubset s count) (pairInput i j) a =
    (singletonInput (s.orderEmbOfFin count i) a || singletonInput (s.orderEmbOfFin count j) a)
  rw [← congrFun (assignment_singleton count i) a, ← congrFun (assignment_singleton count j) a]
  cases h : keepSubset s count a <;> simp [assignment, pairInput, h]

private theorem missing_weight {m n : ℕ} {s : Finset (Fin m)} (count : s.card = n)
    (E : SharedFormula (Fin m)) (reads : ∀ i, E.weight (ones i) = 2) :
    E.weight (missing (keepSubset s count)) = 2 * (univ \ s).card := by
  have eq : missing (keepSubset s count) = fun a => ∑ i ∈ univ \ s, ones i a := by
    funext a
    have bits (i : Fin m) : ones i a = if a = i then 1 else 0 := by
      by_cases h : a = i <;> simp [ones, singletonInput, h]
    by_cases h : a ∈ s <;> simp [missing, keepSubset, bits, h]
  rw [eq, weightSum]
  simp [reads, Nat.mul_comm]

theorem tightSubset {m n bound : ℕ} (size : 2 ≤ n) (floor : CrownLower.LowerBound n bound)
    (E : SharedFormula (Fin m)) (valid : E.Valid) (test : ThresholdOn E.eval)
    (reads : ∀ i, E.weight (ones i) = 2) (s : Finset (Fin m)) (count : s.card = n)
    (cost : gates E ≤ bound + 2 * (univ \ s).card) :
    ∃ F, restrict E (keepSubset s count) = some F ∧ gates F = bound ∧ KeepsLeaves (keepSubset s count) E := by
  have tests : ThresholdOn (fun x => E.eval (assignment (keepSubset s count) x)) := by
    refine ⟨fun i => ?_, fun i j ne => ?_⟩
    · change E.eval (assignment (keepSubset s count) (singletonInput i)) = false
      rw [assignment_singleton]
      exact test.1 _
    · change E.eval (assignment (keepSubset s count) (pairInput i j)) = true
      rw [assignment_pair]
      exact test.2 _ _ (fun eq => ne ((s.orderEmbOfFin count).injective eq))
  exact (tightRestriction size floor E (keepSubset s count) valid tests
    (missing_weight count E reads) cost).2

end CrownSubsetRestriction
