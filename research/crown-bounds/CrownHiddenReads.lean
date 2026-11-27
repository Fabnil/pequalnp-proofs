import CrownFourProfiles
import CrownDropZero

namespace CrownHiddenReads

open CrownForks CrownForest CrownProfiles CrownForestCost CrownDropZero
open CrownVisibility CrownFourProfiles PnpResearch
open CrownProfileThree.Network (ones)

variable {A I : Type}

private def delete [DecidableEq A] (i a : A) : Option A :=
  if a = i then none else some a

/-- If a single variable already forces a formula to one, it can be extracted
    once as a disjunct. The remaining formula has that variable set to zero. -/
theorem repeatReducible [DecidableEq A] (f : Formula A) (i : A)
    (active : f.evalWith (singletonInput i) = true) (repeated : 1 < leafWeight f (ones i)) :
    ∃ g : Formula A, formulaGates g < formulaGates f ∧ ∀ x, g.evalWith x = f.evalWith x := by
  have weights : missing (delete i) = ones i := by
    funext a
    by_cases same : a = i <;> simp [missing, delete, ones, singletonInput, same]
  have leaves := formulaRestrict_leaves f (delete i)
  rw [weights] at leaves
  have split (x : A → Bool) : (x i || formulaEval (formulaRestrict f (delete i)) x) = f.evalWith x := by
    cases on : x i with
    | false =>
      have same : assignment (delete i) x = x := by
        funext a
        by_cases eq : a = i
        · subst a
          simp [assignment, delete, on]
        · simp [assignment, delete, eq]
      simpa only [Bool.false_or, same] using formulaRestrict_eval f (delete i) x
    | true =>
      rw [Bool.true_or]
      symm
      apply (Bool.le_iff_imp.mp (evalMono f ?_)) active
      intro a
      by_cases eq : a = i
      · subst a
        simp [on]
      · simp [singletonInput, eq]
  cases h : formulaRestrict f (delete i) with
  | none =>
    refine ⟨.var i, ?_, fun x => ?_⟩
    · simp only [h, formulaLeaves] at leaves
      simp only [formulaGates]
      omega
    · simpa only [h, formulaEval, Bool.or_false, Formula.evalWith] using split x
  | some rest =>
    refine ⟨.disj (.var i) rest, ?_, fun x => ?_⟩
    · simp only [h, formulaLeaves] at leaves
      simp only [formulaGates]
      omega
    · simpa only [h, formulaEval, Formula.evalWith] using split x

theorem firstRepeatCheaper [deq : DecidableEq A] (E : SharedFormula A) (i : A)
    (head : true ∈ profile E (singletonInput i))
    (twice : 1 < stageWeight E (ones i) (firstHot E (singletonInput i))) :
    ∃ F : SharedFormula A, gates F < gates E ∧ F.eval = E.eval := by
  revert i
  revert deq
  induction E with
  | tree f =>
    intro _ i head _
    simp [profile] at head
  | share f u rest ih =>
    intro deq i head twice
    cases on : f.evalWith (singletonInput i) with
    | true =>
      have count : 1 < leafWeight f (ones i) := by
        simpa [firstHot, profile, on, List.findIdx_cons, stageWeight] using twice
      obtain ⟨g, less, equal⟩ := repeatReducible f i on count
      refine ⟨.share g u rest, Nat.add_lt_add_right less _, ?_⟩
      funext x
      simp only [SharedFormula.eval, equal x]
    | false =>
      have next : withHead false (singletonInput i) = singletonInput (some i) := by
        funext a
        cases a <;> simp [singletonInput]
      have nextWeight : withHead 0 (ones i) = ones (some i) := by
        funext a
        cases a <;> simp [ones, singletonInput]
      have warm : true ∈ profile rest (singletonInput (some i)) := by
        simpa [profile, on, next] using head
      have read : 1 < stageWeight rest (ones (some i)) (firstHot rest (singletonInput (some i))) := by
        simpa [firstHot, profile, on, List.findIdx_cons, stageWeight, nextWeight, next] using twice
      obtain ⟨G, less, equal⟩ := @ih inferInstance (some i) warm read
      refine ⟨.share f u G, Nat.add_lt_add_left less _, ?_⟩
      funext x
      simp only [SharedFormula.eval, equal]

private theorem someActiveBit (E : SharedFormula A) (s : Samples I A)
    (active : allActive E s) (k : ℕ) (inside : k < numShared E) :
    ∃ i, bitAt (profile E (s.one i)) k = true := by
  induction E generalizing k with
  | tree f => simp [numShared] at inside
  | share f u rest ih =>
    cases k with
    | zero => exact active.1
    | succ k =>
      have smaller : k < numShared rest := by simpa [numShared] using inside
      exact ih (s.add f) active.2 k smaller

private theorem bitAt_mem {bits : List Bool} {k : ℕ} (on : bitAt bits k = true) : true ∈ bits := by
  cases h : bits[k]? with
  | none => simp [bitAt, h] at on
  | some b =>
    have eq : b = true := by simpa [bitAt, h] using on
    exact eq ▸ List.mem_of_getElem? h

/-- The two reads of an input absent from the output must be in distinct
    shared stages for a ten-input circuit at the lower bound. -/
theorem hiddenStageAtMostOne (E : SharedFormula (Fin 10)) (valid : E.Valid)
    (test : ThresholdOn E.eval) (cost : gates E ≤ 23) (i : Fin 10) (k : ℕ)
    (raw : E.weight (ones i) ≤ 2) (absent : outputWeight E (ones i) = 0) :
    stageWeight E (ones i) k ≤ 1 := by
  by_contra! hDouble
  have elsewhere (l : ℕ) (ne : l ≠ k) : stageWeight E (ones i) l = 0 := by
    have bound := twoStagesAndOutput_le E (ones i) ne
    omega
  by_cases hot : true ∈ profile E (singletonInput i)
  · have same : firstHot E (singletonInput i) = k := by
      by_contra ne
      have positive := (firstHotFacts E _ hot).2
      change 1 ≤ stageWeight E (ones i) (firstHot E (singletonInput i)) at positive
      rw [elsewhere _ ne] at positive
      omega
    obtain ⟨F, less, equal⟩ := firstRepeatCheaper E i hot (by rw [same]; exact hDouble)
    have bound := tenRequires23 F (equal.symm ▸ test)
    omega
  · have inRange := stageWeight_pos E (ones i) k (by omega)
    obtain ⟨j, on⟩ := someActiveBit E (Samples.raw _) (tenAllActive E valid test cost) k inRange
    change bitAt (profile E (singletonInput j)) k = true at on
    have ne : i ≠ j := by
      intro eq
      subst j
      exact hot (bitAt_mem on)
    have blocked := (pairStable E i j (by
      intro l positive
      by_cases eq : l = k
      · simpa only [eq] using on
      · have z := elsewhere l eq
        omega)).2 absent
    rw [test.2 i j ne, test.1 j] at blocked
    contradiction

end CrownHiddenReads
