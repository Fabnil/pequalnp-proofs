import CrownFirstAnd

namespace CrownOrReaders

open CrownForks CrownForest CrownProfiles CrownVisibility CrownOrStages CrownFourProfiles
open CrownFirstAnd PnpResearch
open CrownProfileThree.Network (ones)

variable {A J I : Type}

theorem orPrefix_mono (E : SharedFormula A) {j k : ℕ} (le : j ≤ k)
    (shape : orPrefix E k) : orPrefix E j := by
  induction E generalizing j k with
  | tree f =>
    cases k with
    | zero =>
      have same : j = 0 := by omega
      simpa only [same] using shape
    | succ k => exact shape.elim
  | share f extra rest ih =>
    cases j with
    | zero => trivial
    | succ j =>
      cases k with
      | zero => omega
      | succ k => exact ⟨shape.1, ih (by omega) shape.2⟩

theorem orOnly_on_iff [DecidableEq A] (f : Formula A) (shape : orOnly f) (x : A → Bool) :
    f.evalWith x = true ↔ ∃ a, 0 < leafWeight f (ones a) ∧ x a = true := by
  induction f with
  | var a =>
    constructor
    · intro yes
      exact ⟨a, by simp [leafWeight, ones, singletonInput], yes⟩
    · rintro ⟨b, reader, yes⟩
      have eq : a = b := by
        by_contra ne
        simp [leafWeight, ones, singletonInput, ne] at reader
      simpa only [Formula.evalWith, eq] using yes
  | conj l r il ir => exact shape.elim
  | disj l r il ir =>
    simp only [Formula.evalWith, Bool.or_eq_true, il shape.1, ir shape.2, leafWeight]
    constructor
    · rintro (⟨a, pos, on⟩ | ⟨a, pos, on⟩) <;> exact ⟨a, by omega, on⟩
    · rintro ⟨a, pos, on⟩
      by_cases found : 0 < leafWeight l (ones a)
      · exact Or.inl ⟨a, found, on⟩
      · exact Or.inr ⟨a, by omega, on⟩

/-- An active OR stage either directly reads an active original argument or
    contains an active earlier signal whose truth suffices to activate it. -/
theorem orStage_reason [deq : DecidableEq A] (E : SharedFormula A) (val : J → A → Bool)
    (x : J) (k : ℕ) (shape : orPrefix E (k + 1)) (active : signal E k (val x) = true) :
    (∃ a, 0 < stageWeight E (ones a) k ∧ val x a = true ∧ ∀ y, val y a ≤ signal E k (val y)) ∨
    ∃ j < k, signal E j (val x) = true ∧ ∀ y, signal E j (val y) ≤ signal E k (val y) := by
  revert deq
  induction E generalizing k with
  | tree f => intro _; exact shape.elim
  | share f extra rest ih =>
    intro deq
    cases k with
    | zero =>
      obtain ⟨a, read, on⟩ := (orOnly_on_iff f shape.1 (val x)).mp active
      exact Or.inl ⟨a, read, on, fun y => Bool.le_iff_imp.mpr fun h =>
        (orOnly_on_iff f shape.1 (val y)).mpr ⟨a, read, h⟩⟩
    | succ k =>
      let val' (y : J) := withHead (f.evalWith (val y)) (val y)
      have tailOn : signal rest k (val' x) = true := active
      rcases ih val' k shape.2 tailOn with ⟨a, read, on, implies⟩ | ⟨j, inside, on, implies⟩
      · cases a with
        | none => exact Or.inr ⟨0, by omega, on, implies⟩
        | some a =>
          have weights : ones (some a) = withHead 0 (ones a) := by
            funext b
            cases b <;> simp [ones, singletonInput]
          rw [weights] at read
          exact Or.inl ⟨a, read, on, implies⟩
      · exact Or.inr ⟨j + 1, by omega, on, implies⟩

theorem orStage_reads [DecidableEq I] (E : SharedFormula I) {i : I} {k : ℕ}
    (early : orPrefix E (k + 1)) (active : signal E k (singletonInput i) = true)
    (noPrior : ∀ j < k, signal E j (singletonInput i) = true → ¬ ∀ y, signal E j y ≤ signal E k y) :
    0 < stageWeight E (ones i) k := by
  rcases orStage_reason E (fun x : I → Bool => x) (singletonInput i) k early active with
    ⟨a, read, on, implies⟩ | ⟨j, inside, on, implies⟩
  · have eq : a = i := by simpa [singletonInput] using on
    exact eq ▸ read
  · exact (noPrior j inside on implies).elim

private theorem threeStages_le (E : SharedFormula A) (w : A → ℕ) {j k t : ℕ}
    (jk : j ≠ k) (jt : j ≠ t) (kt : k ≠ t) :
    stageWeight E w j + stageWeight E w k + stageWeight E w t ≤ E.weight w := by
  induction E generalizing j k t with
  | tree f => simp [stageWeight]
  | share f u rest ih =>
    cases j with
    | zero =>
      cases k with
      | zero => exact (jk rfl).elim
      | succ k =>
        cases t with
        | zero => exact (jt rfl).elim
        | succ t =>
          have tail := twoStagesAndOutput_le rest (withHead 0 w) (k := k) (l := t) (by omega)
          simp only [stageWeight, SharedFormula.weight]
          omega
    | succ j =>
      cases k with
      | zero =>
        cases t with
        | zero => exact (kt rfl).elim
        | succ t =>
          have tail := twoStagesAndOutput_le rest (withHead 0 w) (k := j) (l := t) (by omega)
          simp only [stageWeight, SharedFormula.weight]
          omega
      | succ k =>
        cases t with
        | zero =>
          have tail := twoStagesAndOutput_le rest (withHead 0 w) (k := j) (l := k) (by omega)
          simp only [stageWeight, SharedFormula.weight]
          omega
        | succ t =>
          have tail := ih (withHead 0 w) (j := j) (k := k) (t := t) (by omega) (by omega) (by omega)
          simp only [stageWeight, SharedFormula.weight]
          omega

/-- A singleton that activates the current stage and two incomparable earlier
    OR stages uses both of its reads before the current stage. -/
theorem readersOfOverlap (E : SharedFormula (Fin 10)) (valid : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ a, E.weight (ones a) ≤ 2) (four : numShared E = 4)
    {n j k : ℕ} (inside : n < 4) (early : orPrefix E n)
    (hj : j < n) (hk : k < n) (different : j ≠ k) (i : Fin 10)
    (onJ : signal E j (singletonInput i) = true) (onK : signal E k (singletonInput i) = true)
    (onN : signal E n (singletonInput i) = true)
    (jNotK : ¬ ∀ x, signal E j x ≤ signal E k x) (kNotJ : ¬ ∀ x, signal E k x ≤ signal E j x) :
    stageWeight E (ones i) j = 1 ∧ stageWeight E (ones i) k = 1 ∧ outputWeight E (ones i) = 0 ∧
      (∀ t < 4, t ≠ j → t ≠ k → t ≠ n → signal E t (singletonInput i) = false) ∧
      ∀ a, a ≠ i → ¬ (signal E j (singletonInput a) = true ∧ signal E k (singletonInput a) = true) := by
  have otherOff (t : ℕ) (range : t < 4) (tj : t ≠ j) (tk : t ≠ k) (tn : t ≠ n) :
      signal E t (singletonInput i) = false := by
    apply Bool.eq_false_of_not_eq_true
    intro onT
    have covers : full E (singletonInput i) := by
      intro a inRange
      rw [four] at inRange
      have options : a = j ∨ a = k ∨ a = t ∨ a = n := by omega
      rcases options with rfl | rfl | rfl | rfl
      · exact onJ
      · exact onK
      · exact onT
      · exact onN
    exact noFull E valid test raw (by decide) four i covers
  have earlier (t : ℕ) (lt : t < n) (onT : signal E t (singletonInput i) = true) : t = j ∨ t = k := by
    by_contra! distinct
    have off := otherOff t (lt.trans inside) distinct.1 distinct.2 (Nat.ne_of_lt lt)
    rw [onT] at off
    contradiction
  have readsJ := orStage_reads E (orPrefix_mono E (by omega) early) onJ (by
    intro t lt on
    rcases earlier t (lt.trans hj) on with rfl | rfl
    · omega
    · exact kNotJ)
  have readsK := orStage_reads E (orPrefix_mono E (by omega) early) onK (by
    intro t lt on
    rcases earlier t (lt.trans hk) on with rfl | rfl
    · exact jNotK
    · omega)
  have used := twoStagesAndOutput_le E (ones i) different
  have budget := raw i
  have absent : outputWeight E (ones i) = 0 := by omega
  refine ⟨by omega, by omega, absent, otherOff, ?_⟩
  intro a ne simultaneous
  have unchanged := (pairStable E i a (by
    intro t pos
    change signal E t (singletonInput a) = true
    by_cases tj : t = j
    · simpa only [tj] using simultaneous.1
    by_cases tk : t = k
    · simpa only [tk] using simultaneous.2
    have bound := threeStages_le E (ones i) different (fun h => tj h.symm) (fun h => tk h.symm)
    omega)).2 absent
  rw [test.2 i a ne.symm, test.1 a] at unchanged
  contradiction

end CrownOrReaders
