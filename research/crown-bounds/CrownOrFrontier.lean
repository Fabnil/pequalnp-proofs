import CrownFirstOr
import CrownFourProfiles

namespace CrownOrFrontier

open CrownForks CrownForest CrownForestCost CrownFourProfiles CrownSeparateOr
open CrownOrStages CrownFirstOr CrownDropZero CrownReadSupport PnpResearch

variable {I A : Type} [DecidableEq I]

private def supply (val : (I → Bool) → A → Bool) (f : Formula A) (x : I → Bool) : Option A → Bool :=
  withHead (f.evalWith (val x)) (val x)

/-- At this singleton, the formula reads two incomparable signals that are
    both true. -/
def Overlap (val : (I → Bool) → A → Bool) (f : Formula A) (i : I) : Prop :=
  ∃ a b, Uses f a ∧ Uses f b ∧ val (singletonInput i) a = true ∧
    val (singletonInput i) b = true ∧ (¬ ∀ x, val x a ≤ val x b) ∧ (¬ ∀ x, val x b ≤ val x a)

/-- Follow the OR stages until the first remaining stage that is not an OR.
    Such a stage has an active singleton with overlapping read signals. -/
def Prepared {A : Type} (val : (I → Bool) → A → Bool) : SharedFormula A → Prop
  | .tree _ => True
  | .share f _ rest =>
    (orOnly f ∧ Prepared (supply val f) rest) ∨
      (¬ orOnly f ∧ ∃ i, Overlap val f i ∧ f.evalWith (val (singletonInput i)) = true)

def StagePrepared (val : (I → Bool) → A → Bool) (f : Formula A) : Prop :=
  orOnly f ∨ (¬ orOnly f ∧ ∃ i, Overlap val f i ∧ f.evalWith (val (singletonInput i)) = true)

/-- Carry the same normalization through every shared stage. -/
def AllPrepared {A : Type} (val : (I → Bool) → A → Bool) : SharedFormula A → Prop
  | .tree _ => True
  | .share f _ rest => StagePrepared val f ∧ AllPrepared (supply val f) rest

theorem AllPrepared.first {E : SharedFormula A} {val : (I → Bool) → A → Bool}
    (all : AllPrepared val E) : Prepared val E := by
  induction E with
  | tree f => trivial
  | share f extra rest ih =>
    rcases all.1 with pure | overlap
    · exact Or.inl ⟨pure, ih all.2⟩
    · exact Or.inr overlap

def copies {A : Type} : SharedFormula A → List ℕ
  | .tree _ => []
  | .share _ extra rest => extra :: copies rest

private theorem copies_length (E : SharedFormula A) : (copies E).length = numShared E := by
  induction E <;> simp [copies, numShared, *]

private theorem copies_appendOr (E : SharedFormula A) (f : Formula A) :
    copies (CrownMoveOr.appendOr E f) = copies E := by
  induction E <;> simp [copies, CrownMoveOr.appendOr, *]

private theorem retime_tail (p : Formula A) (terms : Option (Formula A)) (extra : ℕ)
    (rest : SharedFormula (Option A)) :
    ∃ tail, retime p terms extra rest = .share p extra tail ∧ copies tail = copies rest := by
  cases terms with
  | none => exact ⟨rest, rfl, rfl⟩
  | some q => exact ⟨_, rfl, copies_appendOr rest (rename q some)⟩

/-- The comparisons are against any formula with the same singleton and pair
    tests in the given context. Validity of the competitor is unnecessary. -/
def Minimum (val : (I → Bool) → A → Bool) (E : SharedFormula A) : Prop :=
  ∀ G : SharedFormula A, ThresholdOn (fun x => G.eval (val x)) → gates E ≤ gates G

private theorem unchanged (val : (I → Bool) → A → Bool) (E : SharedFormula A)
    (valid : E.Valid) (test : ThresholdOn (fun x => E.eval (val x))) :
    Preserves (pullSamples val) E E :=
  ⟨valid, rfl, fun _ => rfl, test.1, test.2⟩

private theorem prepareByCount (fuel : ℕ) :
    ∀ {A : Type} (val : (I → Bool) → A → Bool) (E : SharedFormula A),
      numShared E ≤ fuel → E.Valid → ThresholdOn (fun x => E.eval (val x)) → Minimum val E →
      ∃ G, Preserves (pullSamples val) E G ∧ copies G = copies E ∧ AllPrepared val G := by
  classical
  induction fuel with
  | zero =>
    intro A val E size valid tests minimal
    cases E with
    | tree f => exact ⟨.tree f, unchanged val _ valid tests, rfl, trivial⟩
    | share f extra rest => simp [numShared] at size
  | succ fuel ih =>
    intro A val E size valid tests minimal
    cases E with
    | tree f => exact ⟨.tree f, unchanged val _ valid tests, rfl, trivial⟩
    | share f extra rest =>
      let before : SharedFormula A := .share f extra rest
      have follow (p : Formula A) (tail : SharedFormula (Option A)) (head : StagePrepared val p)
          (stages : copies tail = copies rest)
          (keeps : Preserves (pullSamples val) before (.share p extra tail)) :
          ∃ G, Preserves (pullSamples val) before G ∧ copies G = copies before ∧ AllPrepared val G := by
        have shape : numShared tail = numShared rest := by
          simpa only [copies_length] using congrArg List.length stages
        have bound : numShared tail ≤ fuel := by
          simp only [numShared] at size
          omega
        have restMinimum : Minimum (supply val p) tail := by
          intro G passes
          have smaller := minimal (.share p extra G) passes
          change gates before ≤ _ at smaller
          rw [← keeps.cost] at smaller
          simpa only [gates, Nat.add_le_add_iff_left] using smaller
        obtain ⟨U, after, count, done⟩ := ih (supply val p) tail bound keeps.valid.2.1
          ⟨keeps.off, keeps.on⟩ restMinimum
        have lifted := Preserves.under (pullSamples val) p extra after keeps.valid
        refine ⟨.share p extra U, ?_, ?_, ⟨head, done⟩⟩
        · exact ⟨lifted.valid, lifted.cost.trans keeps.cost,
            fun w => (lifted.weight w).trans (keeps.weight w), lifted.off, lifted.on⟩
        · simp only [copies, count, stages, before]
      by_cases pure : orOnly f
      · exact follow f rest (Or.inl pure) rfl (unchanged val before valid tests)
      by_cases overlap : ∃ i, Overlap val f i ∧ f.evalWith (val (singletonInput i)) = true
      · exact follow f rest (Or.inr ⟨pure, overlap⟩) rfl (unchanged val before valid tests)
      have compare (i : I) (good : ¬ Overlap val f i) (a b : A) (ra : Uses f a) (rb : Uses f b)
          (ona : val (singletonInput i) a = true) (onb : val (singletonInput i) b = true) :
          (∀ x, val x a ≤ val x b) ∨ (∀ x, val x b ≤ val x a) := by
        by_cases ab : ∀ x, val x a ≤ val x b
        · exact Or.inl ab
        by_cases ba : ∀ x, val x b ≤ val x a
        · exact Or.inr ba
        exact (good ⟨a, b, ra, rb, ona, onb, ab, ba⟩).elim
      have active : ∃ i, f.evalWith (val (singletonInput i)) = true := by
        rcases activeOrCheaper before (pullSamples val) valid tests.1 tests.2 with every | ⟨G, cheaper, passes⟩
        · exact every.1
        · exact (not_lt_of_ge (minimal G ⟨passes.1, passes.2⟩) cheaper).elim
      rcases placeHeadUsing val (Overlap val f) f compare extra rest valid tests active
          (fun i hit => Bool.eq_false_of_not_eq_true fun on => overlap ⟨i, hit, on⟩) with
        ⟨g, cheaper, eval⟩ | ⟨p, terms, only, preserves⟩
      · let G : SharedFormula A := .share g extra rest
        have below : gates G < gates before := Nat.add_lt_add_right cheaper _
        have works : ThresholdOn (fun x => G.eval (val x)) :=
          ⟨fun i => (eval _).trans (tests.1 i), fun i j ne => (eval _).trans (tests.2 i j ne)⟩
        exact (not_lt_of_ge (minimal G works) below).elim
      · obtain ⟨tail, eq, stages⟩ := retime_tail p terms extra rest
        rw [eq] at preserves
        exact follow p tail (Or.inl only) stages preserves

theorem prepareAll (val : (I → Bool) → A → Bool) (E : SharedFormula A)
    (valid : E.Valid) (test : ThresholdOn (fun x => E.eval (val x))) (minimal : Minimum val E) :
    ∃ G, Preserves (pullSamples val) E G ∧ copies G = copies E ∧ AllPrepared val G :=
  prepareByCount (numShared E) val E le_rfl valid test minimal

theorem prepare (val : (I → Bool) → A → Bool) (E : SharedFormula A)
    (valid : E.Valid) (test : ThresholdOn (fun x => E.eval (val x))) (minimal : Minimum val E) :
    ∃ G, Preserves (pullSamples val) E G ∧ copies G = copies E ∧ Prepared val G := by
  obtain ⟨G, preserves, count, done⟩ := prepareAll val E valid test minimal
  exact ⟨G, preserves, count, done.first⟩

end CrownOrFrontier
