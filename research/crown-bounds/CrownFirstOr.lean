import CrownSeparateOr
import CrownReadSupport

namespace CrownFirstOr

open CrownForks CrownForest CrownForestCost CrownFourNormal CrownOrStages
open CrownDropZero CrownFactorAnd CrownSeparateOr PnpResearch
open CrownProfileThree.Network (ones)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

variable {A I : Type}

def pullSamples [DecidableEq I] (val : (I → Bool) → A → Bool) : Samples I A :=
  ⟨val (fun _ => false), fun i => val (singletonInput i), fun i j => val (pairInput i j)⟩

theorem placeHeadUsing [DecidableEq I] (val : (I → Bool) → A → Bool) (except : I → Prop) (f : Formula A)
    (compare : ∀ i, ¬ except i → ∀ a b, CrownReadSupport.Uses f a → CrownReadSupport.Uses f b →
      val (singletonInput i) a = true → val (singletonInput i) b = true →
      (∀ x, val x a ≤ val x b) ∨ (∀ x, val x b ≤ val x a))
    (extra : ℕ) (rest : SharedFormula (Option A))
    (valid : (SharedFormula.share f extra rest).Valid)
    (test : ThresholdOn (fun x => (SharedFormula.share f extra rest).eval (val x)))
    (active : ∃ i, f.evalWith (val (singletonInput i)) = true)
    (offAtExceptions : ∀ i, except i → f.evalWith (val (singletonInput i)) = false) :
    (∃ g : Formula A, formulaGates g < formulaGates f ∧
      ∀ x, (SharedFormula.share g extra rest).eval (val x) =
        (SharedFormula.share f extra rest).eval (val x)) ∨
    ∃ p q, orOnly p ∧ Preserves (pullSamples val) (.share f extra rest) (retime p q extra rest) := by
  obtain ⟨g, equal, proof⟩ := CrownReadSupport.normalizeUsed val
    (fun x => ∃ i, ¬ except i ∧ x = singletonInput i) f
    (fun _ hx => by obtain ⟨i, included, rfl⟩ := hx; exact compare i included)
  have same (x : I → Bool) : (SharedFormula.share g extra rest).eval (val x) =
      (SharedFormula.share f extra rest).eval (val x) := by
    simp only [SharedFormula.eval, equal x]
  rcases proof with fewer | ⟨size, mass, idle⟩
  · exact Or.inl ⟨g, fewer, same⟩
  · obtain ⟨i, pos⟩ := active
    have sampleActive : ∃ i, g.evalWith ((pullSamples val).one i) = true :=
      ⟨i, (equal (singletonInput i)).trans pos⟩
    have off' (i : I) : (SharedFormula.share g extra rest).eval ((pullSamples val).one i) = false :=
      (same (singletonInput i)).trans (test.1 i)
    have on' (i j : I) (ne : i ≠ j) :
        (SharedFormula.share g extra rest).eval ((pullSamples val).two i j) = true :=
      (same (pairInput i j)).trans (test.2 i j ne)
    have termsOff (i : I) : formulaEval (splitTop g).2 ((pullSamples val).one i) = false := by
      by_cases excluded : except i
      · have split := splitTop_eval g (val (singletonInput i))
        rw [equal (singletonInput i), offAtExceptions i excluded] at split
        exact (Bool.or_eq_false_iff.mp split).2
      · exact splitTop_off g _ (idle (singletonInput i) ⟨i, excluded, rfl⟩)
    obtain ⟨p, q, onlyOr, preserved⟩ :=
      movePassiveAnds (pullSamples val) g extra rest termsOff sampleActive valid off' on'
    refine Or.inr ⟨p, q, onlyOr, ⟨preserved.valid, ?_, ?_, preserved.off, preserved.on⟩⟩
    · rw [preserved.cost]
      simp only [gates, size]
    · intro w
      rw [preserved.weight]
      simp only [SharedFormula.weight, mass]

theorem placeHead [DecidableEq I] (val : (I → Bool) → A → Bool) (except : I → Prop)
    (compare : ∀ i, ¬ except i → ∀ a b, val (singletonInput i) a = true → val (singletonInput i) b = true →
      (∀ x, val x a ≤ val x b) ∨ (∀ x, val x b ≤ val x a))
    (f : Formula A) (extra : ℕ) (rest : SharedFormula (Option A))
    (valid : (SharedFormula.share f extra rest).Valid)
    (test : ThresholdOn (fun x => (SharedFormula.share f extra rest).eval (val x)))
    (active : ∃ i, f.evalWith (val (singletonInput i)) = true)
    (offAtExceptions : ∀ i, except i → f.evalWith (val (singletonInput i)) = false) :
    (∃ g : Formula A, formulaGates g < formulaGates f ∧
      ∀ x, (SharedFormula.share g extra rest).eval (val x) =
        (SharedFormula.share f extra rest).eval (val x)) ∨
    ∃ p q, orOnly p ∧ Preserves (pullSamples val) (.share f extra rest) (retime p q extra rest) :=
  placeHeadUsing val except f (fun i good a b _ _ => compare i good a b) extra rest
    valid test active offAtExceptions

private theorem compareRaw [DecidableEq I] (i a b : I)
    (ha : singletonInput i a = true) (hb : singletonInput i b = true) :
    (∀ x : I → Bool, x a ≤ x b) ∨ (∀ x : I → Bool, x b ≤ x a) := by
  have ai : a = i := by simpa [singletonInput] using ha
  have bi : b = i := by simpa [singletonInput] using hb
  subst a
  subst b
  exact Or.inl fun _ => le_rfl

private def afterOr (p : Formula I) (x : I → Bool) : Option I → Bool :=
  withHead (p.evalWith x) x

private theorem compareAfterOr [DecidableEq I] (p : Formula I) (pure : orOnly p)
    (i : I) (a b : Option I)
    (ha : afterOr p (singletonInput i) a = true) (hb : afterOr p (singletonInput i) b = true) :
    (∀ x, afterOr p x a ≤ afterOr p x b) ∨ (∀ x, afterOr p x b ≤ afterOr p x a) := by
  have signal := eval_orOnly p (fun x k => x k) pure projection
  have rawImplies (j : I) (hj : singletonInput i j = true)
      (on : p.evalWith (singletonInput i) = true) (x : I → Bool) : x j ≤ p.evalWith x := by
    have eq : j = i := by simpa [singletonInput] using hj
    subst j
    exact Bool.le_iff_imp.mpr fun accepted => (signal x).mpr ⟨i, accepted, on⟩
  cases a with
  | none =>
    cases b with
    | none => exact Or.inl fun _ => le_rfl
    | some b => exact Or.inr (rawImplies b hb ha)
  | some a =>
    cases b with
    | none => exact Or.inl (rawImplies a ha hb)
    | some b => exact compareRaw i a b ha hb

def HasOrPrefix (k : ℕ) : Prop :=
  ∃ (p : Formula Ten) (q : Formula (Option Ten)) (r : Formula (Option (Option Ten)))
    (s : Formula (Option (Option (Option Ten)))) (h : Formula (Option (Option (Option (Option Ten))))),
    let E : SharedFormula Ten := .share p 1 (.share q 1 (.share r 1 (.share s 1 (.tree h))))
    orPrefix E k ∧ E.Valid ∧ ThresholdOn E.eval ∧ ∀ i, E.weight (ones i) = 2

private theorem firstOr (hyp : HasFourSharedThreshold) : HasOrPrefix 1 := by
  obtain ⟨p, q, r, s, h, valid, test, reads⟩ := hyp
  let rest := SharedFormula.share q 1 (.share r 1 (.share s 1 (.tree h)))
  let E : SharedFormula Ten := .share p 1 rest
  have size : gates E = 23 := fourWithTwoReadsCosts23 E valid reads rfl
  have active := tenAllActive E valid test size.le
  rcases placeHead (fun x : Ten → Bool => x) (fun _ => False) (fun i _ => compareRaw i)
      p 1 rest valid test active.1 (fun _ impossible => impossible.elim) with
    ⟨g, fewer, equal⟩ | ⟨g, moved, pure, preserved⟩
  · let F : SharedFormula Ten := .share g 1 rest
    have less : gates F < gates E := Nat.add_lt_add_right fewer _
    have eq : F.eval = E.eval := funext equal
    have floor := tenRequires23 F (eq.symm ▸ test)
    omega
  · obtain ⟨out, shape⟩ : ∃ out, retime g moved 1 rest =
        .share g 1 (.share q 1 (.share r 1 (.share s 1 (.tree out)))) := by
      cases moved <;> exact ⟨_, rfl⟩
    rw [shape] at preserved
    refine ⟨g, q, r, s, out, ⟨pure, trivial⟩, preserved.valid, ⟨preserved.off, preserved.on⟩, ?_⟩
    intro i
    rw [preserved.weight]
    exact reads i

private theorem secondOr (hyp : HasOrPrefix 1) : HasOrPrefix 2 := by
  obtain ⟨p, q, r, s, h, prefixOr, valid, test, reads⟩ := hyp
  let rest := SharedFormula.share r 1 (.share s 1 (.tree h))
  let E : SharedFormula Ten := .share p 1 (.share q 1 rest)
  have size : gates E = 23 := fourWithTwoReadsCosts23 E valid reads rfl
  have active := tenAllActive E valid test size.le
  rcases placeHead (afterOr p) (fun _ => False) (fun i _ => compareAfterOr p prefixOr.1 i)
      q 1 rest valid.2.1 test active.2.1 (fun _ impossible => impossible.elim) with
    ⟨g, fewer, equal⟩ | ⟨g, moved, pure, preserved⟩
  · let F : SharedFormula Ten := .share p 1 (.share g 1 rest)
    have less : gates F < gates E := Nat.add_lt_add_left (Nat.add_lt_add_right fewer _) _
    have eq : F.eval = E.eval := funext equal
    have floor := tenRequires23 F (eq.symm ▸ test)
    omega
  · obtain ⟨out, shape⟩ : ∃ out, retime g moved 1 rest =
        .share g 1 (.share r 1 (.share s 1 (.tree out))) := by
      cases moved <;> exact ⟨_, rfl⟩
    rw [shape] at preserved
    refine ⟨p, g, r, s, out, ⟨prefixOr.1, pure, trivial⟩,
      ⟨valid.1, preserved.valid, ?_⟩, ⟨preserved.off, preserved.on⟩, ?_⟩
    · rw [preserved.weight]
      exact valid.2.2
    · intro i
      change leafWeight p (ones i) +
        (SharedFormula.share g 1 (.share r 1 (.share s 1 (.tree out)))).weight (withHead 0 (ones i)) = 2
      rw [preserved.weight]
      exact reads i

theorem firstTwoOr (hyp : HasFourSharedThreshold) : HasOrPrefix 2 :=
  secondOr (firstOr hyp)

theorem crownTenFirstTwoOr
    (small : RepSizeAtMost (fun u v : Ten => decide (u ≠ v)) 33) : HasOrPrefix 2 :=
  firstTwoOr (crownTenRequiresFour small)

end CrownFirstOr
