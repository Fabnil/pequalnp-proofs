import CrownFirstOr

namespace CrownFirstAnd

open CrownForks CrownForest CrownProfiles CrownVisibility CrownOrStages
open CrownFourNormal CrownFirstOr CrownForestCost CrownDropZero CrownSeparateOr PnpResearch
open CrownProfileThree.Network (ones)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

variable {A I : Type}

def signal (E : SharedFormula I) (k : ℕ) (x : I → Bool) : Bool :=
  bitAt (profile E x) k

/-- Two incomparable earlier disjunctions are simultaneously true. -/
def earlierOverlap [DecidableEq I] (E : SharedFormula I) (stage : ℕ) (i : I) : Prop :=
  ∃ j k, j < stage ∧ k < stage ∧ j ≠ k ∧
    signal E j (singletonInput i) = true ∧ signal E k (singletonInput i) = true ∧
    (¬ ∀ x, signal E j x ≤ signal E k x) ∧ (¬ ∀ x, signal E k x ≤ signal E j x)

def HasOverlapAt (k : ℕ) : Prop :=
  ∃ (p : Formula Ten) (q : Formula (Option Ten)) (r : Formula (Option (Option Ten)))
    (s : Formula (Option (Option (Option Ten)))) (h : Formula (Option (Option (Option (Option Ten))))),
    let E : SharedFormula Ten := .share p 1 (.share q 1 (.share r 1 (.share s 1 (.tree h))))
    orPrefix E k ∧ E.Valid ∧ ThresholdOn E.eval ∧ (∀ i, E.weight (ones i) = 2) ∧
      ∃ i, earlierOverlap E k i ∧ signal E k (singletonInput i) = true

private def namesArguments (E : SharedFormula I) (n : ℕ) (val : (I → Bool) → A → Bool) : Prop :=
  ∀ a, (∃ i, ∀ x, val x a = x i) ∨ (∃ k < n, ∀ x, val x a = signal E k x)

private theorem comparable [DecidableEq I] (E : SharedFormula I) (n : ℕ) (early : orPrefix E n)
    (val : (I → Bool) → A → Bool) (names : namesArguments E n val)
    (i : I) (disjoint : ¬ earlierOverlap E n i) (a b : A)
    (onA : val (singletonInput i) a = true) (onB : val (singletonInput i) b = true) :
    (∀ x, val x a ≤ val x b) ∨ (∀ x, val x b ≤ val x a) := by
  classical
  have atoms (z : A) : singletonDisjunction (fun x => val x z) := by
    rcases names z with ⟨k, raw⟩ | ⟨k, earlier, flag⟩
    · rw [funext raw]
      exact projection k
    · rw [funext flag]
      exact orStage E n early (fun x a => x a) projection k earlier
  have rawImplies (u v : A) (j : I) (raw : ∀ x, val x u = x j)
      (onU : val (singletonInput i) u = true) (onV : val (singletonInput i) v = true)
      (x : I → Bool) : val x u ≤ val x v := by
    have eq : j = i := by simpa [raw, singletonInput] using onU
    rw [raw, eq]
    exact Bool.le_iff_imp.mpr fun accepted => (atoms v x).mpr ⟨i, accepted, onV⟩
  rcases names a with ⟨j, raw⟩ | ⟨j, earlyJ, flagJ⟩
  · exact Or.inl (rawImplies a b j raw onA onB)
  · rcases names b with ⟨k, raw⟩ | ⟨k, earlyK, flagK⟩
    · exact Or.inr (rawImplies b a k raw onB onA)
    · by_cases lr : ∀ x, signal E j x ≤ signal E k x
      · exact Or.inl fun x => by rw [flagJ, flagK]; exact lr x
      · by_cases rl : ∀ x, signal E k x ≤ signal E j x
        · exact Or.inr fun x => by rw [flagJ, flagK]; exact rl x
        · have ne : j ≠ k := by
            intro eq
            subst k
            exact lr (fun _ => le_rfl)
          exact (disjoint ⟨j, k, earlyJ, earlyK, ne, (flagJ _).symm.trans onA,
            (flagK _).symm.trans onB, lr, rl⟩).elim

private def extend (val : (I → Bool) → A → Bool) (f : Formula A) (x : I → Bool) : Option A → Bool :=
  withHead (f.evalWith (val x)) (val x)

private theorem thirdOr (hyp : HasOrPrefix 2) : HasOverlapAt 2 ∨ HasOrPrefix 3 := by
  obtain ⟨p, q, r, s, h, early, valid, test, raw⟩ := hyp
  let rest := SharedFormula.share s 1 (.tree h)
  let E : SharedFormula Ten := .share p 1 (.share q 1 (.share r 1 rest))
  by_cases overlap : ∃ i, earlierOverlap E 2 i ∧ signal E 2 (singletonInput i) = true
  · exact Or.inl ⟨p, q, r, s, h, early, valid, test, raw, overlap⟩
  · let val := extend (extend (fun x : Ten → Bool => x) p) q
    have names : namesArguments E 2 val := by
      intro a
      rcases a with _ | _ | i
      · exact Or.inr ⟨1, by decide, fun _ => rfl⟩
      · exact Or.inr ⟨0, by decide, fun _ => rfl⟩
      · exact Or.inl ⟨i, fun _ => rfl⟩
    have size : gates E = 23 := fourWithTwoReadsCosts23 E valid raw rfl
    have active := tenAllActive E valid test size.le
    have off (i : Ten) (has : earlierOverlap E 2 i) : r.evalWith (val (singletonInput i)) = false :=
      Bool.eq_false_of_not_eq_true fun on => overlap ⟨i, has, on⟩
    rcases placeHead val (earlierOverlap E 2) (comparable E 2 early val names) r 1 rest
        valid.2.1.2.1 test active.2.2.1 off with ⟨g, fewer, equal⟩ | ⟨g, moved, pure, preserved⟩
    · let F : SharedFormula Ten := .share p 1 (.share q 1 (.share g 1 rest))
      have less : gates F < gates E := by simp only [F, E, gates]; omega
      have eq : F.eval = E.eval := funext equal
      have floor := tenRequires23 F (eq.symm ▸ test)
      omega
    · obtain ⟨out, shape⟩ : ∃ out, retime g moved 1 rest = .share g 1 (.share s 1 (.tree out)) := by
        cases moved <;> exact ⟨_, rfl⟩
      rw [shape] at preserved
      have qRest := Preserves.under ((Samples.raw Ten).add p) q 1 preserved valid.2.1
      have whole := Preserves.under (Samples.raw Ten) p 1 qRest valid
      exact Or.inr ⟨p, q, g, s, out, ⟨early.1, early.2.1, pure, trivial⟩, whole.valid,
        ⟨whole.off, whole.on⟩, fun i => (whole.weight _).trans (raw i)⟩

private theorem fourthOr (hyp : HasOrPrefix 3) : HasOverlapAt 3 ∨ HasOrPrefix 4 := by
  obtain ⟨p, q, r, s, h, early, valid, test, raw⟩ := hyp
  let rest := SharedFormula.tree h
  let E : SharedFormula Ten := .share p 1 (.share q 1 (.share r 1 (.share s 1 rest)))
  by_cases overlap : ∃ i, earlierOverlap E 3 i ∧ signal E 3 (singletonInput i) = true
  · exact Or.inl ⟨p, q, r, s, h, early, valid, test, raw, overlap⟩
  · let val := extend (extend (extend (fun x : Ten → Bool => x) p) q) r
    have names : namesArguments E 3 val := by
      intro a
      rcases a with _ | _ | _ | i
      · exact Or.inr ⟨2, by decide, fun _ => rfl⟩
      · exact Or.inr ⟨1, by decide, fun _ => rfl⟩
      · exact Or.inr ⟨0, by decide, fun _ => rfl⟩
      · exact Or.inl ⟨i, fun _ => rfl⟩
    have size : gates E = 23 := fourWithTwoReadsCosts23 E valid raw rfl
    have active := tenAllActive E valid test size.le
    have off (i : Ten) (has : earlierOverlap E 3 i) : s.evalWith (val (singletonInput i)) = false :=
      Bool.eq_false_of_not_eq_true fun on => overlap ⟨i, has, on⟩
    rcases placeHead val (earlierOverlap E 3) (comparable E 3 early val names) s 1 rest
        valid.2.1.2.1.2.1 test active.2.2.2.1 off with ⟨g, fewer, equal⟩ | ⟨g, moved, pure, preserved⟩
    · let F : SharedFormula Ten := .share p 1 (.share q 1 (.share r 1 (.share g 1 rest)))
      have less : gates F < gates E := by simp only [F, E, gates]; omega
      have eq : F.eval = E.eval := funext equal
      have floor := tenRequires23 F (eq.symm ▸ test)
      omega
    · obtain ⟨out, shape⟩ : ∃ out, retime g moved 1 rest = .share g 1 (.tree out) := by
        cases moved <;> exact ⟨_, rfl⟩
      rw [shape] at preserved
      have rRest := Preserves.under (((Samples.raw Ten).add p).add q) r 1 preserved valid.2.1.2.1
      have qRest := Preserves.under ((Samples.raw Ten).add p) q 1 rRest valid.2.1
      have whole := Preserves.under (Samples.raw Ten) p 1 qRest valid
      exact Or.inr ⟨p, q, r, g, out, ⟨early.1, early.2.1, early.2.2.1, pure, trivial⟩, whole.valid,
        ⟨whole.off, whole.on⟩, fun i => (whole.weight _).trans (raw i)⟩

/-- The two non-OR alternatives are distinguished by the position of an
    active stage above an incomparable pair. -/
theorem threeCasesOfOrPrefix (hyp : HasOrPrefix 2) :
    HasOverlapAt 2 ∨ HasOverlapAt 3 ∨ HasOrPrefix 4 := by
  rcases thirdOr hyp with hit | pure
  · exact Or.inl hit
  · exact Or.inr (fourthOr pure)

theorem crownTenThreeCases
    (small : RepSizeAtMost (fun u v : Ten => decide (u ≠ v)) 33) :
    HasOverlapAt 2 ∨ HasOverlapAt 3 ∨ HasOrPrefix 4 :=
  threeCasesOfOrPrefix (crownTenFirstTwoOr small)

end CrownFirstAnd
