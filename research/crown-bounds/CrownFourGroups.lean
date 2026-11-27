import CrownFullProfile

namespace CrownFourGroups

open CrownForks CrownPairFormula PnpResearch Finset

private abbrev Flag := Option (Fin 3)

variable {I : Type} [DecidableEq I]

def assignment (bits : Flag → Bool) (raw : I → Bool) : Flag ⊕ I → Bool :=
  Sum.elim bits raw

def IndependentTests (out : Formula (Flag ⊕ I)) (profile : I → Flag → Bool) : Prop :=
  (∀ i, out.evalWith (assignment (profile i) (singletonInput i)) = false) ∧
    ∀ i j, i ≠ j → out.evalWith
      (assignment (fun k => profile i k || profile j k) (pairInput i j)) = true

private theorem ignoreInput (f : Formula (Flag ⊕ I)) (bits : Flag → Bool)
    {x y : I → Bool} {i : I} (mono : ∀ k, x k ≤ y k)
    (change : (fun k => rise (x k) (y k)) = fun k => (singletonInput i k).toNat)
    (absent : reads f (.inr i) = 0) :
    f.evalWith (assignment bits y) = f.evalWith (assignment bits x) := by
  symm
  apply eqOfNoRise
  · intro k
    cases k with
    | inl k => exact le_rfl
    | inr k => exact mono k
  · have eq : (fun k => rise (assignment bits x k) (assignment bits y k)) =
        fun k => (singletonInput (Sum.inr i) k).toNat := by
      funext k
      cases k with
      | inl k => simp [assignment, singletonInput, rise]
      | inr k => simpa [assignment, singletonInput] using congrFun change k
    rw [eq]
    exact absent

private theorem removeSingleton (f : Formula (Flag ⊕ I)) (bits : Flag → Bool) (i : I)
    (absent : reads f (.inr i) = 0) :
    f.evalWith (assignment bits (singletonInput i)) = f.evalWith (assignment bits (fun _ => false)) :=
  ignoreInput f bits (fun _ => Bool.false_le _) (by funext k; simp [rise]) absent

private theorem removeFromPair (f : Formula (Flag ⊕ I)) (bits : Flag → Bool) {i j : I}
    (ne : i ≠ j) (absent : reads f (.inr i) = 0) :
    f.evalWith (assignment bits (pairInput i j)) = f.evalWith (assignment bits (singletonInput j)) :=
  ignoreInput f bits (TwoShared.otherSingleton_pair i j) (TwoShared.addedInputRise i j ne) absent

private def testAssignment (a : I) (x : Flag → Bool) : Flag ⊕ I → Bool
  | .inl none => true
  | .inl (some j) => x (some j)
  | .inr i => x none && decide (i = a)

private def testSamples (a : I) : Samples Flag (Flag ⊕ I) :=
  ⟨testAssignment a (fun _ => false), fun i => testAssignment a (singletonInput i),
    fun i j => testAssignment a (pairInput i j)⟩

private def varied (a : I) : Flag → Flag ⊕ I
  | none => .inr a
  | some j => .inl (some j)

private theorem testMono (a : I) : (testSamples a).onBase := by
  intro i k
  rcases k with (_ | _) | k <;> simp [testSamples, testAssignment]

private theorem testInitial (a : I) (i j : Flag) : (testSamples a).leafWitness [] i j := by
  intro k on offi offj
  have add : (testSamples a).two i j k = ((testSamples a).one i k || (testSamples a).one j k) := by
    rcases k with (_ | _) | k
    · rfl
    · rfl
    · by_cases h : k = a <;> simp [testSamples, testAssignment, pairInput, h]
  rw [add, offi, offj] at on
  contradiction

private theorem testWeight (a : I) (i : Flag) (f : Formula (Flag ⊕ I)) :
    leafWeight f ((testSamples a).riseAt i) = reads f (varied a i) := by
  unfold reads
  congr 1
  funext k
  rcases i with _ | i <;> rcases k with (_ | j) | k <;>
    simp [testSamples, Samples.riseAt, testAssignment, varied, singletonInput, rise]

private theorem fourTests (a : I) (f : Formula (Flag ⊕ I))
    (off : ∀ i, f.evalWith ((testSamples a).one i) = false)
    (on : ∀ i j, i ≠ j → f.evalWith ((testSamples a).two i j) = true)
    (aRead : reads f (.inr a) ≤ 1)
    (flagReads : ∀ j : Fin 3, reads f (.inl (some j)) ≤ 2) : False := by
  let s := testSamples a
  let limit (i : Flag) : ℕ := if i.isNone then 1 else 2
  have cap := CrownThreshold.weightedPacking (univ : Finset Flag) (rowCode (s.rows f)) limit 2
    (fun i _ j _ ne => by
      have found := Samples.outputSeparates (testMono a) (testInitial a i j) f (on i j ne) (off i) (off j)
      exact rowCodeSeparates (by simpa only [List.nil_append] using found))
    (fun i _ => by
      rw [fixedRowCode]
      have charge := s.charge (testMono a) f i
      rw [show s.riseAt i = (testSamples a).riseAt i from rfl, testWeight] at charge
      cases i with
      | none => exact le_trans (Nat.le_add_right ..) (charge.trans aRead)
      | some j => exact le_trans (Nat.le_add_right ..) (charge.trans (flagReads j)))
    (fun i _ => by cases i <;> simp [limit])
  have count : (∑ i : Flag, 2 ^ (2 - limit i)) = 5 := by decide +kernel
  rw [count] at cap
  omega

/-- A once-read raw input with one active flag is impossible when all three incident
    two-flag profiles are witnessed by raw inputs absent from the output formula. -/
theorem incidentDoubleProfilesImpossible (f : Formula (Flag ⊕ I)) (profile : I → Flag → Bool)
    (test : IndependentTests f profile) (a : I) (edge : Fin 3 → I)
    (one : profile a = withHead true (fun _ => false))
    (two : ∀ j, profile (edge j) = withHead true (singletonInput j))
    (edgeHidden : ∀ j, reads f (.inr (edge j)) = 0)
    (aRead : reads f (.inr a) ≤ 1)
    (flags : ∀ j : Fin 3, reads f (.inl (some j)) ≤ 2) : False := by
  have edgeNeA (j : Fin 3) : edge j ≠ a := by
    intro h
    have val := congrFun (congrArg profile h) (some j)
    rw [two j, one] at val
    simp [singletonInput] at val
  have edgeNe {j k : Fin 3} (ne : j ≠ k) : edge j ≠ edge k := by
    intro h
    have val := congrFun (congrArg profile h) (some j)
    rw [two j, two k] at val
    simp [singletonInput, ne] at val
  have singletonA : (testSamples a).one none = assignment (profile a) (singletonInput a) := by
    rw [one]
    funext k
    rcases k with (_ | j) | k <;> simp [testSamples, testAssignment, assignment, singletonInput]
  have singletonFlag (j : Fin 3) :
      (testSamples a).one (some j) = assignment (profile (edge j)) (fun _ => false) := by
    rw [two]
    funext k
    rcases k with (_ | k) | k <;> simp [testSamples, testAssignment, assignment, singletonInput]
  have aAndFlag (j : Fin 3) : (testSamples a).two none (some j) =
      assignment (fun k => profile (edge j) k || profile a k) (singletonInput a) := by
    rw [one, two]
    funext k
    rcases k with (_ | k) | k <;>
      simp [testSamples, testAssignment, assignment, pairInput, singletonInput]
  have twoFlags (j k : Fin 3) : (testSamples a).two (some j) (some k) =
      assignment (fun i => profile (edge j) i || profile (edge k) i) (fun _ => false) := by
    rw [two, two]
    funext u
    rcases u with (_ | l) | l <;> simp [testSamples, testAssignment, assignment, pairInput, singletonInput]
  refine fourTests a f ?_ ?_ aRead flags
  · intro j
    cases j with
    | none => rw [singletonA]; exact test.1 a
    | some j =>
      rw [singletonFlag j, ← removeSingleton f _ (edge j) (edgeHidden j)]
      exact test.1 (edge j)
  · have withA (j : Fin 3) : f.evalWith ((testSamples a).two none (some j)) = true := by
      rw [aAndFlag j, ← removeFromPair f _ (edgeNeA j) (edgeHidden j)]
      exact test.2 (edge j) a (edgeNeA j)
    intro j k ne
    rcases j with _ | j <;> rcases k with _ | k
    · exact (ne rfl).elim
    · exact withA k
    · have swap : pairInput (some j) (none : Flag) = pairInput none (some j) := by
        funext u
        exact Bool.or_comm _ _
      change f.evalWith (testAssignment a (pairInput (some j) none)) = true
      rw [swap]
      exact withA j
    · have hjk : j ≠ k := fun h => ne (congrArg some h)
      rw [twoFlags, ← removeSingleton f _ (edge k) (edgeHidden k),
        ← removeFromPair f _ (edgeNe hjk) (edgeHidden j)]
      exact test.2 (edge j) (edge k) (edgeNe hjk)

end CrownFourGroups
