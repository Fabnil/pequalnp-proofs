import CrownFullProfile

namespace CrownProfileThree.Network

open CrownForks CrownProfiles CrownPairFormula PnpResearch Finset

variable {I : Type} [DecidableEq I]

def formulaAt (N : Network I) (k : Fin 4) : Formula (Option (Option (Option I))) :=
  if k = 0 then rename N.first rawKey
  else if k = 1 then rename N.second (fun a => some (some a))
  else if k = 2 then rename N.third some
  else N.output

def atProfile (N : Network I) (k : Fin 4) (b : Bool × Bool × Bool) (x : I → Bool) : Bool :=
  (N.formulaAt k).evalWith (supply b x)

def rawAt (N : Network I) (k : Fin 4) (i : I) : ℕ :=
  reads (N.formulaAt k) (rawKey i)

omit [DecidableEq I] in
private theorem at_eq (N : Network I) (k : Fin 4) (b : Bool × Bool × Bool) (x : I → Bool) :
    N.atProfile k b x = if k = 0 then N.first.evalWith x
      else if k = 1 then N.second.evalWith (withHead b.1 x)
      else if k = 2 then N.third.evalWith (withHead b.2.1 (withHead b.1 x))
      else N.output.evalWith (supply b x) := by
  unfold atProfile formulaAt
  split
  · rw [eval_rename]
    rfl
  · split
    · rw [eval_rename]
      rfl
    · split
      · rw [eval_rename]
        rfl
      · rfl

omit [DecidableEq I] in
theorem atActual (N : Network I) (x : I → Bool) (k : Fin 4) (h : k ≠ 3) :
    N.atProfile k (N.bits x) x = flag (N.bits x) k := by
  fin_cases k <;> rw [at_eq] <;> first | rfl | contradiction

omit [DecidableEq I] in
theorem atOutput (N : Network I) (x : I → Bool) :
    N.atProfile 3 (N.bits x) x = N.forest.eval x := rfl

omit [DecidableEq I] in
theorem atMono (N : Network I) (k : Fin 4) {b c : Bool × Bool × Bool} {x y : I → Bool}
    (prior : ∀ h < k, flag b h ≤ flag c h) (raw : ∀ i, x i ≤ y i) :
    N.atProfile k b x ≤ N.atProfile k c y := by
  simp only [at_eq]
  fin_cases k
  · exact evalMono N.first raw
  · exact evalMono N.second (withHeadMono (prior 0 (by decide)) raw)
  · exact evalMono N.third (withHeadMono (prior 1 (by decide))
      (withHeadMono (prior 0 (by decide)) raw))
  · exact evalMono N.output (withHeadMono (prior 2 (by decide))
      (withHeadMono (prior 1 (by decide)) (withHeadMono (prior 0 (by decide)) raw)))

omit [DecidableEq I] in
theorem atSamePrefix (N : Network I) (k : Fin 4) {b c : Bool × Bool × Bool} (x : I → Bool)
    (prior : ∀ h < k, flag b h = flag c h) : N.atProfile k b x = N.atProfile k c x :=
  le_antisymm (N.atMono k (fun h lt => (prior h lt).le) (fun _ => le_rfl))
    (N.atMono k (fun h lt => (prior h lt).symm.le) (fun _ => le_rfl))

theorem raw_eq (N : Network I) (i : I) :
    N.rawAt 0 i = N.firstRaw i ∧ N.rawAt 1 i = N.secondRaw i ∧
      N.rawAt 2 i = N.thirdRaw i ∧ N.rawAt 3 i = N.outputRaw i := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change leafWeight (rename N.first rawKey) _ = _
    rw [weight_rename]
    congr 1
    funext a
    simp [singletonInput, ones]
  · change leafWeight (rename N.second (fun a => some (some a))) _ = _
    rw [weight_rename]
    congr 1
    funext a
    cases a <;> simp [singletonInput, ones]
  · change leafWeight (rename N.third some) _ = _
    rw [weight_rename]
    congr 1
    funext a
    rcases a with _ | _ | a <;> simp [singletonInput, ones]
  · change leafWeight N.output _ = _
    unfold outputRaw
    congr 1
    funext a
    rcases a with _ | _ | _ | a <;> simp [singletonInput, ones]

theorem rawTotal (N : Network I) (i : I) :
    ∑ k : Fin 4, N.rawAt k i = N.forest.weight (ones i) := by
  obtain ⟨h0, h1, h2, h3⟩ := N.raw_eq i
  rw [Fin.sum_univ_four, h0, h1, h2, h3, weight_eq]

theorem firstRawNeeded (N : Network I) {i : I} (h : firstStage (N.bits (singletonInput i)) ≠ 3) :
    1 ≤ N.rawAt (firstStage (N.bits (singletonInput i))) i := by
  obtain ⟨h0, h1, h2, _⟩ := N.raw_eq i
  rcases N.firstStageRead h with ⟨e, r⟩ | ⟨e, r⟩ | ⟨e, r⟩
  · rwa [e, h0]
  · rwa [e, h1]
  · rwa [e, h2]

theorem rawAtTwo (N : Network I) {i : I} {s t : Fin 4} (st : s ≠ t)
    (reads : N.forest.weight (ones i) ≤ 2) (rs : 1 ≤ N.rawAt s i) (rt : 1 ≤ N.rawAt t i) :
    N.rawAt t i = 1 ∧ ∀ k, k ≠ s → k ≠ t → N.rawAt k i = 0 := by
  rw [← rawTotal] at reads
  have bound (S : Finset (Fin 4)) : ∑ k ∈ S, N.rawAt k i ≤ 2 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => Nat.zero_le _)).trans reads
  have two := bound {s, t}
  rw [sum_insert (by simp [st]), sum_singleton] at two
  refine ⟨by omega, ?_⟩
  intro k ks kt
  have three := bound {k, s, t}
  rw [sum_insert (by simp [ks, kt]), sum_insert (by simp [st]), sum_singleton] at three
  omega

private theorem rawWeight (i : I) : (fun a => (singletonInput (rawKey i) a).toNat) =
    withHead 0 (withHead 0 (withHead 0 (ones i))) := by
  funext a
  rcases a with _ | _ | _ | a <;> simp [singletonInput, ones]

theorem addIgnored (N : Network I) (k : Fin 4) (b : Bool × Bool × Bool)
    {i j : I} (ne : i ≠ j) (absent : N.rawAt k i = 0) :
    N.atProfile k b (pairInput i j) = N.atProfile k b (singletonInput j) := by
  unfold atProfile
  symm
  apply eqOfNoRise
  · exact withHeadMono le_rfl (withHeadMono le_rfl (withHeadMono le_rfl (TwoShared.otherSingleton_pair i j)))
  · have mass : (fun a => rise (supply b (singletonInput j) a) (supply b (pairInput i j) a)) =
        withHead 0 (withHead 0 (withHead 0 (ones i))) := by
      funext a
      rcases a with _ | _ | _ | a
      · simp [supply, rise]
      · simp [supply, rise]
      · simp [supply, rise]
      · exact congrFun (TwoShared.addedInputRise i j ne) a
    rwa [mass, ← rawWeight]

theorem zeroIgnored (N : Network I) (k : Fin 4) (b : Bool × Bool × Bool) {i : I}
    (absent : N.rawAt k i = 0) :
    N.atProfile k b (singletonInput i) = N.atProfile k b (fun _ => false) := by
  unfold atProfile
  symm
  apply eqOfNoRise
  · exact withHeadMono le_rfl (withHeadMono le_rfl (withHeadMono le_rfl (fun _ => Bool.false_le _)))
  · have mass : (fun a => rise (supply b (fun _ => false) a) (supply b (singletonInput i) a)) =
        withHead 0 (withHead 0 (withHead 0 (ones i))) := by
      funext a
      rcases a with _ | _ | _ | a <;> simp [supply, rise, ones]
    rwa [mass, ← rawWeight]

omit [DecidableEq I] in
theorem profileMono (N : Network I) {x y : I → Bool} (mono : ∀ i, x i ≤ y i) (k : Fin 4) :
    flag (N.bits x) k ≤ flag (N.bits y) k := by
  fin_cases k
  · exact N.signals_mono mono (some (some none))
  · exact N.signals_mono mono (some none)
  · exact N.signals_mono mono none
  · exact le_rfl

end CrownProfileThree.Network
