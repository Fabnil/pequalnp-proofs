import CrownProfileThree
import CrownPairFormula

namespace CrownProfileThree.Network

open CrownForks CrownProfiles CrownPairFormula PnpResearch Finset

variable {I : Type} [DecidableEq I]

def firstStage (b : Bool × Bool × Bool) : Fin 4 :=
  if b.1 then 0 else if b.2.1 then 1 else if b.2.2 then 2 else 3

def flag (b : Bool × Bool × Bool) (k : Fin 4) : Bool :=
  if k = 0 then b.1 else if k = 1 then b.2.1 else if k = 2 then b.2.2 else false

theorem stageActive : ∀ b : Bool × Bool × Bool,
    firstStage b ≠ 3 → flag b (firstStage b) = true := by decide +kernel

private theorem fullActive : ∀ k : Fin 4,
    k ≠ 3 → flag (true, true, true) k = true := by decide +kernel

private theorem coldStage : ∀ b : Bool × Bool × Bool,
    firstStage b = 3 → load b = 0 := by decide +kernel

private theorem headToNat {A : Type} (x : A → Bool) :
    (fun a => (withHead false x a).toNat) = withHead 0 (fun a => (x a).toNat) := by
  funext a
  cases a <;> rfl

theorem firstStageRead (N : Network I) {i : I}
    (warm : firstStage (N.bits (singletonInput i)) ≠ 3) :
    let k := firstStage (N.bits (singletonInput i))
    (k = 0 ∧ 1 ≤ N.firstRaw i) ∨ (k = 1 ∧ 1 ≤ N.secondRaw i) ∨ (k = 2 ∧ 1 ≤ N.thirdRaw i) := by
  change _ ∨ _ ∨ _
  by_cases hp : N.first.evalWith (singletonInput i) = true
  · exact Or.inl ⟨by simp [firstStage, bits, signals, hp], readsOfTrue _ _ hp⟩
  · have p : N.first.evalWith (singletonInput i) = false := Bool.eq_false_iff.mpr hp
    by_cases hq : N.second.evalWith (withHead false (singletonInput i)) = true
    · have read := readsOfTrue _ _ hq
      rw [headToNat] at read
      exact Or.inr (Or.inl ⟨by simp [firstStage, bits, signals, p, hq], read⟩)
    · have q : N.second.evalWith (withHead false (singletonInput i)) = false :=
        Bool.eq_false_iff.mpr hq
      have hr : N.third.evalWith (withHead false (withHead false (singletonInput i))) = true := by
        by_contra! off
        have z := Bool.eq_false_iff.mpr off
        exact warm (by simp [firstStage, bits, signals, p, q, z])
      have read := readsOfTrue _ _ hr
      simp only [headToNat] at read
      exact Or.inr (Or.inr ⟨by simp [firstStage, bits, signals, p, q, hr], read⟩)

theorem onlyFirstStageAndOutput (N : Network I) (i : I)
    (warm : firstStage (N.bits (singletonInput i)) ≠ 3) (out : 1 ≤ N.outputRaw i)
    (twice : N.forest.weight (ones i) ≤ 2) :
    let k := firstStage (N.bits (singletonInput i))
    N.outputRaw i = 1 ∧ (k ≠ 0 → N.firstRaw i = 0) ∧
      (k ≠ 1 → N.secondRaw i = 0) ∧ (k ≠ 2 → N.thirdRaw i = 0) := by
  dsimp only
  rw [weight_eq] at twice
  rcases N.firstStageRead warm with ⟨stage, h⟩ | ⟨stage, h⟩ | ⟨stage, h⟩ <;>
    rw [stage] <;> refine ⟨by omega, ?_, ?_, ?_⟩ <;>
    exact fun _ => by omega

private theorem evalUnchanged {A : Type} (f : Formula A) {u v : A → Bool}
    (mono : ∀ a, u a ≤ v a)
    (h : f.evalWith u = true ∨ leafWeight f (fun a => rise (u a) (v a)) = 0) :
    f.evalWith v = f.evalWith u := by
  rcases h with on | zero
  · exact ((Bool.le_iff_imp.mp (evalMono f mono)) on).trans on.symm
  · exact (eqOfNoRise f mono zero).symm

theorem stableWhenAlreadyActive (N : Network I) {i j : I} (ne : j ≠ i) (k : Fin 4)
    (on : flag (N.bits (singletonInput i)) k = true)
    (pRead : k ≠ 0 → N.firstRaw j = 0) (qRead : k ≠ 1 → N.secondRaw j = 0)
    (rRead : k ≠ 2 → N.thirdRaw j = 0) :
    N.bits (pairInput j i) = N.bits (singletonInput i) := by
  let x := singletonInput i
  let y := pairInput j i
  have mono : ∀ a, x a ≤ y a := TwoShared.otherSingleton_pair j i
  have mass : (fun a => rise (x a) (y a)) = ones j := TwoShared.addedInputRise j i ne
  let p := N.first.evalWith x
  have pe : N.first.evalWith y = p := by
    apply evalUnchanged _ mono
    by_cases h : k = 0
    · exact Or.inl (by simpa [flag, h, bits, signals, x, p] using on)
    · exact Or.inr (by rw [mass]; exact pRead h)
  let q := N.second.evalWith (withHead p x)
  have qe : N.second.evalWith (withHead p y) = q := by
    apply evalUnchanged _ (withHeadMono le_rfl mono)
    by_cases h : k = 1
    · exact Or.inl (by simpa [flag, h, bits, signals, x, p, q] using on)
    · apply Or.inr
      have w : (fun a => rise (withHead p x a) (withHead p y a)) = withHead 0 (ones j) := by
        funext a
        cases a with
        | none => cases p <;> rfl
        | some a => exact congrFun mass a
      rw [w]
      exact qRead h
  have re : N.third.evalWith (withHead q (withHead p y)) =
      N.third.evalWith (withHead q (withHead p x)) := by
    apply evalUnchanged _ (withHeadMono le_rfl (withHeadMono le_rfl mono))
    by_cases h : k = 2
    · exact Or.inl (by simpa [flag, h, bits, signals, x, p, q] using on)
    · apply Or.inr
      have w : (fun a => rise (withHead q (withHead p x) a) (withHead q (withHead p y) a)) =
          withHead 0 (withHead 0 (ones j)) := by
        funext a
        rcases a with _ | _ | a
        · cases q <;> rfl
        · cases p <;> rfl
        · exact congrFun mass a
      rw [w]
      exact rRead h
  change N.bits y = N.bits x
  simp only [bits, signals, withHead_some, withHead_none, pe, qe, re, p, q]

def supply (b : Bool × Bool × Bool) (x : I → Bool) : Option (Option (Option I)) → Bool :=
  withHead b.2.2 (withHead b.2.1 (withHead b.1 x))

omit [DecidableEq I] in
theorem supply_signals (N : Network I) (x : I → Bool) :
    supply (N.bits x) x = N.signals x := rfl

abbrev rawKey (i : I) : Option (Option (Option I)) := some (some (some i))

theorem supply_setTwo (b : Bool × Bool × Bool) (u : I → Bool)
    (i j : I) (a c : Bool) :
    setTwo (supply b u) (rawKey i) (rawKey j) a c = supply b (setTwo u i j a c) := by
  funext k
  rcases k with _ | _ | _ | k <;> simp [setTwo, supply]

private theorem formulaReads (N : Network I) (i : I) :
    reads N.output (rawKey i) = N.outputRaw i := by
  unfold reads outputRaw
  congr 1
  funext a
  rcases a with _ | _ | _ | a <;> simp [singletonInput, ones]

theorem setTwo_zero {i j : I} (ne : i ≠ j) :
    setTwo (fun _ => false) i j true false = singletonInput i ∧
    setTwo (fun _ => false) i j false true = singletonInput j ∧
    setTwo (fun _ => false) i j true true = pairInput i j := by
  refine ⟨?_, ?_, ?_⟩ <;> funext k <;> by_cases ki : k = i <;>
    by_cases kj : k = j <;> simp_all [setTwo, singletonInput, pairInput]

theorem setTwo_one {i j a : I} (ia : i ≠ a) (ja : j ≠ a) (ij : i ≠ j) :
    setTwo (singletonInput a) i j false false = singletonInput a ∧
    setTwo (singletonInput a) i j true false = pairInput i a ∧
    setTwo (singletonInput a) i j false true = pairInput j a := by
  refine ⟨?_, ?_, ?_⟩ <;> funext k <;> by_cases ki : k = i <;>
    by_cases kj : k = j <;> simp_all [setTwo, singletonInput, pairInput]

theorem twoAtOneStage (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j a : I} (ij : i ≠ j) (ia : i ≠ a) (ja : j ≠ a)
    (warm : firstStage (N.bits (singletonInput i)) ≠ 3)
    (same : firstStage (N.bits (singletonInput i)) = firstStage (N.bits (singletonInput j)))
    (atA : flag (N.bits (singletonInput a)) (firstStage (N.bits (singletonInput i))) = true)
    (oi : 1 ≤ N.outputRaw i) (oj : 1 ≤ N.outputRaw j)
    (ri : N.forest.weight (ones i) ≤ 2) (rj : N.forest.weight (ones j) ≤ 2) : False := by
  let k := firstStage (N.bits (singletonInput i))
  obtain ⟨outi, pi, qi, ti⟩ := N.onlyFirstStageAndOutput i warm oi ri
  obtain ⟨outj, pj, qj, tj⟩ := N.onlyFirstStageAndOutput j (same ▸ warm) oj rj
  rw [← same] at pj qj tj
  have iA := N.stableWhenAlreadyActive ia k atA pi qi ti
  have jA := N.stableWhenAlreadyActive ja k atA pj qj tj
  have atJ := stageActive (N.bits (singletonInput j)) (same ▸ warm)
  rw [← same] at atJ
  have ijBits := N.stableWhenAlreadyActive ij k atJ pi qi ti
  have jiBits := N.stableWhenAlreadyActive ij.symm k (stageActive _ warm) pj qj tj
  have swap : pairInput i j = pairInput j i := by funext v; exact Bool.or_comm _ _
  have sameBits : N.bits (singletonInput i) = N.bits (singletonInput j) := by
    rw [← jiBits, ← ijBits, swap]
  let base := supply (N.bits (singletonInput i)) (fun _ : I => false)
  let atBase := supply (N.bits (singletonInput a)) (singletonInput a)
  obtain ⟨u10, u01, u11⟩ := setTwo_zero ij
  obtain ⟨v00, v10, v01⟩ := setTwo_one ia ja ij
  apply noAndToOr N.output (i := rawKey i) (j := rawKey j) (by simpa using ij)
    (by rw [formulaReads, outi]) (by rw [formulaReads, outj]) base atBase
  · simpa only [base, supply_setTwo, u10, supply_signals, ← eval_eq] using test.1 i
  · simpa only [base, supply_setTwo, u01, sameBits, supply_signals, ← eval_eq] using test.1 j
  · simpa only [base, supply_setTwo, u11, ← jiBits, ← swap, supply_signals, ← eval_eq] using test.2 i j ij
  · rw [show atBase = supply (N.bits (singletonInput a)) (singletonInput a) from rfl,
      supply_setTwo, v00, supply_signals, ← eval_eq]
    exact test.1 a
  · rw [show atBase = supply (N.bits (singletonInput a)) (singletonInput a) from rfl,
      supply_setTwo, v10, ← iA, supply_signals, ← eval_eq]
    exact test.2 i a ia
  · rw [show atBase = supply (N.bits (singletonInput a)) (singletonInput a) from rfl,
      supply_setTwo, v01, ← jA, supply_signals, ← eval_eq]
    exact test.2 j a ja

theorem cardLeSevenOfFull [Fintype I] (N : Network I)
    (test : ThresholdOn N.forest.eval) (reads : ∀ i, N.forest.weight (ones i) ≤ 2)
    (few : (univ.filter fun i => firstStage (N.bits (singletonInput i)) = 3).card ≤ 3)
    {a : I} (full : N.bits (singletonInput a) = (true, true, true)) : Fintype.card I ≤ 7 := by
  let stage (i : I) := firstStage (N.bits (singletonInput i))
  let cold := univ.filter fun i => stage i = 3
  let hot := univ.filter fun i => stage i ≠ 3
  have total : cold.card + hot.card = Fintype.card I := by
    simpa [cold, hot] using
      card_filter_add_card_filter_not (s := (univ : Finset I)) (fun i => stage i = 3)
  have smallCold : cold.card ≤ 3 := few
  let rest := hot.erase a
  have aHot : a ∈ hot := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    change firstStage (N.bits (singletonInput a)) ≠ 3
    rw [full]
    decide
  have restCard : rest.card + 1 = hot.card := card_erase_add_one aHot
  have restSmall : rest.card ≤ (univ.erase (3 : Fin 4)).card := by
    apply card_le_card_of_injOn stage
    · intro i hi
      change i ∈ rest at hi
      have h := (mem_filter.mp (mem_erase.mp hi).2).2
      simp [h]
    · intro i hi j hj same
      by_contra! ne
      change i ∈ rest at hi
      change j ∈ rest at hj
      obtain ⟨ia, ih⟩ := mem_erase.mp hi
      obtain ⟨ja, jh⟩ := mem_erase.mp hj
      have warm : stage i ≠ 3 := (mem_filter.mp ih).2
      have atA : flag (N.bits (singletonInput a)) (stage i) = true := by
        rw [full]
        exact fullActive _ warm
      exact N.twoAtOneStage test ne ia ja warm same atA
        (N.fullProfileForcesOutputRead test ia full) (N.fullProfileForcesOutputRead test ja full)
        (reads i) (reads j)
  have count : (univ.erase (3 : Fin 4)).card = 3 := by decide
  omega

theorem noFullProfile [Fintype I] (N : Network I) (size : Fintype.card I = 8)
    (valid : N.forest.Valid) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2) (a : I) :
    N.bits (singletonInput a) ≠ (true, true, true) := by
  intro full
  let stage (i : I) := firstStage (N.bits (singletonInput i))
  let cold := univ.filter fun i => stage i = 3
  let hot := univ.filter fun i => stage i ≠ 3
  let weight (i : I) := 2 ^ (3 - load (N.bits (singletonInput i)))
  have total : cold.card + hot.card = 8 := by
    simpa [cold, hot, size] using
      card_filter_add_card_filter_not (s := (univ : Finset I)) (fun i => stage i = 3)
  have coldWeight : (∑ i ∈ cold, weight i) = cold.card * 8 := by
    calc
      _ = ∑ i ∈ cold, (8 : ℕ) := sum_congr rfl fun i hi => by
        have h := coldStage _ (mem_filter.mp hi).2
        simp [weight, h]
      _ = _ := by simp
  have hotWeight : hot.card ≤ ∑ i ∈ hot, weight i := by
    calc
      hot.card = ∑ i ∈ hot, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ hot, weight i := sum_le_sum fun i _ => Nat.pow_pos (by decide)
  have sumEq : (∑ i ∈ cold, weight i) + (∑ i ∈ hot, weight i) = ∑ i ∈ univ, weight i := by
    exact sum_filter_add_sum_filter_not (s := univ) (p := fun i => stage i = 3) _
  have packed : (∑ i ∈ univ, weight i) ≤ 32 := N.halfPacking valid test reads univ
  have smallCold : cold.card ≤ 3 := by omega
  have bound := N.cardLeSevenOfFull test reads smallCold full
  omega

end CrownProfileThree.Network
