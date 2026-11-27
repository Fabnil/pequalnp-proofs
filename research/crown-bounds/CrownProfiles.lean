import CrownSharedCuts

namespace CrownProfiles

open CrownForks CrownForest PnpResearch Finset

variable {A I : Type}

def profile {A : Type} : SharedFormula A → (A → Bool) → List Bool
  | .tree _, _ => []
  | .share f _ tail, x =>
    let bit := f.evalWith x
    bit :: profile tail (withHead bit x)

def keptWeight {A : Type} : SharedFormula A → List Bool → (A → ℕ) → ℕ
  | .tree f, _, w => leafWeight f w
  | .share f _ tail, bits, w =>
    (if bits.headD false then 0 else leafWeight f w) +
      keptWeight tail bits.tail (withHead 0 w)

def keptRows {A I : Type} : SharedFormula A → List Bool → Samples I A → List (Cut I)
  | .tree f, _, s => s.rows f
  | .share f _ tail, bits, s =>
    if bits.headD false then keptRows tail bits.tail (s.freeze true)
    else s.rows f ++ keptRows tail bits.tail (s.add f)

theorem keptWeight_le (E : SharedFormula A) (bits : List Bool) (w : A → ℕ) :
    keptWeight E bits w ≤ E.weight w := by
  induction E generalizing bits with
  | tree f => rfl
  | share f _ tail ih =>
    simp only [keptWeight, SharedFormula.weight]
    have h := ih bits.tail (withHead 0 w)
    split <;> omega

theorem readsOfTrue (f : Formula A) (x : A → Bool) (on : f.evalWith x = true) :
    1 ≤ leafWeight f (fun a => (x a).toNat) := by
  by_contra! h
  have hzero : (fun a => rise false (x a)) = fun a => (x a).toNat := by
    funext a
    simp [rise]
  have noRise := eqOfNoRise f (base := fun _ => false) (value := x)
    (fun a => Bool.false_le (x a)) (by rw [hzero]; omega)
  rw [evalZero, on] at noRise
  contradiction

theorem activeUsesRead (E : SharedFormula A) (x : A → Bool) (active : true ∈ profile E x) :
    keptWeight E (profile E x) (fun a => (x a).toNat) + 1 ≤
      E.weight (fun a => (x a).toNat) := by
  induction E with
  | tree f => simp [profile] at active
  | share f _ tail ih =>
    by_cases on : f.evalWith x = true
    · simp only [profile, on, keptWeight, List.headD_cons, List.tail_cons, ↓reduceIte,
        Nat.zero_add, SharedFormula.weight]
      have left := readsOfTrue f x on
      have right := keptWeight_le tail (profile tail (withHead true x))
        (withHead 0 fun a => (x a).toNat)
      omega
    · have off : f.evalWith x = false := Bool.eq_false_iff.mpr on
      simp only [profile, off, List.mem_cons, Bool.true_eq_false, false_or] at active
      have h := ih (withHead false x) active
      have w : (fun a => (withHead false x a).toNat) = withHead 0 (fun a => (x a).toNat) := by
        funext a
        cases a <;> rfl
      rw [w] at h
      simp only [profile, off, keptWeight, List.headD_cons, List.tail_cons, Bool.false_eq_true,
        ↓reduceIte, SharedFormula.weight]
      omega

theorem keptDegree (E : SharedFormula A) (bits : List Bool) (s : Samples I A) (i : I)
    (mono : s.onBase) (agree : profile E (s.one i) = bits) :
    degree (keptRows E bits s) i ≤ keptWeight E bits (s.riseAt i) := by
  induction E generalizing bits with
  | tree f => exact le_trans (Nat.le_add_right ..) (s.charge mono f i)
  | share f _ tail ih =>
    subst bits
    by_cases on : f.evalWith (s.one i) = true
    · have h := ih (profile tail (withHead true (s.one i))) (s.freeze true)
        (s.freeze_onBase mono true) rfl
      rw [Samples.freeze_riseAt] at h
      simpa [profile, on, keptRows, keptWeight] using h
    · have off : f.evalWith (s.one i) = false := Bool.eq_false_iff.mpr on
      have h := ih (profile tail ((s.add f).one i)) (s.add f) (s.add_onBase mono f) rfl
      rw [Samples.add_riseAt] at h
      simp only [off, rise, Bool.and_false, Bool.toNat_false] at h
      have atOne : (s.add f).one i = withHead false (s.one i) := by simp [Samples.add, off]
      rw [atOne] at h
      have c := s.charge mono f i
      simp only [profile, off, keptRows, keptWeight, List.headD_cons, List.tail_cons,
        Bool.false_eq_true, ↓reduceIte, degree_append]
      omega

theorem keptSeparates (E : SharedFormula A) (bits : List Bool) (s : Samples I A)
    (prior : List (Cut I)) (i j : I) (mono : s.onBase)
    (known : s.leafWitness prior i j) (one_le_two : ∀ a, s.one i a ≤ s.two i j a)
    (agreei : profile E (s.one i) = bits) (agreej : profile E (s.one j) = bits)
    (on : E.eval (s.two i j) = true) (offi : E.eval (s.one i) = false)
    (offj : E.eval (s.one j) = false) :
    separated (prior ++ keptRows E bits s) i j := by
  induction E generalizing bits prior with
  | tree f => exact Samples.outputSeparates mono known f on offi offj
  | share f _ tail ih =>
    subst bits
    have same := (List.cons.inj agreej).1
    have rest := (List.cons.inj agreej).2
    by_cases active : f.evalWith (s.one i) = true
    · have atPair := (Bool.le_iff_imp.mp (evalMono f one_le_two)) active
      change tail.eval (withHead (f.evalWith (s.two i j)) (s.two i j)) = true at on
      change tail.eval (withHead (f.evalWith (s.one i)) (s.one i)) = false at offi
      change tail.eval (withHead (f.evalWith (s.one j)) (s.one j)) = false at offj
      rw [atPair] at on
      rw [same, active] at offj rest
      rw [active] at offi
      have h := ih (profile tail (withHead true (s.one i))) (s.freeze true) prior
        (s.freeze_onBase mono true) (Samples.freeze_leafWitness known true)
        (withHeadMono le_rfl one_le_two) rfl rest on offi offj
      simpa [profile, keptRows, active] using h
    · have idle : f.evalWith (s.one i) = false := Bool.eq_false_iff.mpr active
      have h := ih (profile tail ((s.add f).one i)) (s.add f) (prior ++ s.rows f)
        (s.add_onBase mono f) (Samples.add_leafWitness mono known f)
        (withHeadMono (evalMono f one_le_two) one_le_two) rfl rest on offi offj
      change separated ((prior ++ s.rows f) ++
        keptRows tail (profile tail (withHead (f.evalWith (s.one i)) (s.one i))) (s.add f)) i j at h
      simpa [profile, keptRows, idle, List.append_assoc] using h

theorem profileCapacity [DecidableEq I] (E : SharedFormula I) (test : ThresholdOn E.eval)
    (S : Finset I) (bits : List Bool) (agree : ∀ i ∈ S, profile E (singletonInput i) = bits)
    (reads : ∀ i ∈ S, E.weight (fun k => (singletonInput i k).toNat) ≤ 2)
    (active : true ∈ bits) : S.card ≤ 2 := by
  apply boundedByCuts S (keptRows E bits (Samples.raw I)) 1
  · intro i hi j hj ne
    simpa using keptSeparates E bits (Samples.raw I) [] i j Samples.raw_onBase
      (Samples.raw_leafWitness i j) (TwoShared.singleton_pair i j)
      (agree i hi) (agree j hj) (test.2 i j ne) (test.1 i) (test.1 j)
  · intro i hi
    have d := keptDegree E bits (Samples.raw I) i Samples.raw_onBase (agree i hi)
    have a := activeUsesRead E (singletonInput i) (agree i hi ▸ active)
    rw [agree i hi] at a
    rw [TwoShared.raw_rises] at d
    exact le_trans d (by have b := reads i hi; omega)

theorem keptReadOfPair [DecidableEq I] (E : SharedFormula I) (test : ThresholdOn E.eval)
    {i j : I} (ne : i ≠ j) (same : profile E (singletonInput j) = profile E (singletonInput i)) :
    1 ≤ keptWeight E (profile E (singletonInput i)) (fun k => (singletonInput i k).toNat) := by
  let bits := profile E (singletonInput i)
  let s := Samples.raw I
  have found : separated (keptRows E bits s) i j := by
    simpa only [List.nil_append] using keptSeparates E bits s [] i j Samples.raw_onBase
      (Samples.raw_leafWitness i j) (TwoShared.singleton_pair i j)
      rfl same (test.2 i j ne) (test.1 i) (test.1 j)
  have count := keptDegree E bits s i Samples.raw_onBase rfl
  change _ ≤ keptWeight E bits ((Samples.raw I).riseAt i) at count
  rw [TwoShared.raw_rises] at count
  apply le_trans _ count
  obtain ⟨row, inside, split⟩ := found
  have yes : (row i).isSome = true := by
    rcases split with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have yes' : row ∈ (keptRows E bits s).filter (fun r => (r i).isSome) :=
    List.mem_filter.mpr ⟨inside, yes⟩
  rw [degree, List.countP_eq_length_filter]
  exact List.length_pos_of_mem yes'

end CrownProfiles
