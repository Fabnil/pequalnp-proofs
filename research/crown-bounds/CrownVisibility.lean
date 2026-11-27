import CrownFourNormal

namespace CrownVisibility

open CrownForks CrownForest CrownProfiles CrownPairFormula PnpResearch
open CrownProfileThree.Network (ones)

variable {A I : Type}

def outputWeight {A : Type} : SharedFormula A → (A → ℕ) → ℕ
  | .tree f, w => leafWeight f w
  | .share _ _ rest, w => outputWeight rest (withHead 0 w)

def stageWeight {A : Type} : SharedFormula A → (A → ℕ) → ℕ → ℕ
  | .tree _, _, _ => 0
  | .share f _ _, w, 0 => leafWeight f w
  | .share _ _ rest, w, k + 1 => stageWeight rest (withHead 0 w) k

def bitAt (bits : List Bool) (k : ℕ) : Bool := bits[k]?.getD false

def firstHot (E : SharedFormula A) (x : A → Bool) : ℕ :=
  (profile E x).findIdx id

theorem stageAndOutput_le (E : SharedFormula A) (w : A → ℕ) (k : ℕ) :
    outputWeight E w + stageWeight E w k ≤ E.weight w := by
  induction E generalizing k with
  | tree f => simp [outputWeight, stageWeight, SharedFormula.weight]
  | share f u rest ih =>
    cases k with
    | zero =>
      have tail := ih (withHead 0 w) 0
      simp only [outputWeight, stageWeight, SharedFormula.weight]
      omega
    | succ k =>
      have tail := ih (withHead 0 w) k
      simp only [outputWeight, stageWeight, SharedFormula.weight]
      omega

theorem twoStagesAndOutput_le (E : SharedFormula A) (w : A → ℕ) {k l : ℕ} (ne : k ≠ l) :
    outputWeight E w + stageWeight E w k + stageWeight E w l ≤ E.weight w := by
  induction E generalizing k l with
  | tree f => simp [outputWeight, stageWeight, SharedFormula.weight]
  | share f u rest ih =>
    cases k with
    | zero =>
      cases l with
      | zero => exact (ne rfl).elim
      | succ l =>
        have tail := stageAndOutput_le rest (withHead 0 w) l
        simp only [outputWeight, stageWeight, SharedFormula.weight]
        omega
    | succ k =>
      cases l with
      | zero =>
        have tail := stageAndOutput_le rest (withHead 0 w) k
        simp only [outputWeight, stageWeight, SharedFormula.weight]
        omega
      | succ l =>
        have tail := ih (withHead 0 w) (k := k) (l := l) (by omega)
        simp only [outputWeight, stageWeight, SharedFormula.weight]
        omega

theorem firstHotFacts (E : SharedFormula A) (x : A → Bool) (hot : true ∈ profile E x) :
    bitAt (profile E x) (firstHot E x) = true ∧
      1 ≤ stageWeight E (fun a => (x a).toNat) (firstHot E x) := by
  induction E with
  | tree f => simp [profile] at hot
  | share f u rest ih =>
    cases head : f.evalWith x with
    | false =>
      have hot' : true ∈ profile rest (withHead false x) := by simpa [profile, head] using hot
      have mass : (fun a => (withHead false x a).toNat) = withHead 0 (fun a => (x a).toNat) := by
        funext a
        cases a <;> rfl
      have tail := ih (withHead false x) hot'
      rw [mass] at tail
      simpa [profile, head, firstHot, List.findIdx_cons, bitAt, stageWeight] using tail
    | true =>
      exact ⟨by simp [bitAt, firstHot, profile, List.findIdx_cons, head],
        by simpa [firstHot, profile, List.findIdx_cons, head, stageWeight] using readsOfTrue f x head⟩

private theorem leafWeight_le (f : Formula A) (w z : A → ℕ) (le : ∀ a, w a ≤ z a) :
    leafWeight f w ≤ leafWeight f z := by
  induction f with
  | var a => exact le a
  | conj l r il ir | disj l r il ir => exact Nat.add_le_add il ir

/-- A shared stage that directly reads a changed input can absorb that change
    when it already outputs one. -/
theorem stableProfile (E : SharedFormula A) (x y : A → Bool) (w : A → ℕ)
    (mono : ∀ a, x a ≤ y a) (bounded : ∀ a, rise (x a) (y a) ≤ w a)
    (covered : ∀ k, 0 < stageWeight E w k → bitAt (profile E x) k = true) :
    profile E y = profile E x ∧ (outputWeight E w = 0 → E.eval y = E.eval x) := by
  induction E with
  | tree f =>
    refine ⟨rfl, fun zero => (eqOfNoRise f mono ?_).symm⟩
    have bound := leafWeight_le f _ w bounded
    change leafWeight f w = 0 at zero
    omega
  | share f u rest ih =>
    have eq : f.evalWith y = f.evalWith x := by
      by_cases zero : leafWeight f w = 0
      · have bound := leafWeight_le f _ w bounded
        exact (eqOfNoRise f mono (by omega)).symm
      · have on : f.evalWith x = true := covered 0 (by change 0 < leafWeight f w; omega)
        exact ((Bool.le_iff_imp.mp (evalMono f mono)) on).trans on.symm
    have tail := ih (withHead (f.evalWith x) x) (withHead (f.evalWith x) y) (withHead 0 w)
      (withHeadMono le_rfl mono)
      (by intro a; cases a with
          | none => cases f.evalWith x <;> simp [rise]
          | some a => exact bounded a)
      (by intro k pos; exact covered (k + 1) pos)
    simpa only [profile, SharedFormula.eval, eq, List.cons.injEq, true_and, outputWeight] using tail

theorem pairStable [DecidableEq I] (E : SharedFormula I) (i j : I)
    (covered : ∀ k, 0 < stageWeight E (ones i) k →
      bitAt (profile E (singletonInput j)) k = true) :
    profile E (pairInput i j) = profile E (singletonInput j) ∧
      (outputWeight E (ones i) = 0 → E.eval (pairInput i j) = E.eval (singletonInput j)) := by
  apply stableProfile E _ _ (ones i) (TwoShared.otherSingleton_pair i j) _ covered
  intro a
  unfold ones pairInput rise
  cases singletonInput i a <;> cases singletonInput j a <;> decide

/-- A singleton that activates a stage and is read at the output has only one
    occurrence before the output, in its first active stage. -/
theorem visibleReads (E : SharedFormula A) (x : A → Bool) (hot : true ∈ profile E x)
    (visible : 0 < outputWeight E (fun a => (x a).toNat))
    (raw : E.weight (fun a => (x a).toNat) ≤ 2) :
    outputWeight E (fun a => (x a).toNat) = 1 ∧
      ∀ k, stageWeight E (fun a => (x a).toNat) k = if k = firstHot E x then 1 else 0 := by
  have facts := (firstHotFacts E x hot).2
  have one := stageAndOutput_le E (fun a => (x a).toNat) (firstHot E x)
  refine ⟨by omega, fun k => ?_⟩
  split
  · rename_i same
    subst k
    omega
  · rename_i ne
    have two := twoStagesAndOutput_le E (fun a => (x a).toNat) ne
    omega

theorem addVisible [DecidableEq I] (E : SharedFormula I) {i j : I}
    (hot : true ∈ profile E (singletonInput i))
    (visible : 0 < outputWeight E (ones i)) (raw : E.weight (ones i) ≤ 2)
    (atJ : bitAt (profile E (singletonInput j)) (firstHot E (singletonInput i)) = true) :
    profile E (pairInput i j) = profile E (singletonInput j) := by
  refine (pairStable E i j ?_).1
  intro k positive
  have reads := (visibleReads E (singletonInput i) hot visible raw).2 k
  change stageWeight E (ones i) k = _ at reads
  split at reads
  · rename_i same
    simpa only [same] using atJ
  · omega

/-- View every raw input and every computed signal as a separate argument in
    the output formula. -/
def outputFormula {A B : Type} : SharedFormula A → (A → B) → (ℕ → B) → Formula B
  | .tree f, map, _ => rename f map
  | .share _ _ rest, map, signal =>
    outputFormula rest (withHead (signal 0) map) (fun k => signal (k + 1))

private theorem outputFormula_eval {B : Type} (E : SharedFormula A) (map : A → B) (signal : ℕ → B)
    (value : B → Bool) (agree : ∀ k, value (signal k) = bitAt (profile E (value ∘ map)) k) :
    (outputFormula E map signal).evalWith value = E.eval (value ∘ map) := by
  induction E generalizing signal with
  | tree f => exact eval_rename f map value
  | share f u rest ih =>
    have merge : value ∘ withHead (signal 0) map =
        withHead (f.evalWith (value ∘ map)) (value ∘ map) := by
      funext a
      cases a with
      | none => exact agree 0
      | some a => rfl
    have tail := ih (withHead (signal 0) map) (fun k => signal (k + 1)) (by
      intro k
      rw [merge]
      exact agree (k + 1))
    simpa only [outputFormula, SharedFormula.eval, merge] using tail

private theorem outputFormula_weight {B : Type} (E : SharedFormula A) (map : A → B)
    (signal : ℕ → B) (w : B → ℕ) (zero : ∀ k, w (signal k) = 0) :
    leafWeight (outputFormula E map signal) w = outputWeight E (w ∘ map) := by
  induction E generalizing signal with
  | tree f => exact weight_rename f map w
  | share f u rest ih =>
    have merge : w ∘ withHead (signal 0) map = withHead 0 (w ∘ map) := by
      funext a
      cases a with
      | none => exact zero 0
      | some a => rfl
    simpa only [outputFormula, outputWeight, merge] using
      ih (withHead (signal 0) map) (fun k => signal (k + 1)) (fun k => zero (k + 1))

def output (E : SharedFormula A) : Formula (A ⊕ ℕ) :=
  outputFormula E Sum.inl Sum.inr

def supply (bits : List Bool) (x : A → Bool) : A ⊕ ℕ → Bool :=
  Sum.elim x (bitAt bits)

theorem output_eval (E : SharedFormula A) (x : A → Bool) :
    (output E).evalWith (supply (profile E x) x) = E.eval x :=
  outputFormula_eval E Sum.inl Sum.inr _ (fun _ => rfl)

theorem output_read [DecidableEq I] (E : SharedFormula I) (i : I) :
    reads (output E) (Sum.inl i) = outputWeight E (ones i) := by
  have rule := outputFormula_weight E Sum.inl Sum.inr (ones (Sum.inl i)) (by
    intro k
    simp [ones, singletonInput])
  have inputs : (ones (Sum.inl i) : I ⊕ ℕ → ℕ) ∘ Sum.inl = ones i := by
    funext a
    simp [ones, singletonInput]
  rw [inputs] at rule
  exact rule

private theorem supply_setTwo [DecidableEq I] (bits : List Bool) (x : I → Bool)
    (i j : I) (a b : Bool) :
    supply bits (setTwo x i j a b) = setTwo (supply bits x) (Sum.inl i) (Sum.inl j) a b := by
  funext k
  cases k <;> simp [supply, setTwo]

/-- Two visible singletons with the same first active stage rule out activating
    that stage on a third singleton. -/
theorem twoVisible [DecidableEq I] (E : SharedFormula I) (test : ThresholdOn E.eval)
    {i j a : I} (ij : i ≠ j) (ia : i ≠ a) (ja : j ≠ a)
    (hi : true ∈ profile E (singletonInput i)) (hj : true ∈ profile E (singletonInput j))
    (vi : 0 < outputWeight E (ones i)) (vj : 0 < outputWeight E (ones j))
    (ri : E.weight (ones i) ≤ 2) (rj : E.weight (ones j) ≤ 2)
    (first : firstHot E (singletonInput i) = firstHot E (singletonInput j))
    (atA : bitAt (profile E (singletonInput a)) (firstHot E (singletonInput i)) = true) : False := by
  have iA := addVisible E hi vi ri atA
  have jA := addVisible E hj vj rj (first ▸ atA)
  have ijBits := addVisible E hi vi ri (first.symm ▸ (firstHotFacts E _ hj).1)
  have jiBits := addVisible E hj vj rj (first ▸ (firstHotFacts E _ hi).1)
  have swap : pairInput i j = pairInput j i := by funext a; exact Bool.or_comm _ _
  have same : profile E (singletonInput i) = profile E (singletonInput j) := by
    rw [← jiBits, ← ijBits, swap]
  let base := supply (profile E (singletonInput i)) (fun _ : I => false)
  let atBase := supply (profile E (singletonInput a)) (singletonInput a)
  obtain ⟨u10, u01, u11⟩ := CrownProfileThree.Network.setTwo_zero ij
  obtain ⟨v00, v10, v01⟩ := CrownProfileThree.Network.setTwo_one ia ja ij
  apply noAndToOr (output E) (i := Sum.inl i) (j := Sum.inl j) (by simpa using ij)
    (by rw [output_read]; exact (visibleReads E _ hi vi ri).1.le)
    (by rw [output_read]; exact (visibleReads E _ hj vj rj).1.le) base atBase
  · simpa only [base, ← supply_setTwo, u10, output_eval] using test.1 i
  · simpa only [base, ← supply_setTwo, u01, same, output_eval] using test.1 j
  · rw [show base = supply (profile E (singletonInput i)) (fun _ => false) from rfl,
      ← supply_setTwo, u11, ← jiBits, ← swap, output_eval]
    exact test.2 i j ij
  · simpa only [atBase, ← supply_setTwo, v00, output_eval] using test.1 a
  · simpa only [atBase, ← supply_setTwo, v10, ← iA, output_eval] using test.2 i a ia
  · simpa only [atBase, ← supply_setTwo, v01, ← jA, output_eval] using test.2 j a ja

end CrownVisibility
