import CrownProfiles

namespace CrownFrozenCuts

open CrownForks CrownForest CrownProfiles PnpResearch Finset

variable {A I : Type}

/-- Every shared signal selected by the mask is true on the given input. -/
def includes {A : Type} : SharedFormula A → List Bool → (A → Bool) → Prop
  | .tree _, _, _ => True
  | .share f _ rest, mask, x =>
    (mask.headD false = true → f.evalWith x = true) ∧
      includes rest mask.tail (withHead (f.evalWith x) x)

private theorem kept_add (E : SharedFormula A) (mask : List Bool) (w z : A → ℕ) :
    keptWeight E mask (fun a => w a + z a) = keptWeight E mask w + keptWeight E mask z := by
  induction E generalizing mask with
  | tree f => exact leafWeight_add f w z
  | share f _ rest ih =>
    have split : withHead 0 (fun a => w a + z a) = fun a => withHead 0 w a + withHead 0 z a := by
      funext a
      cases a <;> rfl
    simp only [keptWeight, leafWeight_add, split, ih]
    split <;> omega

private theorem kept_mul (E : SharedFormula A) (mask : List Bool) (k : ℕ) (w : A → ℕ) :
    keptWeight E mask (fun a => k * w a) = k * keptWeight E mask w := by
  induction E generalizing mask with
  | tree f => exact leafWeight_mul f w k
  | share f _ rest ih =>
    have split : withHead 0 (fun a => k * w a) = fun a => k * withHead 0 w a := by
      funext a
      cases a <;> simp
    simp only [keptWeight, leafWeight_mul, split, ih]
    split <;> simp [Nat.mul_add]

private theorem kept_head (rest : SharedFormula (Option A)) (mask : List Bool) (k : ℕ) (w : A → ℕ) :
    keptWeight rest mask (withHead k w) =
      keptWeight rest mask (withHead 0 w) + k * keptWeight rest mask (withHead 1 fun _ => 0) := by
  have split : withHead k w = fun a =>
      withHead 0 w a + k * withHead 1 (fun _ => 0) a := by
    funext a
    cases a <;> simp
  rw [split, kept_add, kept_mul]

/-- Activated signals are charged only for reads in formulas that were not
    frozen. The first surviving read is paid for by computing the signal. -/
def extraAfterFreeze {I A : Type} : SharedFormula A → List Bool → Samples I A → I → ℕ
  | .tree _, _, _, _ => 0
  | .share f _ rest, mask, s, i =>
    if mask.headD false then extraAfterFreeze rest mask.tail (s.freeze true) i
    else
      let reads := keptWeight rest mask.tail (withHead 1 fun _ => 0)
      rise (f.evalWith s.base) (f.evalWith (s.one i)) * (reads - 1) +
        extraAfterFreeze rest mask.tail (s.add f) i

theorem degree_le (E : SharedFormula A) (mask : List Bool) (s : Samples I A) (i : I)
    (mono : s.onBase) :
    degree (keptRows E mask s) i ≤ keptWeight E mask (s.riseAt i) + extraAfterFreeze E mask s i := by
  induction E generalizing mask with
  | tree f => exact (Nat.le_add_right ..).trans (s.charge mono f i)
  | share f _ rest ih =>
    by_cases freeze : mask.headD false = true
    · simpa only [keptRows, keptWeight, extraAfterFreeze, freeze, ↓reduceIte, Nat.zero_add,
        Samples.freeze_riseAt] using ih mask.tail (s.freeze true) (s.freeze_onBase mono true)
    · have h := s.charge mono f i
      have later := ih mask.tail (s.add f) (s.add_onBase mono f)
      rw [Samples.add_riseAt, kept_head] at later
      have off : mask.headD false = false := Bool.eq_false_iff.mpr freeze
      simp only [keptRows, keptWeight, extraAfterFreeze, off, Bool.false_eq_true,
        ite_false, degree_append]
      let reads := keptWeight rest mask.tail (withHead 1 fun _ => 0)
      let bit := rise (f.evalWith s.base) (f.evalWith (s.one i))
      change degree (s.rows f) i + bit ≤ _ at h
      change _ ≤ _ + bit * reads + _ at later
      change _ ≤ _ + (bit * (reads - 1) + _)
      have gain : bit * reads ≤ bit * (reads - 1) + bit := by
        by_cases zero : reads = 0
        · simp [zero]
        · have split : reads = (reads - 1) + 1 := by omega
          conv_lhs => rw [split]
          rw [Nat.mul_add, Nat.mul_one]
      omega

theorem separates (E : SharedFormula A) (mask : List Bool) (s : Samples I A)
    (prior : List (Cut I)) (i j : I) (mono : s.onBase) (known : s.leafWitness prior i j)
    (one_le_two : ∀ a, s.one i a ≤ s.two i j a)
    (hitI : includes E mask (s.one i)) (hitJ : includes E mask (s.one j))
    (on : E.eval (s.two i j) = true) (offI : E.eval (s.one i) = false)
    (offJ : E.eval (s.one j) = false) : separated (prior ++ keptRows E mask s) i j := by
  induction E generalizing mask prior with
  | tree f => exact Samples.outputSeparates mono known f on offI offJ
  | share f _ rest ih =>
    by_cases freeze : mask.headD false = true
    · have atI := hitI.1 freeze
      have atJ := hitJ.1 freeze
      have atPair := (Bool.le_iff_imp.mp (evalMono f one_le_two)) atI
      have tailI : includes rest mask.tail ((s.freeze true).one i) := by
        simpa only [Samples.freeze, atI] using hitI.2
      have tailJ : includes rest mask.tail ((s.freeze true).one j) := by
        simpa only [Samples.freeze, atJ] using hitJ.2
      have positive : rest.eval ((s.freeze true).two i j) = true := by
        simpa only [SharedFormula.eval, Samples.freeze, atPair] using on
      have negativeI : rest.eval ((s.freeze true).one i) = false := by
        simpa only [SharedFormula.eval, Samples.freeze, atI] using offI
      have negativeJ : rest.eval ((s.freeze true).one j) = false := by
        simpa only [SharedFormula.eval, Samples.freeze, atJ] using offJ
      have tail := ih mask.tail (s.freeze true) prior (s.freeze_onBase mono true)
        (Samples.freeze_leafWitness known true) (withHeadMono le_rfl one_le_two)
        tailI tailJ positive negativeI negativeJ
      simpa only [keptRows, freeze, ↓reduceIte] using tail
    · have tail := ih mask.tail (s.add f) (prior ++ s.rows f)
        (s.add_onBase mono f) (Samples.add_leafWitness mono known f)
        (withHeadMono (evalMono f one_le_two) one_le_two) hitI.2 hitJ.2 on offI offJ
      have off : mask.headD false = false := Bool.eq_false_iff.mpr freeze
      simpa only [keptRows, off, Bool.false_eq_true, ite_false, List.append_assoc] using tail

/-- Singleton labels that all activate the selected signals still obey the cut
    inequality. Their cost counts only reads after fixing those signals to one. -/
theorem packing [DecidableEq I] (E : SharedFormula I) (test : ThresholdOn E.eval)
    (mask : List Bool) (S : Finset I) (limit : I → ℕ) (ceiling : ℕ)
    (common : ∀ i ∈ S, includes E mask (singletonInput i))
    (bounded : ∀ i ∈ S, keptWeight E mask (fun j => (singletonInput i j).toNat) +
      extraAfterFreeze E mask (Samples.raw I) i ≤ limit i)
    (small : ∀ i ∈ S, limit i ≤ ceiling) :
    ∑ i ∈ S, 2 ^ (ceiling - limit i) ≤ 2 ^ ceiling := by
  let s := Samples.raw I
  refine CrownThreshold.weightedPacking S (rowCode (keptRows E mask s)) limit ceiling ?_ ?_ small
  · intro i hi j hj ne
    apply rowCodeSeparates
    have cut := separates E mask s [] i j Samples.raw_onBase (Samples.raw_leafWitness i j)
      (TwoShared.singleton_pair i j) (common i hi) (common j hj) (test.2 i j ne)
      (test.1 i) (test.1 j)
    simpa only [List.nil_append] using cut
  · intro i hi
    rw [fixedRowCode]
    have cost := degree_le E mask (Samples.raw I) i Samples.raw_onBase
    rw [TwoShared.raw_rises] at cost
    exact cost.trans (bounded i hi)

end CrownFrozenCuts
