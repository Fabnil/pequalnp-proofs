import CrownOrProfiles

namespace CrownOrPacking

open CrownForks CrownPairFormula CrownFourGroups PnpResearch Finset

private abbrev Flag := Option (Fin 3)

variable {I : Type} [DecidableEq I]

private def profileSamples (p : I → Flag → Bool) : Samples I (Flag ⊕ I) :=
  ⟨fun _ => false, fun i => assignment (p i) (singletonInput i),
    fun i j => assignment (fun k => p i k || p j k) (pairInput i j)⟩

private theorem onBase (p : I → Flag → Bool) : (profileSamples p).onBase :=
  fun _ _ => Bool.false_le _

private theorem leaves (p : I → Flag → Bool) (i j : I) : (profileSamples p).leafWitness [] i j := by
  intro w on hi hj
  have pair : (profileSamples p).two i j w =
      ((profileSamples p).one i w || (profileSamples p).one j w) := by
    cases w <;> rfl
  rw [pair, hi, hj] at on
  contradiction

def active (p : I → Flag → Bool) (i : I) : Finset Flag :=
  univ.filter (p i · = true)

private def indicator {A : Type} [DecidableEq A] (a : A) : A → ℕ :=
  fun b => (singletonInput a b).toNat

private theorem mass (p : I → Flag → Bool) (i : I) :
    (profileSamples p).riseAt i =
      fun w => indicator (.inr i) w + ∑ k ∈ active p i, indicator (.inl k) w := by
  funext w
  cases w with
  | inr j =>
    simp [profileSamples, Samples.riseAt, assignment, rise, indicator, singletonInput]
  | inl k =>
    have value : (profileSamples p).riseAt i (.inl k) = (p i k).toNat := by
      simp [profileSamples, Samples.riseAt, assignment, rise]
    rw [value]
    have rawZero : indicator (.inr i) (Sum.inl k) = 0 := by simp [indicator, singletonInput]
    rw [rawZero, Nat.zero_add]
    by_cases on : p i k = true
    · have mem : k ∈ active p i := mem_filter.mpr ⟨mem_univ _, on⟩
      rw [sum_eq_single_of_mem k mem, on]
      · simp [indicator, singletonInput]
      · intro l _ ne
        simp [indicator, singletonInput, ne.symm]
    · have off : p i k = false := Bool.eq_false_iff.mpr on
      rw [off]
      symm
      apply sum_eq_zero
      intro l hl
      have ne : k ≠ l := by
        intro h
        subst l
        exact on (mem_filter.mp hl).2
      simp [indicator, singletonInput, ne]

private theorem weight_sum {K A : Type} (f : Formula A) (S : Finset K) (w : K → A → ℕ) :
    leafWeight f (fun a => ∑ k ∈ S, w k a) = ∑ k ∈ S, leafWeight f (w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => induction f <;> simp_all [leafWeight]
  | insert k S hk ih =>
    have eq : (fun a => ∑ j ∈ insert k S, w j a) =
        (fun a => w k a + ∑ j ∈ S, w j a) := by
      funext a
      rw [sum_insert hk]
    rw [eq, leafWeight_add, ih, sum_insert hk]

theorem weightOfProfile (f : Formula (Flag ⊕ I)) (p : I → Flag → Bool) (i : I) :
    leafWeight f ((profileSamples p).riseAt i) =
      reads f (.inr i) + ∑ k ∈ active p i, reads f (.inl k) := by
  rw [mass, leafWeight_add, weight_sum]
  rfl

/-- The output alone gives the cut bound whenever OR-closure makes the profile of
    a pair the union of the singleton profiles, even with dependencies among flags. -/
theorem profilePacking (f : Formula (Flag ⊕ I)) (p : I → Flag → Bool)
    (test : IndependentTests f p) (S : Finset I) (limit : I → ℕ) (ceiling : ℕ)
    (used : ∀ i ∈ S, reads f (.inr i) + ∑ k ∈ active p i, reads f (.inl k) ≤ limit i)
    (cap : ∀ i ∈ S, limit i ≤ ceiling) :
    ∑ i ∈ S, 2 ^ (ceiling - limit i) ≤ 2 ^ ceiling := by
  let s := profileSamples p
  refine CrownThreshold.weightedPacking S (rowCode (s.rows f)) limit ceiling ?_ ?_ cap
  · intro i _ j _ ne
    have sep := Samples.outputSeparates (onBase p) (leaves p i j) f (test.2 i j ne) (test.1 i) (test.1 j)
    exact rowCodeSeparates (by simpa only [List.nil_append] using sep)
  · intro i hi
    rw [fixedRowCode]
    have h := s.charge (onBase p) f i
    change _ ≤ leafWeight f ((profileSamples p).riseAt i) at h
    rw [weightOfProfile] at h
    exact (Nat.le_add_right ..).trans (h.trans (used i hi))

private theorem unionEq (a b : Flag → Bool) (lower : ∀ k, a k ≤ b k) :
    (fun k => a k || b k) = b := by
  have bit : ∀ x y : Bool, x ≤ y → (x || y) = y := by decide
  funext k
  exact bit (a k) (b k) (lower k)

theorem hiddenProfileCannotBeIncluded (f : Formula (Flag ⊕ I)) (p : I → Flag → Bool)
    (test : IndependentTests f p) {i j : I} (ne : i ≠ j)
    (hidden : reads f (.inr i) = 0) (contained : ∀ k, p i k ≤ p j k) : False := by
  have sameBits := unionEq (p i) (p j) contained
  let x := assignment (p j) (singletonInput j)
  let y := assignment (p j) (pairInput i j)
  have order (k : Flag ⊕ I) : x k ≤ y k := by
    cases k with
    | inl k => exact le_rfl
    | inr k => exact TwoShared.otherSingleton_pair i j k
  have mass : (fun k => rise (x k) (y k)) = indicator (.inr i) := by
    funext k
    cases k with
    | inl k => simp [x, y, assignment, rise, indicator, singletonInput]
    | inr k => simpa [x, y, assignment, indicator, singletonInput] using congrFun (TwoShared.addedInputRise i j ne) k
  have stable := eqOfNoRise f order (by rw [mass]; exact hidden)
  have accept := test.2 i j ne
  rw [sameBits, ← stable] at accept
  exact Bool.false_ne_true ((test.1 j).symm.trans accept)

private theorem setTwo_assign (bits : Flag → Bool) (x : I → Bool) (i j : I) (b c : Bool) :
    setTwo (assignment bits x) (Sum.inr i) (Sum.inr j) b c =
      assignment bits (setTwo x i j b c) := by
  funext k
  cases k <;> simp [setTwo, assignment]

theorem repeatedProfileCannotBeIncluded (f : Formula (Flag ⊕ I)) (p : I → Flag → Bool)
    (test : IndependentTests f p) {i j a : I} (ij : i ≠ j) (ia : i ≠ a) (ja : j ≠ a)
    (equal : p i = p j) (contained : ∀ k, p i k ≤ p a k)
    (ri : reads f (.inr i) ≤ 1) (rj : reads f (.inr j) ≤ 1) : False := by
  let u := assignment (p i) (fun _ : I => false)
  let v := assignment (p a) (singletonInput a)
  have joinij : (fun k => p i k || p j k) = p i := by
    rw [← equal]
    exact unionEq (p i) (p i) fun _ => le_rfl
  have joinia := unionEq (p i) (p a) contained
  have joinja : (fun k => p j k || p a k) = p a := by rw [← equal]; exact joinia
  obtain ⟨u10, u01, u11⟩ := CrownProfileThree.Network.setTwo_zero ij
  obtain ⟨v00, v10, v01⟩ := CrownProfileThree.Network.setTwo_one ia ja ij
  apply noAndToOr f (i := Sum.inr i) (j := Sum.inr j) (by simpa using ij) ri rj u v
  · rw [show u = assignment (p i) (fun _ : I => false) from rfl, setTwo_assign, u10]
    exact test.1 i
  · rw [show u = assignment (p i) (fun _ : I => false) from rfl, setTwo_assign, u01, equal]
    exact test.1 j
  · rw [show u = assignment (p i) (fun _ : I => false) from rfl, setTwo_assign, u11, ← joinij]
    exact test.2 i j ij
  · rw [show v = assignment (p a) (singletonInput a) from rfl, setTwo_assign, v00]
    exact test.1 a
  · rw [show v = assignment (p a) (singletonInput a) from rfl, setTwo_assign, v10, ← joinia]
    exact test.2 i a ia
  · rw [show v = assignment (p a) (singletonInput a) from rfl, setTwo_assign, v01, ← joinja]
    exact test.2 j a ja

end CrownOrPacking
