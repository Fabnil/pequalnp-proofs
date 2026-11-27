import CrownVisibility

namespace CrownFourProfiles

open CrownForks CrownForest CrownProfiles CrownSharedCuts CrownVisibility Finset
open CrownProfileThree.Network (ones)

variable {A I : Type}

def numShared {A : Type} : SharedFormula A → ℕ
  | .tree _ => 0
  | .share _ _ rest => numShared rest + 1

@[simp] theorem profile_length (E : SharedFormula A) (x : A → Bool) :
    (profile E x).length = numShared E := by
  induction E with
  | tree f => rfl
  | share f u rest ih => simp [profile, numShared, ih]

theorem stageWeight_pos (E : SharedFormula A) (w : A → ℕ) (k : ℕ)
    (positive : 0 < stageWeight E w k) : k < numShared E := by
  induction E generalizing k with
  | tree f => simp [stageWeight] at positive
  | share f u rest ih =>
    cases k with
    | zero => simp [numShared]
    | succ k =>
      have tail := ih (withHead 0 w) k positive
      simpa only [numShared] using Nat.succ_lt_succ tail

theorem firstHot_lt (E : SharedFormula A) (x : A → Bool) (hot : true ∈ profile E x) :
    firstHot E x < numShared E := by
  rw [← profile_length E x]
  exact List.findIdx_lt_length_of_exists ⟨true, hot, rfl⟩

def full (E : SharedFormula A) (x : A → Bool) : Prop :=
  ∀ k < numShared E, bitAt (profile E x) k = true

theorem fullForcesVisible [DecidableEq I] (E : SharedFormula I) (test : ThresholdOn E.eval)
    {i a : I} (ne : i ≠ a) (cover : full E (singletonInput a)) : 0 < outputWeight E (ones i) := by
  have same := (pairStable E i a fun k positive => cover k (stageWeight_pos E _ k positive)).2
  by_contra! no
  have eq := same (Nat.eq_zero_of_le_zero no)
  rw [test.2 i a ne, test.1 a] at eq
  contradiction

/-- A full singleton leaves at most one nonempty profile per first active
    stage among the other inputs. -/
theorem cardLeOfFull [Fintype I] [DecidableEq I] (E : SharedFormula I)
    (test : ThresholdOn E.eval) (raw : ∀ i, E.weight (ones i) ≤ 2)
    (cold : (CrownFourNormal.emptyProfiles E).card ≤ 3)
    {a : I} (cover : full E (singletonInput a)) : Fintype.card I ≤ numShared E + 4 := by
  let other := univ.filter fun i : I => i ≠ a ∧ true ∈ profile E (singletonInput i)
  have small : other.card ≤ numShared E := by
    rw [← card_range (numShared E)]
    apply card_le_card_of_injOn (fun i => firstHot E (singletonInput i))
    · intro i hi
      exact mem_range.mpr (firstHot_lt E _ (mem_filter.mp hi).2.2)
    · intro i hi j hj same
      by_contra ne
      have pi := (mem_filter.mp hi).2
      have pj := (mem_filter.mp hj).2
      exact twoVisible E test ne pi.1 pj.1 pi.2 pj.2 (fullForcesVisible E test pi.1 cover)
        (fullForcesVisible E test pj.1 cover) (raw i) (raw j) same
        (cover _ (firstHot_lt E _ pi.2))
  have covered : (univ : Finset I) ⊆ insert a (other ∪ CrownFourNormal.emptyProfiles E) := by
    intro i _
    by_cases same : i = a
    · simp [same]
    · by_cases hot : true ∈ profile E (singletonInput i)
      · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, same, hot⟩))
      · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hot⟩))
  have total := card_le_card covered
  rw [card_univ] at total
  have union := card_union_le other (CrownFourNormal.emptyProfiles E)
  have addHead := card_insert_le a (other ∪ CrownFourNormal.emptyProfiles E)
  omega

theorem noFull [Fintype I] [DecidableEq I] (E : SharedFormula I)
    (valid : E.Valid) (test : ThresholdOn E.eval) (raw : ∀ i, E.weight (ones i) ≤ 2)
    (large : 10 ≤ Fintype.card I) (four : numShared E = 4) (i : I) :
    ¬ full E (singletonInput i) := by
  intro cover
  have cold := CrownFourNormal.emptyProfileCount E valid test raw (by omega)
  have total := cardLeOfFull E test raw cold cover
  omega

def twoReads {A : Type} : SharedFormula A → Prop
  | .tree _ => True
  | .share _ extra tail => extra = 1 ∧ twoReads tail

private theorem extra_le_count (E : SharedFormula A) (reuse : twoReads E) (s : Samples I A) (i : I) :
    extraCharge E s i ≤ (profile E (s.one i)).count true := by
  induction E with
  | tree f => rfl
  | share f u tail ih =>
    have b := ih reuse.2 (s.add f)
    change extraCharge tail (s.add f) i ≤
      (profile tail (withHead (f.evalWith (s.one i)) (s.one i))).count true at b
    have repeats : u = 1 := reuse.1
    cases h : f.evalWith (s.base) <;> cases g : f.evalWith (s.one i) <;>
      simp [extraCharge, repeats, rise, h, g, profile] at * <;> omega

theorem packing64 [Fintype I] [DecidableEq I] (E : SharedFormula I)
    (valid : E.Valid) (test : ThresholdOn E.eval) (raw : ∀ i, E.weight (ones i) ≤ 2)
    (four : numShared E = 4) (reuse : twoReads E) :
    ∑ i : I, 2 ^ (4 - (profile E (singletonInput i)).count true) ≤ 64 := by
  let weight (i : I) := (profile E (singletonInput i)).count true
  have bounded (i : I) : weight i ≤ 4 := by
    have h := List.count_le_length (a := true) (l := profile E (singletonInput i))
    simpa only [weight, profile_length, four] using h
  have bound := packing E valid test univ (fun i => 2 + weight i) 6
    (fun i _ => Nat.add_le_add (raw i) (extra_le_count E reuse (Samples.raw I) i))
    (fun i _ => by have h := bounded i; omega)
  have exponent (i : I) : 6 - (2 + weight i) = 4 - weight i := by omega
  simpa only [exponent, weight, show (2 : ℕ) ^ 6 = 64 by rfl] using bound

end CrownFourProfiles
