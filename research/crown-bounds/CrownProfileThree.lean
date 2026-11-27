import CrownProfiles
import CrownEight

namespace CrownProfileThree

open CrownForks CrownForest CrownProfiles PnpResearch Finset

structure Network (I : Type) where
  first : Formula I
  second : Formula (Option I)
  third : Formula (Option (Option I))
  output : Formula (Option (Option (Option I)))

namespace Network

variable {I : Type}

def forest (N : Network I) : SharedFormula I :=
  .share N.first 1 (.share N.second 1 (.share N.third 1 (.tree N.output)))

def signals (N : Network I) (x : I → Bool) : Option (Option (Option I)) → Bool :=
  let p := N.first.evalWith x
  let q := N.second.evalWith (withHead p x)
  let r := N.third.evalWith (withHead q (withHead p x))
  withHead r (withHead q (withHead p x))

theorem signals_mono (N : Network I) {x y : I → Bool} (le : ∀ i, x i ≤ y i) :
    ∀ a, N.signals x a ≤ N.signals y a := by
  let p := withHeadMono (evalMono N.first le) le
  let q := withHeadMono (evalMono N.second p) p
  exact withHeadMono (evalMono N.third q) q

def bits (N : Network I) (x : I → Bool) : Bool × Bool × Bool :=
  (N.signals x (some (some none)), N.signals x (some none), N.signals x none)

theorem profile_eq (N : Network I) (x : I → Bool) :
    profile N.forest x = [(N.bits x).1, (N.bits x).2.1, (N.bits x).2.2] := rfl

def load (b : Bool × Bool × Bool) : ℕ := b.1.toNat + b.2.1.toNat + b.2.2.toNat

variable [DecidableEq I]

def ones (i : I) : I → ℕ := fun k => (singletonInput i k).toNat

def firstRaw (N : Network I) (i : I) : ℕ := leafWeight N.first (ones i)

def secondRaw (N : Network I) (i : I) : ℕ := leafWeight N.second (withHead 0 (ones i))

def thirdRaw (N : Network I) (i : I) : ℕ := leafWeight N.third (withHead 0 (withHead 0 (ones i)))

def outputRaw (N : Network I) (i : I) : ℕ :=
  leafWeight N.output (withHead 0 (withHead 0 (withHead 0 (ones i))))

theorem weight_eq (N : Network I) (i : I) :
    N.forest.weight (ones i) = N.firstRaw i + N.secondRaw i + N.thirdRaw i + N.outputRaw i := by
  simp only [forest, SharedFormula.weight, firstRaw, secondRaw, thirdRaw, outputRaw, Nat.add_assoc]

omit [DecidableEq I] in
theorem eval_eq (N : Network I) (x : I → Bool) :
    N.forest.eval x = N.output.evalWith (N.signals x) := rfl

theorem halfPacking (N : Network I) (valid : N.forest.Valid) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2) (S : Finset I) :
    ∑ i ∈ S, 2 ^ (3 - load (N.bits (singletonInput i))) ≤ 32 := by
  have extra (i : I) : CrownSharedCuts.extraCharge N.forest (Samples.raw I) i =
      load (N.bits (singletonInput i)) := by
    simp only [forest, CrownSharedCuts.extraCharge, Samples.add, Samples.raw, evalZero,
      withHead_const, Nat.mul_one, Nat.add_zero]
    simp [bits, signals, load, rise, Nat.add_assoc]
  have within (i : I) : load (N.bits (singletonInput i)) ≤ 3 := by
    generalize N.bits (singletonInput i) = b
    rcases b with ⟨p, q, r⟩
    cases p <;> cases q <;> cases r <;> decide
  simpa only [Nat.sub_add_eq, show (5 : ℕ) - 2 = 3 from rfl,
    show (2 : ℕ) ^ 5 = 32 from rfl] using
    CrownSharedCuts.packing N.forest valid test S
      (fun i => 2 + load (N.bits (singletonInput i))) 5
      (fun i _ => by rw [extra]; exact Nat.add_le_add_right (reads i) _)
      (fun i _ => by have h := within i; omega)

theorem groupCapacity (N : Network I) (test : ThresholdOn N.forest.eval)
    (reads : ∀ i, N.forest.weight (ones i) ≤ 2) (S : Finset I) (b : Bool × Bool × Bool)
    (same : ∀ i ∈ S, N.bits (singletonInput i) = b) (active : b ≠ (false, false, false)) :
    S.card ≤ 2 := by
  apply profileCapacity N.forest test S [b.1, b.2.1, b.2.2]
  · intro i hi
    rw [profile_eq, same i hi]
  · exact fun i _ => reads i
  · rcases b with ⟨p, q, r⟩
    cases p <;> cases q <;> cases r <;> simp_all

theorem fullProfileForcesOutputRead (N : Network I) (test : ThresholdOn N.forest.eval)
    {i j : I} (ne : i ≠ j) (full : N.bits (singletonInput j) = (true, true, true)) :
    1 ≤ N.outputRaw i := by
  let x := withHead true (withHead true (withHead true (singletonInput j)))
  let y := withHead true (withHead true (withHead true (pairInput i j)))
  have all : N.bits (pairInput i j) = (true, true, true) := by
    have le := N.signals_mono (TwoShared.otherSingleton_pair i j)
    have p := congrArg Prod.fst full
    have q := congrArg (fun a => a.2.1) full
    have r := congrArg (fun a => a.2.2) full
    exact Prod.ext ((Bool.le_iff_imp.mp (le (some (some none)))) p)
      (Prod.ext ((Bool.le_iff_imp.mp (le (some none))) q) ((Bool.le_iff_imp.mp (le none)) r))
  have assign (z : I → Bool) (yes : N.bits z = (true, true, true)) :
      N.signals z = withHead true (withHead true (withHead true z)) := by
    have p := congrArg Prod.fst yes
    have q := congrArg (fun a => a.2.1) yes
    have r := congrArg (fun a => a.2.2) yes
    funext a
    rcases a with _ | _ | _ | a
    · exact r
    · exact q
    · exact p
    · rfl
  have off : N.output.evalWith x = false := by simpa only [eval_eq, assign _ full] using test.1 j
  have on : N.output.evalWith y = true := by simpa only [eval_eq, assign _ all] using test.2 i j ne
  have mono : ∀ a, x a ≤ y a :=
    withHeadMono le_rfl (withHeadMono le_rfl (withHeadMono le_rfl (TwoShared.otherSingleton_pair i j)))
  have mass : (fun a => rise (x a) (y a)) = withHead 0 (withHead 0 (withHead 0 (ones i))) := by
    funext a
    rcases a with _ | _ | _ | a
    · rfl
    · rfl
    · rfl
    · exact congrFun (TwoShared.addedInputRise i j ne) a
  by_contra! notRead
  have none : leafWeight N.output (fun a => rise (x a) (y a)) = 0 := by
    rw [mass]
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ notRead)
  rw [eqOfNoRise N.output mono none, on] at off
  contradiction

end Network

end CrownProfileThree
