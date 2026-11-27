import CrownMargin

namespace CrownFourNormal

open CrownRun CrownForks CrownForest CrownProfiles CrownSharedCuts PnpResearch Finset

private theorem extraBound {A I : Type} (E : SharedFormula A) (s : Samples I A) (i : I) :
    extraCharge E s i ≤ E.extraUses := by
  induction E with
  | tree f => rfl
  | share f u tail ih =>
    have bit : rise (f.evalWith s.base) (f.evalWith (s.one i)) ≤ 1 := by
      cases f.evalWith s.base <;> cases f.evalWith (s.one i) <;> decide
    simp only [extraCharge, SharedFormula.extraUses]
    exact Nat.add_le_add (by simpa using Nat.mul_le_mul_right u bit) (ih (s.add f))

private theorem extraZero {A I : Type} (E : SharedFormula A) (s : Samples I A) (i : I)
    (none : true ∉ profile E (s.one i)) : extraCharge E s i = 0 := by
  induction E with
  | tree f => rfl
  | share f u tail ih =>
    have off : f.evalWith (s.one i) = false := by
      cases h : f.evalWith (s.one i) with
      | false => rfl
      | true => exact (none (by simp [profile, h])).elim
    have after : true ∉ profile tail ((s.add f).one i) := by
      intro active
      exact none (List.mem_cons_of_mem _ active)
    simp [extraCharge, rise, off, ih (s.add f) after]

variable {I : Type} [Fintype I] [DecidableEq I]

def emptyProfiles (E : SharedFormula I) : Finset I :=
  univ.filter fun i => true ∉ profile E (singletonInput i)

theorem emptyProfileCount (E : SharedFormula I) (valid : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ i, E.weight (CrownProfileThree.Network.ones i) ≤ 2)
    (big : 4 < Fintype.card I) : (emptyProfiles E).card ≤ 3 := by
  let c := emptyProfiles E
  let h := univ.filter fun i : I => ¬ (true ∉ profile E (singletonInput i))
  let limit (i : I) := if true ∉ profile E (singletonInput i) then 2 else 2 + E.extraUses
  let weight (i : I) := 2 ^ ((2 + E.extraUses) - limit i)
  let W := 2 ^ E.extraUses
  have cap : (∑ i : I, weight i) ≤ 4 * W := by
    have pack := packing E valid test univ limit (2 + E.extraUses)
      (fun i _ => by
        by_cases off : true ∉ profile E (singletonInput i)
        · have z := extraZero E (Samples.raw I) i off
          rw [show limit i = 2 by simp [limit, off], z, Nat.add_zero]
          exact raw i
        · have up := extraBound E (Samples.raw I) i
          simp only [limit, ite_eq_right off]
          exact Nat.add_le_add (raw i) up)
      (fun i _ => by simp [limit]; split <;> omega)
    rw [Nat.pow_add] at pack
    exact pack
  have count : c.card + h.card = Fintype.card I := by
    simpa [c, h, emptyProfiles] using
      card_filter_add_card_filter_not (s := (univ : Finset I))
        (fun i => true ∉ profile E (singletonInput i))
  have weights : (∑ i ∈ c, weight i) + (∑ i ∈ h, weight i) = ∑ i : I, weight i :=
    sum_filter_add_sum_filter_not (s := univ) (p := fun i => true ∉ profile E (singletonInput i)) _
  have cold : (∑ i ∈ c, weight i) = c.card * W := by
    apply sum_const_nat
    intro i hi
    have off := (mem_filter.mp (show i ∈ emptyProfiles E from hi)).2
    have diff : 2 + E.extraUses - 2 = E.extraUses := by omega
    simp only [weight, limit, ite_eq_left off, diff, W]
  have hot : h.card ≤ ∑ i ∈ h, weight i := by
    calc
      h.card = ∑ i ∈ h, (1 : ℕ) := by simp
      _ ≤ ∑ i ∈ h, weight i := sum_le_sum fun i _ => Nat.pow_pos (by decide)
  have bound : c.card * W + h.card ≤ 4 * W := by omega
  change c.card ≤ 3
  by_contra! many
  by_cases eq : c.card = 4
  · rw [eq] at count bound
    omega
  · have larger : 4 < c.card := by omega
    have pos : 0 < W := Nat.pow_pos (by decide)
    have more : 4 * W < c.card * W := Nat.mul_lt_mul_of_pos_right larger pos
    exact (not_lt_of_ge ((Nat.le_add_right _ _).trans bound)) more

private theorem oneSharedAtMostNine (p : Formula I) (u : ℕ) (h : Formula (Option I))
    (test : ThresholdOn (SharedFormula.share p u (.tree h)).eval)
    (raw : ∀ i, (SharedFormula.share p u (.tree h)).weight (CrownProfileThree.Network.ones i) ≤ 2)
    (cold : (emptyProfiles (.share p u (.tree h))).card ≤ 3) : Fintype.card I ≤ 9 := by
  let N : CrownProfileThree.Network I := ⟨p, .var none, .var none, rename h (fun a => some (some a))⟩
  have empty : N.count (false, false, false) = (emptyProfiles (.share p u (.tree h))).card := by
    change (univ.filter fun i => N.bits (singletonInput i) = (false, false, false)).card = _
    apply congrArg Finset.card
    ext i
    cases value : p.evalWith (singletonInput i) <;>
      simp [N, CrownProfileThree.Network.bits, CrownProfileThree.Network.signals, Formula.evalWith,
        emptyProfiles, profile, value]
  refine N.atMostNineOfFewEmpty ?_ ?_ (empty ▸ cold)
  · simpa [N, CrownProfileThree.Network.forest, SharedFormula.eval, Formula.evalWith, eval_rename,
      Function.comp_def] using test
  · simpa [N, CrownProfileThree.Network.forest, SharedFormula.weight, leafWeight, weight_rename,
      Function.comp_def] using raw

private theorem twoSharedAtMostNine (p : Formula I) (u : ℕ) (q : Formula (Option I)) (v : ℕ)
    (h : Formula (Option (Option I)))
    (test : ThresholdOn (SharedFormula.share p u (.share q v (.tree h))).eval)
    (raw : ∀ i, (SharedFormula.share p u (.share q v (.tree h))).weight
      (CrownProfileThree.Network.ones i) ≤ 2)
    (cold : (emptyProfiles (.share p u (.share q v (.tree h)))).card ≤ 3) : Fintype.card I ≤ 9 := by
  let N : CrownProfileThree.Network I := ⟨p, q, .var none, rename h some⟩
  have empty : N.count (false, false, false) = (emptyProfiles (.share p u (.share q v (.tree h)))).card := by
    change (univ.filter fun i => N.bits (singletonInput i) = (false, false, false)).card = _
    apply congrArg Finset.card
    ext i
    simp only [emptyProfiles, mem_filter, mem_univ, true_and]
    let a := p.evalWith (singletonInput i)
    let b := q.evalWith (withHead a (singletonInput i))
    change (a, b, b) = (false, false, false) ↔ true ∉ [a, b]
    have rule : ∀ x y : Bool, (x, y, y) = (false, false, false) ↔ true ∉ [x, y] := by
      decide +kernel
    exact rule a b
  refine N.atMostNineOfFewEmpty ?_ ?_ (empty ▸ cold)
  · simpa [N, CrownProfileThree.Network.forest, SharedFormula.eval, Formula.evalWith, eval_rename,
      Function.comp_def] using test
  · simpa [N, CrownProfileThree.Network.forest, SharedFormula.weight, leafWeight, weight_rename,
      Function.comp_def] using raw

private theorem threeSharedAtMostNine (p : Formula I) (u : ℕ) (q : Formula (Option I)) (v : ℕ)
    (r : Formula (Option (Option I))) (w : ℕ) (h : Formula (Option (Option (Option I))))
    (test : ThresholdOn (SharedFormula.share p u (.share q v (.share r w (.tree h)))).eval)
    (raw : ∀ i, (SharedFormula.share p u (.share q v (.share r w (.tree h)))).weight
      (CrownProfileThree.Network.ones i) ≤ 2)
    (cold : (emptyProfiles (.share p u (.share q v (.share r w (.tree h))))).card ≤ 3) :
    Fintype.card I ≤ 9 := by
  let N : CrownProfileThree.Network I := ⟨p, q, r, h⟩
  have empty : N.count (false, false, false) =
      (emptyProfiles (.share p u (.share q v (.share r w (.tree h))))).card := by
    change (univ.filter fun i => N.bits (singletonInput i) = (false, false, false)).card = _
    apply congrArg Finset.card
    ext i
    have same : profile (.share p u (.share q v (.share r w (.tree h)))) (singletonInput i) =
        [(N.bits (singletonInput i)).1, (N.bits (singletonInput i)).2.1, (N.bits (singletonInput i)).2.2] := rfl
    simp only [emptyProfiles, mem_filter, mem_univ, true_and, same]
    generalize N.bits (singletonInput i) = b
    revert b
    decide +kernel
  exact N.atMostNineOfFewEmpty test raw (empty ▸ cold)

theorem atLeastFour (E : SharedFormula I) (valid : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ i, E.weight (CrownProfileThree.Network.ones i) ≤ 2)
    (big : 10 ≤ Fintype.card I) :
    ∃ (p : Formula I) (u : ℕ) (q : Formula (Option I)) (v : ℕ)
      (r : Formula (Option (Option I))) (w : ℕ) (s : Formula (Option (Option (Option I))))
      (z : ℕ) (tail : SharedFormula (Option (Option (Option (Option I))))),
      E = .share p u (.share q v (.share r w (.share s z tail))) := by
  have cold := emptyProfileCount E valid test raw (by omega)
  cases E with
  | tree f =>
    have few := formulaThresholdCapacity f test raw
    omega
  | share p u tail =>
    cases tail with
    | tree h =>
      have few := oneSharedAtMostNine p u h test raw cold
      omega
    | share q v tail =>
      cases tail with
      | tree h =>
        have few := twoSharedAtMostNine p u q v h test raw cold
        omega
      | share r w tail =>
        cases tail with
        | tree h =>
          have few := threeSharedAtMostNine p u q v r w h test raw cold
          omega
        | share s z tail => exact ⟨p, u, q, v, r, w, s, z, tail, rfl⟩

theorem exactlyFour (E : SharedFormula I) (valid : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ i, E.weight (CrownProfileThree.Network.ones i) ≤ 2)
    (big : 10 ≤ Fintype.card I) (reuse : E.extraUses ≤ 4) :
    ∃ (p : Formula I) (q : Formula (Option I)) (r : Formula (Option (Option I)))
      (s : Formula (Option (Option (Option I)))) (h : Formula (Option (Option (Option (Option I))))),
      E = .share p 1 (.share q 1 (.share r 1 (.share s 1 (.tree h)))) := by
  obtain ⟨p, u, q, v, r, w, s, z, tail, rfl⟩ := atLeastFour E valid test raw big
  have up : 0 < u := valid.1
  have vp : 0 < v := valid.2.1.1
  have wp : 0 < w := valid.2.1.2.1.1
  have zp : 0 < z := valid.2.1.2.1.2.1.1
  cases tail with
  | tree h =>
    simp only [SharedFormula.extraUses] at reuse
    obtain ⟨rfl, rfl, rfl, rfl⟩ : u = 1 ∧ v = 1 ∧ w = 1 ∧ z = 1 := by omega
    exact ⟨p, q, r, s, h, rfl⟩
  | share t a tail =>
    have ap : 0 < a := valid.2.1.2.1.2.1.2.1.1
    simp only [SharedFormula.extraUses] at reuse
    omega

end CrownFourNormal

namespace CrownFourNormal

open CrownForks CrownForest PnpResearch PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.Represents

abbrev Ten := Fin 10

def HasFourSharedThreshold : Prop :=
  ∃ (p : Formula Ten) (q : Formula (Option Ten)) (r : Formula (Option (Option Ten)))
    (s : Formula (Option (Option (Option Ten)))) (h : Formula (Option (Option (Option (Option Ten))))),
    let E : SharedFormula Ten := .share p 1 (.share q 1 (.share r 1 (.share s 1 (.tree h))))
    E.Valid ∧ ThresholdOn E.eval ∧ ∀ i, E.weight (CrownProfileThree.Network.ones i) = 2

theorem crownTenRequiresFour (small : RepSizeAtMost (fun u v : Fin 10 => decide (u ≠ v)) 33) :
    HasFourSharedThreshold := by
  obtain ⟨E, valid, test, raw, reuse⟩ := CrownMargin.crownTenBudget33 small
  obtain ⟨p, q, r, s, h, rfl⟩ := exactlyFour E valid test (fun i => (raw i).le) (by decide) reuse
  exact ⟨p, q, r, s, h, valid, test, raw⟩

end CrownFourNormal
