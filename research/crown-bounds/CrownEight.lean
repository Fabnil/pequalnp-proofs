import CrownSharedCuts
import CrownLower

namespace CrownEight

open CrownRun CrownForks CrownForest CrownSharedCuts PnpResearch Finset
  PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

section Capacity

variable {I : Type} [DecidableEq I] [Fintype I]

private theorem oneSharedAtMostSix {p : Formula I} {out : Formula (Option I)} {u : ℕ}
    (ok : (SharedFormula.share p u (.tree out)).Valid)
    (test : ThresholdOn (SharedFormula.share p u (.tree out)).eval)
    (raw : ∀ i, (SharedFormula.share p u (.tree out)).weight
      (fun k => (singletonInput i k).toNat) ≤ 2) : Fintype.card I ≤ 6 := by
  let E : SharedFormula I := .share p u (.tree out)
  let hot (i : I) := p.evalWith (singletonInput i)
  let H := univ.filter fun i => hot i = true
  let C := univ.filter fun i => hot i = false
  have coldBound : C.card ≤ 4 := by
    have packed := packing E ok test C (fun _ => 2) 2 (by
      intro i hi
      have off := (Finset.mem_filter.mp hi).2
      have zero : extraCharge E (Samples.raw I) i = 0 := by
        simp [hot] at off
        simp [E, extraCharge, Samples.raw, rise, off]
      rw [zero, Nat.add_zero]
      exact raw i) (fun _ _ => le_rfl)
    simpa using packed
  let s := (Samples.raw I).freeze true
  have hotBound : H.card ≤ 2 := by
    refine Samples.formulaCapacity H s out
      (Samples.freeze_onBase _ Samples.raw_onBase _)
      (fun i j => Samples.freeze_leafWitness (Samples.raw_leafWitness i j) _) ?_ ?_ ?_
    · intro i hi
      have h := (Finset.mem_filter.mp hi).2
      change p.evalWith (singletonInput i) = true at h
      change out.evalWith (withHead true (singletonInput i)) = false
      simpa only [SharedFormula.eval, h] using test.1 i
    · intro i hi j _ ne
      have atOne := (Finset.mem_filter.mp hi).2
      have atPair := (Bool.le_iff_imp.mp (evalMono p (TwoShared.singleton_pair i j))) atOne
      change out.evalWith (withHead true (pairInput i j)) = true
      simpa only [SharedFormula.eval, atPair] using test.2 i j ne
    · intro i hi
      change leafWeight out (((Samples.raw I).freeze true).riseAt i) ≤ 1
      rw [Samples.freeze_riseAt, TwoShared.raw_rises]
      have atOne : p.evalWith (singletonInput i) = true := (Finset.mem_filter.mp hi).2
      have used : 1 ≤ leafWeight p (fun k => (singletonInput i k).toNat) := by
        by_contra! no
        have mass : leafWeight p ((Samples.raw I).riseAt i) = 0 := by
          rw [TwoShared.raw_rises]
          omega
        have e := eqOfNoRise p (Samples.raw_onBase i) mass
        change p.evalWith (fun _ => false) = p.evalWith (singletonInput i) at e
        simp [evalZero, atOne] at e
      have bound := raw i
      change leafWeight p (fun k => (singletonInput i k).toNat) +
        leafWeight out (withHead 0 fun k => (singletonInput i k).toNat) ≤ 2 at bound
      omega
  have complement : (univ.filter fun i : I => ¬ hot i = true) = C := by
    ext i
    cases h : hot i <;> simp [C, h]
  have split := Finset.card_filter_add_card_filter_not (s := (univ : Finset I)) (fun i => hot i = true)
  rw [complement] at split
  have h : H.card + C.card = Fintype.card I := by simpa [H] using split
  omega

private def cutLimit (p q : Bool) : ℕ := if p && q then 5 else if p || q then 4 else 2

private theorem twoSharedAtMostSeven {p : Formula I} {q : Formula (Option I)}
    {out : Formula (Option (Option I))} {u v : ℕ}
    (ok : (SharedFormula.share p u (.share q v (.tree out))).Valid)
    (test : ThresholdOn (SharedFormula.share p u (.share q v (.tree out))).eval)
    (raw : ∀ i, (SharedFormula.share p u (.share q v (.tree out))).weight
      (fun k => (singletonInput i k).toNat) ≤ 2)
    (reuse : u + v ≤ 3) : Fintype.card I ≤ 7 := by
  let E : SharedFormula I := .share p u (.share q v (.tree out))
  let N : TwoShared I := ⟨p, q, out⟩
  have correct : N.ThresholdTests := test
  have uses (i : I) : N.firstRaw i + N.secondRaw i + N.outputRaw i ≤ 2 := by
    simpa only [N, TwoShared.firstRaw, TwoShared.secondRaw, TwoShared.outputRaw,
      SharedFormula.weight, Nat.add_assoc] using raw i
  have up : 0 < u := ok.1
  have vp : 0 < v := ok.2.1.1
  have chargeEq (i : I) : extraCharge E (Samples.raw I) i = (N.pOn i).toNat * u + (N.qOn i).toNat * v := by
    have zero : ((Samples.raw I).add p).base = (fun _ => false) := by simp [Samples.add, Samples.raw, evalZero]
    change rise (p.evalWith (fun _ => false)) (N.pOn i) * u +
      (rise (q.evalWith ((Samples.raw I).add p).base) (N.qOn i) * v + 0) = _
    simp [zero, evalZero, rise]
  have packed := packing E ok test (univ : Finset I) (fun i => cutLimit (N.pOn i) (N.qOn i)) 5 (by
    intro i _
    rw [chargeEq]
    have w : E.weight (fun k => (singletonInput i k).toNat) ≤ 2 := raw i
    cases N.pOn i <;> cases N.qOn i <;> simp [cutLimit] <;> omega)
    (fun i _ => by cases N.pOn i <;> cases N.qOn i <;> decide)
  let c := (N.group false false).card
  let a := (N.group true false).card
  let b := (N.group false true).card
  let d := (N.group true true).card
  have weight (i : I) : 2 ^ (5 - cutLimit (N.pOn i) (N.qOn i)) =
      (if N.pOn i = false ∧ N.qOn i = false then 8 else 0) +
      (if N.pOn i = true ∧ N.qOn i = false then 2 else 0) +
      (if N.pOn i = false ∧ N.qOn i = true then 2 else 0) +
      (if N.pOn i = true ∧ N.qOn i = true then 1 else 0) := by
    cases N.pOn i <;> cases N.qOn i <;> decide
  simp only [weight] at packed
  have bound : 8 * c + 2 * a + 2 * b + d ≤ 32 := by
    simpa [c, a, b, d, TwoShared.group, sum_add_distrib, sum_ite, Nat.mul_comm] using packed
  have count : Fintype.card I = c + a + b + d := by
    calc
      _ = ∑ i : I, (1 : ℕ) := by simp
      _ = ∑ i : I, ((if N.pOn i = false ∧ N.qOn i = false then 1 else 0) +
          (if N.pOn i = true ∧ N.qOn i = false then 1 else 0) +
          (if N.pOn i = false ∧ N.qOn i = true then 1 else 0) +
          (if N.pOn i = true ∧ N.qOn i = true then 1 else 0)) := by
        apply sum_congr rfl
        intro i _
        cases N.pOn i <;> cases N.qOn i <;> decide
      _ = _ := by simp [c, a, b, d, TwoShared.group, sum_add_distrib]
  have ha : a ≤ 2 := N.leftCapacity correct uses
  have hb : b ≤ 2 := N.rightCapacity correct uses
  have hd : d ≤ 2 := N.bothCapacity correct uses
  by_cases eq : d = 2
  · have zero : a = 0 := N.linked correct uses eq
    omega
  · omega

end Capacity

abbrev Eight := Fin 8

private theorem exactlyThree (E : SharedFormula Eight) (ok : E.Valid) (test : ThresholdOn E.eval)
    (raw : ∀ i, E.weight (fun k => (singletonInput i k).toNat) ≤ 2) (budget : E.extraUses ≤ 3) :
    ∃ (p : Formula Eight) (q : Formula (Option Eight)) (r : Formula (Option (Option Eight)))
      (out : Formula (Option (Option (Option Eight)))), E = .share p 1 (.share q 1 (.share r 1 (.tree out))) := by
  cases E with
  | tree out =>
    have h := formulaThresholdCapacity out test raw
    simp at h
  | share p u tail =>
    cases tail with
    | tree out =>
      have h := oneSharedAtMostSix ok test raw
      simp at h
    | share q v tail =>
      cases tail with
      | tree out =>
        have uv : u + v ≤ 3 := by simpa [SharedFormula.extraUses] using budget
        have h := twoSharedAtMostSeven ok test raw uv
        simp at h
      | share r w tail =>
        have hu : 0 < u := ok.1
        have hv : 0 < v := ok.2.1.1
        have hw : 0 < w := ok.2.1.2.1.1
        have count : u + (v + (w + tail.extraUses)) ≤ 3 := budget
        have e₁ : u = 1 := by omega
        have e₂ : v = 1 := by omega
        have e₃ : w = 1 := by omega
        cases tail with
        | tree out => exact ⟨p, q, r, out, by rw [e₁, e₂, e₃]⟩
        | share f n end' =>
          have npos : 0 < n := ok.2.1.2.1.2.1.1
          simp only [SharedFormula.extraUses] at count
          omega

theorem threeSharedForReadTwice {s : ℕ} {F : BF 8} {idx : List Eight}
    (run : MR [F] s (idx.map var)) (test : ThresholdOn F) (budget : s ≤ 18)
    (twice : ∀ i, idx.count i = 2) :
    ∃ (p : Formula Eight) (q : Formula (Option Eight)) (r : Formula (Option (Option Eight)))
      (out : Formula (Option (Option (Option Eight)))),
      let E : SharedFormula Eight := .share p 1 (.share q 1 (.share r 1 (.tree out)))
      E.Valid ∧ E.eval = F ∧ ∀ i, E.weight (fun k => (singletonInput i k).toNat) = 2 := by
  have start : ((idx.map Formula.var).map (wire var)).Perm (idx.map var) := by
    rw [List.map_map]
    exact List.Perm.refl _
  obtain ⟨E, ok, compute, mass, time⟩ := fromTrace run Eight var (idx.map Formula.var) start
  have all : idx.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    apply List.mem_toFinset.mpr
    exact List.count_pos_iff.mp (by rw [twice]; decide)
  have length : idx.length = 16 := by
    rw [← List.sum_toFinset_count_eq_length idx, all]
    simp [twice]
  simp only [List.length_map, length] at time
  have extra : E.extraUses ≤ 3 := by omega
  have counts (i : Eight) : E.weight (fun k => (singletonInput i k).toNat) = 2 := by
    rw [mass, stock_vars, twice]
  change E.eval = F at compute
  obtain ⟨p, q, r, out, rfl⟩ := exactlyThree E ok (compute.symm ▸ test) (fun i => (counts i).le) extra
  exact ⟨p, q, r, out, ok, compute, counts⟩

def HasThreeSharedThreshold : Prop :=
  ∃ (p : Formula Eight) (q : Formula (Option Eight)) (r : Formula (Option (Option Eight)))
    (out : Formula (Option (Option (Option Eight)))),
    let E : SharedFormula Eight := .share p 1 (.share q 1 (.share r 1 (.tree out)))
    E.Valid ∧ ThresholdOn E.eval ∧ ∀ i, E.weight (fun k => (singletonInput i k).toNat) = 2

theorem budget18RequiresThree {s : ℕ} {F : BF 8} (test : ThresholdOn F)
    (compute : CrownLower.Computes 8 s F) (budget : s ≤ 18) : HasThreeSharedThreshold := by
  have normalized : ∃ (t : ℕ) (G : BF 8) (idx : List Eight),
      MR [G] t (idx.map var) ∧ ThresholdOn G ∧ t ≤ 18 ∧ ∀ i, idx.count i = 2 := by
    by_contra missing
    exact CrownLower.cannotCompute (n := 7) (budget := 18) (by decide)
      (CrownLower.lowerUpToSeven 7 (by decide) (by decide)) (by decide)
      (fun {t G idx} run correct size all => missing ⟨t, G, idx, run, correct, size, all⟩)
      test compute budget
  obtain ⟨t, G, idx, run, correct, size, twice⟩ := normalized
  obtain ⟨p, q, r, out, valid, eval, counts⟩ := threeSharedForReadTwice run correct size twice
  exact ⟨p, q, r, out, valid, eval.symm ▸ correct, counts⟩

theorem crown26RequiresThree (small : RepSizeAtMost (fun u v : Fin 8 => decide (u ≠ v)) 26) :
    HasThreeSharedThreshold := by
  obtain ⟨C, mono, cost, correct⟩ :=
    (CrownThreshold.crownIffThreshold (n := 8) (budget := 18) (by decide)).mp small
  have test := CrownLower.thresholdTwoTests 8
  have notOne : (CrownThreshold.thresholdTwo (n := 8)) ≠ oneF := by
    intro e
    have h := test.1 0
    rw [e] at h
    simp [oneF] at h
  obtain ⟨t, size, idx, run⟩ := CrownRun.fromCircuit mono _ correct
    (CrownLower.thresholdNonzero (by decide) test) notOne
  have compute : CrownLower.Computes 8 t CrownThreshold.thresholdTwo := by
    apply CrownLower.ucOfRun run
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    exact ⟨i, rfl⟩
  exact budget18RequiresThree test compute (size.trans cost)

def eightWitness : Circuit :=
  let lift (wire : ℕ) := if wire < 7 then wire else wire + 1
  ⟨CrownLower.sevenWitness.gates.map (fun g => ⟨g.op, g.inputs.map lift⟩) ++
    [⟨.or, [21, 6]⟩, ⟨.and, [24, 7]⟩, ⟨.or, [23, 25]⟩], 26⟩

set_option maxRecDepth 8192 in
private theorem eightWitnessCorrect : ∀ x : Fin 8 → Bool,
    eightWitness.eval (List.ofFn x) = CrownThreshold.thresholdTwo x := by
  decide +kernel

theorem crownUpper27 : RepSizeAtMost (fun u v : Fin 8 => decide (u ≠ v)) 27 := by
  apply (CrownThreshold.crownIffThreshold (n := 8) (budget := 19) (by decide)).mpr
  exact ⟨eightWitness, by simp [Monotone2, eightWitness, CrownLower.sevenWitness], by decide, eightWitnessCorrect⟩

end CrownEight
