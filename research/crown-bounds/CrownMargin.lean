import CrownProduct

namespace CrownMargin

open CrownRun CrownForks CrownForest PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.Represents PnpResearch

theorem forestAtMargin {n lower s : ℕ} {F : BF (n + 1)} (size : 2 ≤ n)
    (floor : CrownLower.LowerBound n lower) (cost : s ≤ lower + 2)
    (test : ThresholdOn F) (computes : CrownLower.Computes (n + 1) s F) :
    ∃ E : SharedFormula (Fin (n + 1)), E.Valid ∧ ThresholdOn E.eval ∧
      (∀ i, E.weight (fun j => (singletonInput i j).toNat) = 2) ∧
      E.extraUses + 2 * (n + 1) ≤ s + 1 := by
  classical
  have normal : ∃ (t : ℕ) (G : BF (n + 1)) (idx : List (Fin (n + 1))),
      MR [G] t (idx.map var) ∧ ThresholdOn G ∧ t ≤ s ∧ ∀ i, idx.count i = 2 := by
    by_contra missing
    exact CrownLower.cannotCompute size floor cost
      (fun {t G idx} run correct budget twice => missing ⟨t, G, idx, run, correct, budget, twice⟩)
      test computes le_rfl
  obtain ⟨t, G, idx, run, correct, budget, twice⟩ := normal
  have start : ((idx.map Formula.var).map (wire var)).Perm (idx.map var) := by
    rw [List.map_map]
    exact List.Perm.refl _
  obtain ⟨E, valid, eval, mass, steps⟩ := fromTrace run (Fin (n + 1)) var (idx.map Formula.var) start
  have labels : idx.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    apply List.mem_toFinset.mpr
    exact List.count_pos_iff.mp (by rw [twice]; decide)
  have nreads : idx.length = 2 * (n + 1) := by
    rw [← List.sum_toFinset_count_eq_length idx, labels]
    simp [twice]
    omega
  simp only [List.length_map, nreads] at steps
  have each (i : Fin (n + 1)) : E.weight (fun j => (singletonInput i j).toNat) = 2 := by
    rw [mass, stock_vars, twice]
  change E.eval = G at eval
  exact ⟨E, valid, eval.symm ▸ correct, each, by omega⟩

theorem tenBudget23Forest (h : CrownThreshold.HasThresholdTwo 10 23) :
    ∃ E : SharedFormula (Fin 10), E.Valid ∧ ThresholdOn E.eval ∧
      (∀ i, E.weight (fun j => (singletonInput i j).toNat) = 2) ∧ E.extraUses ≤ 4 := by
  obtain ⟨C, mono, cost, comp⟩ := h
  have tests := CrownLower.thresholdTwoTests 10
  have notOne : CrownThreshold.thresholdTwo (n := 10) ≠ oneF := by
    intro eq
    have bad := tests.1 0
    rw [eq] at bad
    simp [oneF] at bad
  obtain ⟨s, steps, idx, run⟩ := CrownRun.fromCircuit mono _ comp
    (CrownLower.thresholdNonzero (by decide) tests) notOne
  have computation : CrownLower.Computes 10 s CrownThreshold.thresholdTwo := by
    apply CrownLower.ucOfRun run
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    exact ⟨i, rfl⟩
  have floor : CrownLower.LowerBound 9 21 := CrownProduct.thresholdLowerFromEight 1
  obtain ⟨E, valid, correct, reads, extra⟩ :=
    forestAtMargin (by decide : 2 ≤ 9) floor (steps.trans cost) tests computation
  exact ⟨E, valid, correct, reads, by omega⟩

theorem crownTenBudget33 (h : RepSizeAtMost (fun u v : Fin 10 => decide (u ≠ v)) 33) :
    ∃ E : SharedFormula (Fin 10), E.Valid ∧ ThresholdOn E.eval ∧
      (∀ i, E.weight (fun j => (singletonInput i j).toNat) = 2) ∧ E.extraUses ≤ 4 :=
  tenBudget23Forest ((CrownThreshold.crownIffThreshold (n := 10) (budget := 23) (by decide)).mp h)

end CrownMargin
