import CrownFourNetwork
import CrownHiddenReads

namespace CrownFourthStructure

open CrownForks CrownForest CrownProfiles CrownVisibility CrownFirstAnd CrownFourProfiles
open CrownFourNetwork CrownFourNormal CrownForestCost CrownHiddenReads CrownOrReaders
open CrownProfileThree.Network (ones)

structure Case (N : Network Ten) where
  valid : N.forest.Valid
  test : ThresholdOn N.forest.eval
  raw : ∀ i, N.forest.weight (ones i) = 2
  early : CrownOrStages.orPrefix N.forest 3
  a : Ten
  p : Fin 3
  q : Fin 3
  missing : Fin 3
  pq : p ≠ q
  pm : p ≠ missing
  qm : q ≠ missing
  onP : signal N.forest p.val (singletonInput a) = true
  onQ : signal N.forest q.val (singletonInput a) = true
  onLast : N.last (singletonInput a) = true
  offMissing : signal N.forest missing.val (singletonInput a) = false
  pNotQ : ¬ ∀ x, signal N.forest p.val x ≤ signal N.forest q.val x
  qNotP : ¬ ∀ x, signal N.forest q.val x ≤ signal N.forest p.val x
  noBoth : ∀ i, i ≠ a →
    ¬ (signal N.forest p.val (singletonInput i) = true ∧ signal N.forest q.val (singletonInput i) = true)

theorem ofOverlap (hyp : HasOverlapAt 3) : ∃ N : Network Ten, Nonempty (Case N) := by
  obtain ⟨p, q, r, s, h, early, valid, test, raw, a, overlap, onLast⟩ := hyp
  let N : Network Ten := ⟨⟨p, q, r, s⟩, h⟩
  change earlierOverlap N.forest 3 a at overlap
  obtain ⟨j, k, hj, hk, ne, onJ, onK, notJK, notKJ⟩ := overlap
  let m := 3 - (j + k)
  have rangeM : m < 3 := by dsimp [m]; omega
  have jm : j ≠ m := by dsimp [m]; omega
  have km : k ≠ m := by dsimp [m]; omega
  let P : Fin 3 := ⟨j, hj⟩
  let Q : Fin 3 := ⟨k, hk⟩
  let M : Fin 3 := ⟨m, rangeM⟩
  have facts := readersOfOverlap N.forest valid test (fun i => (raw i).le) N.numShared_eq
    (by decide) early hj hk ne a onJ onK onLast notJK notKJ
  have offM := facts.2.2.2.1 m (by omega) (fun h => jm h.symm) (fun h => km h.symm) (by omega)
  refine ⟨N, ⟨⟨valid, test, raw, early, a, P, Q, M, ?_, ?_, ?_, onJ, onK, onLast, offM, notJK,
    notKJ, facts.2.2.2.2⟩⟩⟩
  · exact fun same => ne (congrArg Fin.val same)
  · exact fun same => jm (congrArg Fin.val same)
  · exact fun same => km (congrArg Fin.val same)

namespace Case

variable {N : Network Ten} (C : Case N)

theorem anchor_on_except_missing (k : ℕ) (inside : k < 4) (ne : k ≠ C.missing.val) :
    signal N.forest k (singletonInput C.a) = true := by
  have rangeP := C.p.isLt
  have rangeQ := C.q.isLt
  have rangeM := C.missing.isLt
  have pq : C.p.val ≠ C.q.val := fun h => C.pq (Fin.ext h)
  have pm : C.p.val ≠ C.missing.val := fun h => C.pm (Fin.ext h)
  have qm : C.q.val ≠ C.missing.val := fun h => C.qm (Fin.ext h)
  have options : k = C.p.val ∨ k = C.q.val ∨ k = 3 := by omega
  rcases options with h | h | rfl
  · rw [h]
    exact C.onP
  · rw [h]
    exact C.onQ
  · exact C.onLast

/-- A different input absent from the output must be read by the one signal
    that is zero on the distinguished singleton. -/
theorem hidden_reads_missing {i : Ten} (ne : i ≠ C.a)
    (absent : outputWeight N.forest (ones i) = 0) : N.stages.rawAt C.missing.castSucc i = 1 := by
  have count := N.rawAt_eq C.missing.castSucc i
  change N.stages.rawAt C.missing.castSucc i = stageWeight N.forest (ones i) C.missing.val at count
  have size := (fourWithTwoReadsCosts23 N.forest C.valid C.raw rfl).le
  have maximum := hiddenStageAtMostOne N.forest C.valid C.test size i C.missing.val (C.raw i).le absent
  have positive : 0 < N.stages.rawAt C.missing.castSucc i := by
    by_contra! zero
    have same := (pairStable N.forest i C.a (by
      intro k pos
      have inside := stageWeight_pos N.forest (ones i) k pos
      rw [N.numShared_eq] at inside
      apply C.anchor_on_except_missing k inside
      intro eq
      rw [eq] at pos
      omega)).2 absent
    rw [C.test.2 i C.a ne, C.test.1 C.a] at same
    contradiction
  omega

theorem hidden_activates_missing {i : Ten} (ne : i ≠ C.a)
    (absent : outputWeight N.forest (ones i) = 0) : signal N.forest C.missing.val (singletonInput i) = true := by
  have pure := orPrefix_mono N.forest (show C.missing.castSucc.val + 1 ≤ 3 by
    have range := C.missing.isLt
    change C.missing.val + 1 ≤ 3
    omega) C.early
  exact N.direct_or_on C.missing.castSucc i pure (by rw [C.hidden_reads_missing ne absent]; decide)

theorem cold_is_visible {i : Ten} (ne : i ≠ C.a) (cold : true ∉ profile N.forest (singletonInput i)) :
    0 < outputWeight N.forest (ones i) := by
  by_contra! hidden
  have on := C.hidden_activates_missing ne (by omega : outputWeight N.forest (ones i) = 0)
  have some : (profile N.forest (singletonInput i))[C.missing.val]? = Option.some true := by
    cases entry : (profile N.forest (singletonInput i))[C.missing.val]? <;>
      simp_all [signal, bitAt]
  exact cold (List.mem_of_getElem? some)

include C in
theorem stage_active (k : Fin 4) : ∃ i, signal N.forest k.val (singletonInput i) = true := by
  have size := (fourWithTwoReadsCosts23 N.forest C.valid C.raw rfl).le
  have active := CrownDropZero.tenAllActive N.forest C.valid C.test size
  fin_cases k
  · exact active.1
  · exact active.2.1
  · exact active.2.2.1
  · exact active.2.2.2.1

theorem p_not_implies_missing :
    ¬ ∀ x, signal N.forest C.p.val x ≤ signal N.forest C.missing.val x := by
  intro implies
  have on := (Bool.le_iff_imp.mp (implies (singletonInput C.a))) C.onP
  rw [C.offMissing] at on
  contradiction

theorem q_not_implies_missing :
    ¬ ∀ x, signal N.forest C.q.val x ≤ signal N.forest C.missing.val x := by
  intro implies
  have on := (Bool.le_iff_imp.mp (implies (singletonInput C.a))) C.onQ
  rw [C.offMissing] at on
  contradiction

theorem missing_not_implies_both :
    ¬ ((∀ x, signal N.forest C.missing.val x ≤ signal N.forest C.p.val x) ∧
       (∀ x, signal N.forest C.missing.val x ≤ signal N.forest C.q.val x)) := by
  rintro ⟨toP, toQ⟩
  obtain ⟨i, on⟩ := C.stage_active C.missing.castSucc
  change signal N.forest C.missing.val (singletonInput i) = true at on
  have ne : i ≠ C.a := by
    intro eq
    rw [eq, C.offMissing] at on
    contradiction
  exact C.noBoth i ne
    ⟨(Bool.le_iff_imp.mp (toP _)) on, (Bool.le_iff_imp.mp (toQ _)) on⟩

end Case

end CrownFourthStructure
