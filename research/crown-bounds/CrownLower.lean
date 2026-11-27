import CrownForest
import CrownSingle

/-!
Exact bounds for the threshold-two function through seven inputs,
and their consequences for crown graphs in the Desk model.
-/

namespace CrownLower

open CrownRun CrownForks CrownErase CrownSingle
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def Computes (n s : ℕ) (F : BF n) : Prop :=
  UC gF MonoA s (fun f => ∃ i : Fin n, f = var i) F

def LowerBound (n bound : ℕ) : Prop :=
  ∀ {s : ℕ} {F : BF n}, ThresholdOn F → Computes n s F → bound ≤ s

theorem topOnSingleton {n : ℕ} {p j : Fin (n + 1)} (ne : j ≠ p) :
    otop p (singletonInput j) = true := by
  simp only [otop, decide_eq_true_eq]
  exact ⟨j, ne, by simp [singletonInput]⟩

theorem topIsNotAnInput {n : ℕ} (size : 2 ≤ n) (p j : Fin (n + 1)) :
    otop p ≠ var j := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have ab : a ≠ b := by
    intro eq
    cases congrArg Fin.val eq
  obtain ⟨k, kp, kj⟩ : ∃ k : Fin (n + 1), k ≠ p ∧ k ≠ j := by
    by_cases same : p.succAbove a = j
    · refine ⟨p.succAbove b, Fin.succAbove_ne p b, ?_⟩
      intro e
      exact ab (Fin.succAbove_right_injective (same.trans e.symm))
    · exact ⟨p.succAbove a, Fin.succAbove_ne p a, same⟩
  intro eq
  have mismatch := topOnSingleton kp
  rw [eq] at mismatch
  simp [var, singletonInput, kj.symm] at mismatch

theorem omitTop {n s : ℕ} (size : 2 ≤ n) (p : Fin (n + 1)) {F : BF (n + 1)}
    (test : ThresholdOn F)
    (compute : UC gF MonoA s (fun f => f = otop p ∨
      ∃ j : Fin (n + 1), j ≠ p ∧ f = var j) (rst p F)) :
    Computes n s (fun x => F (liftBits p x)) := by
  have dominate : ∀ f, (∃ j : Fin (n + 1), j ≠ p ∧ f = var j) →
      ∀ x, f x = true → otop p x = true := by
    rintro f ⟨j, ne, rfl⟩ x yes
    simp only [otop, decide_eq_true_eq]
    exact ⟨j, ne, yes⟩
  have different : rst p F ≠ otop p := by
    intro same
    let j : Fin n := ⟨0, by omega⟩
    have no := (liftThreshold test p).1 j
    change F (liftBits p (singletonInput j)) = false at no
    have yes : otop p (liftBits p (singletonInput j)) = true := by
      rw [liftBits_single]
      exact topOnSingleton (Fin.succAbove_ne p j)
    have bad := congrFun same (liftBits p (singletonInput j))
    simp [rst, liftBits_fixed, no, yes] at bad
  have eliminated := top_elim (otop p) s _ _ dominate different compute
  have projected := projectUC p eliminated
  have agree : (fun x => rst p F (liftBits p x)) = fun x => F (liftBits p x) := by
    funext x
    simp [rst, liftBits_fixed]
  rw [agree] at projected
  exact projected

theorem noSmallRun {n lower budget : ℕ} (size : 2 ≤ n)
    (floor : LowerBound n lower) (limit : budget ≤ lower + 2)
    (twice : ∀ {s : ℕ} {F : BF (n + 1)} {idx : List (Fin (n + 1))},
      MR [F] s (idx.map var) → ThresholdOn F → s ≤ budget →
      (∀ i, idx.count i = 2) → False) :
    ∀ s (y : BF (n + 1)) (ys : List (BF (n + 1))) (idx : List (Fin (n + 1))),
      MR (y :: ys) s (idx.map var) → ThresholdOn (outF (y :: ys)) →
      s + ys.length ≤ budget → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y ys idx run test cost
    have single := complete_run y ys run
    by_cases all : ∀ i, idx.count i = 2
    · exact twice single test cost all
    obtain ⟨p, different⟩ := not_forall.mp all
    have more := everyInputUsed (by omega) single test p
    have less := atMostTwice size single test floor (by omega) p
    have once : idx.count p = 1 := by omega
    have present : p ∈ idx := List.count_pos_iff.mp (by omega)
    have absent : p ∉ idx.erase p := by
      intro hm
      have positive := List.count_pos_iff.mpr hm
      rw [List.count_erase_self, once] at positive
      omega
    let rest := (idx.erase p).map var
    have perm : (idx.map var).Perm (var p :: rest) :=
      (List.perm_cons_erase present).map var
    have independent : ∀ w ∈ rest, InvX p w := by
      intro w wm
      obtain ⟨j, used, rfl⟩ := List.mem_map.mp wm
      exact InvX_var (fun same => absent (same ▸ used))
    have step := SU size p y ys test s rest (TR.perm perm run) independent
    unfold SUc at step
    rcases step with ⟨needed, remove⟩ | ⟨u, y', ys', s', time, terms, valid, moved⟩
    · have noTop : otop p ∉ rest := by
        intro hm
        obtain ⟨j, _, eq⟩ := List.mem_map.mp hm
        exact topIsNotAnInput size p j eq.symm
      simp [noTop] at needed remove
      have compute := remove (fun f => f = otop p ∨
        ∃ j : Fin (n + 1), j ≠ p ∧ f = var j) (by
          intro w wm
          obtain ⟨j, used, rfl⟩ := List.mem_map.mp wm
          exact Or.inr ⟨j, fun same => absent (same ▸ used), rfl⟩) (Or.inl rfl)
      have bound := floor (liftThreshold test p) (omitTop size p test compute)
      omega
    · let next := List.replicate (u + 1) p ++ idx.erase p
      have nextRun : MR (y' :: ys') s' (next.map var) := by
        simpa only [next, List.map_append, List.map_replicate] using moved
      exact ih s' (by omega) y' ys' next nextRun valid (by omega)

theorem thresholdNonzero {n : ℕ} {F : BF n} (size : 2 ≤ n) (test : ThresholdOn F) :
    F ≠ zF := by
  intro eq
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have ne : i ≠ j := by
    intro h
    cases congrArg Fin.val h
  have yes := test.2 i j ne
  simp [eq, zF] at yes

theorem cannotCompute {n lower budget s : ℕ} {F : BF (n + 1)} (size : 2 ≤ n)
    (floor : LowerBound n lower) (limit : budget ≤ lower + 2)
    (twice : ∀ {t : ℕ} {G : BF (n + 1)} {idx : List (Fin (n + 1))},
      MR [G] t (idx.map var) → ThresholdOn G → t ≤ budget →
      (∀ i, idx.count i = 2) → False)
    (test : ThresholdOn F) (compute : Computes (n + 1) s F) (cost : s ≤ budget) :
    False := by
  classical
  obtain ⟨t, steps, ws, available, run⟩ :=
    normalize gF zF MonoA (fun _ => True) (fun _ _ _ _ _ => trivial)
      gF_zero_left gF_zero_right gF_self s _ F (fun _ _ => trivial)
      (thresholdNonzero (by omega) test) compute
  obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => (available w hw).1
  apply noSmallRun size floor limit twice t F [] idx (TR.monoC (fun _ _ _ h => h.1) run)
  · have same : outF [F] = F := funext fun x => by simp [outF]
    rwa [same]
  · simpa using steps.trans cost

theorem lowerUpToSeven (n : ℕ) (lo : 2 ≤ n) (hi : n ≤ 7) :
    LowerBound n (3 * n - 5) := by
  induction n with
  | zero => omega
  | succ n ih =>
    intro s F test compute
    by_cases base : n = 1
    · subst n
      simpa using thresholdRequiresGate test compute
    have size : 2 ≤ n := by omega
    have floor : LowerBound n (3 * n - 5) := ih size (by omega)
    by_contra! tooSmall
    have budget : s ≤ 3 * (n + 1) - 6 := by omega
    refine cannotCompute size floor (budget := 3 * (n + 1) - 6) (by omega) ?_ test compute budget
    intro t G idx run passes cost counts
    exact CrownForest.noReadTwiceBefore run passes hi (by omega) counts

theorem lowerAtEight : LowerBound 8 18 := by
  intro s F test compute
  by_contra! tooSmall
  have floor : LowerBound 7 16 := lowerUpToSeven 7 (by decide) (by decide)
  refine cannotCompute (n := 7) (budget := 17) (by decide) floor (by decide) ?_ test compute (by omega)
  intro t G idx run passes cost counts
  let p : Fin 8 := 0
  have part := eraseProjection run p (restrictionNonzero (by decide) passes p)
  have bound := floor (liftThreshold passes p) part
  rw [counts p] at bound
  omega

theorem ucOfRun {n s : ℕ} {F : BF n} {ws : List (BF n)} (run : MR [F] s ws) :
    ∀ inputs : BF n → Prop, (∀ f ∈ ws, inputs f) → UC gF MonoA s inputs F := by
  refine TR.ind (P := fun t w => ∀ inputs : BF n → Prop,
    (∀ f ∈ w, inputs f) → UC gF MonoA t inputs F) run ?_ ?_ ?_
  · intro inputs all
    exact all F (by simp)
  · intro _ xs ys perm _ ih inputs all
    exact ih inputs fun f hf => all f (perm.mem_iff.mp hf)
  · intro t a b rest k u op _ ih inputs all
    exact UC_gate k a b op (all a (by simp)) (all b (by simp)) (ih _ (by
      intro w wm
      rcases List.mem_append.mp wm with new | old
      · exact Or.inl (List.eq_of_mem_replicate new)
      · exact Or.inr (all w (by simp [old]))))

theorem circuitBound {n lower : ℕ} (size : 2 ≤ n) (floor : LowerBound n lower)
    {C : Circuit} (mono : Monotone2 C) {F : BF n} (test : ThresholdOn F)
    (acts : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x) : lower ≤ C.size := by
  obtain ⟨s, LE, idx, run⟩ :=
    CrownRun.fromCircuit mono F acts (thresholdNonzero size test)
      (fun eq => by have no := test.1 ⟨0, by omega⟩; simp [eq, oneF] at no)
  apply le_trans (floor test (ucOfRun run _ ?_)) LE
  intro w wm
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp wm
  exact ⟨i, rfl⟩

theorem thresholdTwoTests (n : ℕ) : ThresholdOn (CrownThreshold.thresholdTwo (n := n)) := by
  constructor
  · intro i
    have same : singletonInput i = CrownThreshold.pairInput i i := by
      funext k
      simp [singletonInput, CrownThreshold.pairInput]
    rw [same, CrownThreshold.thresholdTwo, CrownThreshold.pairCount]
    simp
  · intro i j ne
    have same : pairInput i j = CrownThreshold.pairInput i j := by
      funext k
      by_cases hi : k = i <;> by_cases hj : k = j <;>
        simp [pairInput, singletonInput, CrownThreshold.pairInput, hi, hj]
    rw [same, CrownThreshold.thresholdTwo, CrownThreshold.pairCount]
    simp [ne]

theorem noCrown22 :
    ¬ RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 22 := by
  intro assumed
  obtain ⟨C, mono, size, computes⟩ := CrownThreshold.crownSevenTwentyTwo.mp assumed
  have floor : LowerBound 7 16 := lowerUpToSeven 7 (by decide) (by decide)
  have lower := circuitBound (by decide : 2 ≤ 7) floor mono (thresholdTwoTests 7) computes
  omega

theorem noCrown25 :
    ¬ RepSizeAtMost (fun u v : Fin 8 => decide (u ≠ v)) 25 := by
  intro assumed
  obtain ⟨C, mono, size, computes⟩ :=
    (CrownThreshold.crownIffThreshold (n := 8) (budget := 17) (by decide)).mp assumed
  have lower := circuitBound (by decide : 2 ≤ 8) lowerAtEight mono (thresholdTwoTests 8) computes
  omega

def sevenWitness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 1]⟩,
    ⟨.and, [7, 2]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [7, 2]⟩,
    ⟨.and, [11, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 3]⟩,
    ⟨.and, [14, 4]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [14, 4]⟩,
    ⟨.and, [17, 5]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 5]⟩,
    ⟨.and, [20, 6]⟩, ⟨.or, [19, 21]⟩], 22⟩

set_option maxRecDepth 4096 in
theorem sevenWitnessCorrect :
    ∀ x : Fin 7 → Bool, sevenWitness.eval (List.ofFn x) = CrownThreshold.thresholdTwo x := by
  decide +kernel

theorem crownSevenMinimum :
    RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) 23 ∧
      ∀ s, RepSizeAtMost (fun u v : Fin 7 => decide (u ≠ v)) s → 23 ≤ s := by
  constructor
  · apply (CrownThreshold.crownIffThreshold (n := 7) (budget := 16) (by decide)).mpr
    exact ⟨sevenWitness, by simp [Monotone2, sevenWitness], by decide, sevenWitnessCorrect⟩
  · intro s witness
    by_contra! tooSmall
    obtain ⟨C, mono, sz, rep⟩ := witness
    exact noCrown22 ⟨C, mono, by omega, rep⟩

end CrownLower
