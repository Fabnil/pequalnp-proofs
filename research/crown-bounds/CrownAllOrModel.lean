import CrownSignalReads
import CrownFourGroups

namespace CrownAllOrModel

open CrownForks CrownForest CrownVisibility CrownFirstAnd CrownFourNetwork CrownFourNormal
open CrownOrStages CrownOrReaders CrownPairFormula CrownFourGroups PnpResearch Finset
open CrownProfileThree.Network (ones)

abbrev Flag := Option (Fin 3)

def stage (k : Flag) : Fin 4 := withHead 3 Fin.castSucc k

def flagValues {I : Type} (N : Network I) (x : I → Bool) (k : Flag) : Bool :=
  signal N.forest (stage k).val x

/-- Name the four computed values and original inputs in the output formula. -/
def outputKey {I : Type} : Option (Option (Option (Option I))) → Flag ⊕ I
  | none => .inl none
  | some none => .inl (some 2)
  | some (some none) => .inl (some 1)
  | some (some (some none)) => .inl (some 0)
  | some (some (some (some i))) => .inr i

def output {I : Type} (N : Network I) : Formula (Flag ⊕ I) :=
  rename N.out outputKey

theorem output_eval {I : Type} (N : Network I) (x : I → Bool) :
    (output N).evalWith (assignment (flagValues N x) x) = N.forest.eval x := by
  rw [output, eval_rename]
  change N.out.evalWith _ = N.out.evalWith (withHead (N.last x) (N.stages.signals x))
  congr 1
  funext k
  rcases k with _ | _ | _ | _ | i <;> rfl

theorem output_raw_read {I : Type} [DecidableEq I] (N : Network I) (i : I) :
    reads (output N) (.inr i) = outputWeight N.forest (ones i) := by
  rw [output, reads, weight_rename]
  change leafWeight N.out _ = leafWeight N.out _
  congr 1
  funext k
  rcases k with _ | _ | _ | _ | j <;> simp [outputKey, singletonInput, ones]

theorem flags_on_pair {I : Type} [DecidableEq I] (N : Network I) (pure : orPrefix N.forest 4)
    (i j : I) :
    flagValues N (pairInput i j) = fun k =>
      flagValues N (singletonInput i) k || flagValues N (singletonInput j) k := by
  funext k
  exact orStage_pair N.forest 4 pure (stage k).val (stage k).isLt i j

theorem passes_tests {I : Type} [DecidableEq I] (N : Network I) (pure : orPrefix N.forest 4)
    (test : ThresholdOn N.forest.eval) :
    IndependentTests (output N) (fun i => flagValues N (singletonInput i)) := by
  exact ⟨fun i => (output_eval N _).trans (test.1 i),
    fun i j ne => by rw [← flags_on_pair N pure, output_eval]; exact test.2 i j ne⟩

theorem flag_iff_direct {I : Type} [DecidableEq I] (N : Network I) (pure : orPrefix N.forest 4)
    (independent : ∀ s t, N.readsFlag s t = 0) (k : Flag) (i : I) :
    flagValues N (singletonInput i) k = true ↔ 0 < N.stages.rawAt (stage k) i := by
  have proof : orPrefix N.forest ((stage k).val + 1) :=
    orPrefix_mono N.forest (Nat.succ_le_of_lt (stage k).isLt) pure
  constructor
  · intro on
    rcases N.or_stage_reason (stage k) proof i on with yes | ⟨s, used, _⟩
    · exact yes
    · rw [independent] at used
      omega
  · exact N.direct_or_on (stage k) i proof

private theorem count_named {A B : Type} [DecidableEq B] (f : Formula A) (map : A → B) (b : B)
    (w : A → ℕ) (eq : ∀ a, (singletonInput b (map a)).toNat = w a) :
    reads (rename f map) b = leafWeight f w := by
  rw [reads, weight_rename]
  congr 1
  exact funext eq

variable {I : Type} [DecidableEq I]

theorem output_reads_last (N : Network I) (valid : N.forest.Valid) : reads (output N) (.inl none) = 2 := by
  unfold output
  rw [count_named _ _ _ (withHead 1 (fun _ => 0)) (by intro a; rcases a with _ | _ | _ | _ | a <;> rfl)]
  exact valid.2.1.2.1.2.1.2.2

/-- The two reads of each earlier OR signal are accounted for between the
    remaining common formulas and the output. -/
theorem earlier_read_budget (N : Network I) (valid : N.forest.Valid) (s : Fin 3) :
    reads (output N) (.inl (some s)) + (∑ t : Fin 4, N.readsFlag s t) = 2 := by
  have absent (s : Fin 3) (t : Fin 4) (order : t.val ≤ s.val) : N.readsFlag s t = 0 := by
    by_contra! no
    have pos : 0 < N.readsFlag s t := by omega
    have early := N.readsFlag_forward s t pos
    omega
  rw [Fin.sum_univ_four]
  fin_cases s
  · let w₁ : Option I → ℕ := withHead 1 (fun _ => 0)
    let w₂ := withHead 0 w₁
    let w₃ := withHead 0 w₂
    let w₄ := withHead 0 w₃
    have q : N.readsFlag 0 1 = leafWeight N.stages.second w₁ :=
      count_named _ (fun a => some (some a)) (Network.flagKey 0) _ (by intro a; cases a <;> rfl)
    have r : N.readsFlag 0 2 = leafWeight N.stages.third w₂ :=
      count_named _ some (Network.flagKey 0) _ (by intro a; rcases a with _ | _ | a <;> rfl)
    have d : N.readsFlag 0 3 = leafWeight N.stages.output w₃ := by
      change leafWeight N.stages.output _ = _
      congr 1
      funext a
      rcases a with _ | _ | _ | a <;> rfl
    have out : reads (output N) (.inl (some 0)) = leafWeight N.out w₄ :=
      count_named _ outputKey _ _ (by intro a; rcases a with _ | _ | _ | _ | a <;> rfl)
    have cost : leafWeight N.stages.second w₁ + (leafWeight N.stages.third w₂ +
        (leafWeight N.stages.output w₃ + leafWeight N.out w₄)) = 2 := valid.2.2
    change reads (output N) (.inl (some 0)) +
      (N.readsFlag 0 0 + N.readsFlag 0 1 + N.readsFlag 0 2 + N.readsFlag 0 3) = 2
    rw [out, absent 0 0 (by decide), q, r, d]
    omega
  · let w₂ : Option (Option I) → ℕ := withHead 1 (fun _ => 0)
    let w₃ := withHead 0 w₂
    let w₄ := withHead 0 w₃
    have r : N.readsFlag 1 2 = leafWeight N.stages.third w₂ :=
      count_named _ some (Network.flagKey 1) _ (by intro a; rcases a with _ | _ | a <;> rfl)
    have d : N.readsFlag 1 3 = leafWeight N.stages.output w₃ := by
      change leafWeight N.stages.output _ = _
      congr 1
      funext a
      rcases a with _ | _ | _ | a <;> rfl
    have out : reads (output N) (.inl (some 1)) = leafWeight N.out w₄ :=
      count_named _ outputKey _ _ (by intro a; rcases a with _ | _ | _ | _ | a <;> rfl)
    have cost : leafWeight N.stages.third w₂ + (leafWeight N.stages.output w₃ + leafWeight N.out w₄) = 2 :=
      valid.2.1.2.2
    change reads (output N) (.inl (some 1)) +
      (N.readsFlag 1 0 + N.readsFlag 1 1 + N.readsFlag 1 2 + N.readsFlag 1 3) = 2
    rw [out, absent 1 0 (by decide), absent 1 1 (by decide), r, d]
    omega
  · let w₃ : Option (Option (Option I)) → ℕ := withHead 1 (fun _ => 0)
    let w₄ := withHead 0 w₃
    have d : N.readsFlag 2 3 = leafWeight N.stages.output w₃ := by
      change leafWeight N.stages.output _ = _
      congr 1
      funext a
      rcases a with _ | _ | _ | a <;> rfl
    have out : reads (output N) (.inl (some 2)) = leafWeight N.out w₄ :=
      count_named _ outputKey _ _ (by intro a; rcases a with _ | _ | _ | _ | a <;> rfl)
    have cost : leafWeight N.stages.output w₃ + leafWeight N.out w₄ = 2 := valid.2.1.2.1.2.2
    change reads (output N) (.inl (some 2)) +
      (N.readsFlag 2 0 + N.readsFlag 2 1 + N.readsFlag 2 2 + N.readsFlag 2 3) = 2
    rw [out, absent 2 0 (by decide), absent 2 1 (by decide), absent 2 2 (by decide), d]
    omega

theorem output_flag_cap (N : Network I) (valid : N.forest.Valid) (k : Flag) :
    reads (output N) (.inl k) ≤ 2 := by
  cases k with
  | none => exact (output_reads_last N valid).le
  | some s =>
    have used := earlier_read_budget N valid s
    omega

end CrownAllOrModel
