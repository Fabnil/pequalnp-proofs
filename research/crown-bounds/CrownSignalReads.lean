import CrownFourNetwork

namespace CrownFourNetwork.Network

open CrownForks CrownOrStages CrownOrReaders CrownFirstAnd CrownPairFormula PnpResearch
open CrownProfileThree.Network (flag ones rawKey)

variable {I : Type}

def flagKey (s : Fin 3) : Option (Option (Option I)) :=
  match s.val with
  | 0 => some (some none)
  | 1 => some none
  | _ => none

theorem givenFlag (N : Network I) (x : I → Bool) (s : Fin 3) :
    CrownProfileThree.Network.supply (N.stages.bits x) x (flagKey s) = signal N.forest s.val x := by
  fin_cases s <;> rfl

variable [DecidableEq I]

def readsFlag (N : Network I) (s : Fin 3) (t : Fin 4) : ℕ :=
  reads (N.stages.formulaAt t) (flagKey s)

def link (N : Network I) (s t : Fin 3) : Prop := 0 < N.readsFlag s t.castSucc

private theorem rename_avoids {A B : Type} [DecidableEq B] (f : Formula A) (map : A → B) (b : B)
    (absent : ∀ a, map a ≠ b) : reads (rename f map) b = 0 := by
  unfold reads
  rw [weight_rename]
  have eq : ((fun a => (singletonInput b a).toNat) ∘ map) = fun _ => 0 := by
    funext a
    simp [singletonInput, absent a]
  rw [eq]
  simpa [CrownForest.stock] using CrownForest.stock_zero [f]

theorem readsFlag_forward (N : Network I) (s : Fin 3) (t : Fin 4)
    (used : 0 < N.readsFlag s t) : s.val < t.val := by
  by_contra! reverse
  have no : N.readsFlag s t = 0 := by
    fin_cases s <;> fin_cases t
    all_goals
      first
      | (exfalso; revert reverse; decide)
      | (unfold readsFlag; apply rename_avoids; intro a; simp [flagKey, rawKey])
  omega

theorem or_flag_implies (N : Network I) (s : Fin 3) (t : Fin 4)
    (pure : orPrefix N.forest (t.val + 1)) (used : 0 < N.readsFlag s t) (x : I → Bool) :
    signal N.forest s.val x ≤ signal N.forest t.val x := by
  apply Bool.le_iff_imp.mpr
  intro earlier
  rw [← N.stage_eval]
  apply (orOnly_on_iff _ (N.formulaAt_pure t pure) _).mpr
  exact ⟨flagKey s, used, (N.givenFlag x s).trans earlier⟩

theorem or_stage_reason (N : Network I) (t : Fin 4) (pure : orPrefix N.forest (t.val + 1)) (i : I)
    (on : signal N.forest t.val (singletonInput i) = true) :
    0 < N.stages.rawAt t i ∨
      ∃ s : Fin 3, 0 < N.readsFlag s t ∧ signal N.forest s.val (singletonInput i) = true := by
  rw [← N.stage_eval] at on
  obtain ⟨key, used, on⟩ := (orOnly_on_iff _ (N.formulaAt_pure t pure) _).mp on
  rcases key with _ | _ | _ | j
  · exact Or.inr ⟨2, used, on⟩
  · exact Or.inr ⟨1, used, on⟩
  · exact Or.inr ⟨0, used, on⟩
  · have eq : j = i := by
      simpa [CrownProfileThree.Network.supply, singletonInput] using on
    subst j
    exact Or.inl used

end CrownFourNetwork.Network
