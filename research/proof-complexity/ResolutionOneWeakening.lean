import PEqualNP.Outside.L_pcx_150

namespace ResolutionOneWeakening

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

/-- A resolution-over-parities derivation with its number of weakening steps. -/
inductive Counted (F : Set (LinClause V)) : ℕ → List (LinClause V) → Prop
  | nil : Counted F 0 []
  | ax {n π C} : Counted F n π → C ∈ F → Counted F n (C :: π)
  | res {n π C D R} : Counted F n π → C ∈ π → D ∈ π → IsLinResolvent C D R →
      Counted F n (R :: π)
  | weak {n π C D} : Counted F n π → C ∈ π →
      (∀ a, LinClauseSat a C → LinClauseSat a D) → Counted F (n + 1) (D :: π)

private def nonSingleton (C : LinClause V) : LinClause V :=
  C.filter fun e => e.1.card ≠ 1

omit [DecidableEq V] in
private theorem singleton_of_mem {C : LinClause V} (pure : nonSingleton C = ∅)
    {e : LinEq V} (mem : e ∈ C) : e.1.card = 1 := by
  by_contra shape
  have bad : e ∈ nonSingleton C := Finset.mem_filter.mpr ⟨mem, shape⟩
  simp [pure] at bad

omit [DecidableEq V] in
private theorem axis_sat (a : V → Bool) (v : V) (b : Bool) :
    LinEqSat a ({v}, b) ↔ a v = b := by
  cases h : a v <;> cases b <;> simp [LinEqSat, Finset.filter_singleton, h]

private def Tautology (C : LinClause V) : Prop := ∀ a, LinClauseSat a C

private def Covered (ρ : List (Clause V)) (C : LinClause V) : Prop :=
  Tautology C ∨ ∃ D ∈ ρ, linOfClause D ⊆ C

private theorem covered_mono {ρ σ : List (Clause V)} {C : LinClause V}
    (incl : ∀ D ∈ ρ, D ∈ σ) (cover : Covered ρ C) : Covered σ C := by
  rcases cover with taut | ⟨D, mem, sub⟩
  · exact Or.inl taut
  · exact Or.inr ⟨D, incl D mem, sub⟩

/-- Implication into a non-tautological clause of singleton equations gives inclusion. -/
private theorem axis_imp_subset {A : Clause V} {D : LinClause V}
    (pure : nonSingleton D = ∅) (notTaut : ¬ Tautology D)
    (imp : ∀ a, LinClauseSat a (linOfClause A) → LinClauseSat a D) : linOfClause A ⊆ D := by
  classical
  intro e mem
  obtain ⟨⟨v, b⟩, literal, rfl⟩ := Finset.mem_image.mp mem
  by_contra missing
  obtain ⟨a, no⟩ := not_forall.mp notTaut
  let a' := Function.update a v b
  have holds : LinClauseSat a' (linOfClause A) :=
    ⟨({v}, b), Finset.mem_image_of_mem _ literal, (axis_sat a' v b).mpr (by simp [a'])⟩
  obtain ⟨⟨support, rhs⟩, present, truth⟩ := imp a' holds
  have size : support.card = 1 := singleton_of_mem pure present
  obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp size
  have rhs_eq := (axis_sat a' w rhs).mp truth
  by_cases same : w = v
  · subst w
    have equal : b = rhs := by simpa [a'] using rhs_eq
    exact missing (equal.symm ▸ present)
  · exact no ⟨({w}, rhs), present, (axis_sat a w rhs).mpr (by simpa [a', same] using rhs_eq)⟩

private theorem coverImp {ρ : List (Clause V)} {C D : LinClause V}
    (old : Covered ρ C) (pure : nonSingleton D = ∅)
    (imp : ∀ a, LinClauseSat a C → LinClauseSat a D) : Covered ρ D := by
  classical
  by_cases taut : Tautology D
  · exact Or.inl taut
  · rcases old with old | ⟨A, mem, sub⟩
    · exact (taut (fun a => imp a (old a))).elim
    · refine Or.inr ⟨A, mem, axis_imp_subset pure taut ?_⟩
      rintro a ⟨q, hq, hv⟩
      exact imp a ⟨q, sub hq, hv⟩

private theorem resolvent_sat {C D R : LinClause V} (step : IsLinResolvent C D R)
    (a : V → Bool) (left : LinClauseSat a C) (right : LinClauseSat a D) : LinClauseSat a R := by
  obtain ⟨f, _, _, rfl⟩ := step
  by_cases odd : Odd (f.filter fun v => a v = true).card
  · obtain ⟨q, mem, sat⟩ := left
    have apart : q ≠ (f, false) := by
      rintro rfl
      exact Bool.false_ne_true (sat.mp odd)
    exact ⟨q, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨apart, mem⟩), sat⟩
  · obtain ⟨q, mem, sat⟩ := right
    have apart : q ≠ (f, true) := by
      rintro rfl
      exact odd (sat.mpr rfl)
    exact ⟨q, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨apart, mem⟩), sat⟩

/-- If all nonempty sets of nonsingleton equations agree, a resolution keeps
their union. When both parents remove one of these equations, each has the
complementary equation that the other parent retains. -/
private theorem nonsingleton_res {C D R S : LinClause V} (step : IsLinResolvent C D R)
    (left : nonSingleton C = ∅ ∨ nonSingleton C = S)
    (right : nonSingleton D = ∅ ∨ nonSingleton D = S) :
    nonSingleton R = nonSingleton C ∪ nonSingleton D := by
  obtain ⟨f, fm, fp, rfl⟩ := step
  ext q
  simp only [nonSingleton, Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩ | ⟨_, h⟩, nonsingle⟩
    · exact Or.inl ⟨h, nonsingle⟩
    · exact Or.inr ⟨h, nonsingle⟩
  · rintro (⟨mem, nonsingle⟩ | ⟨mem, nonsingle⟩)
    · refine ⟨?_, nonsingle⟩
      by_cases pivot : q = (f, false)
      · subst q
        have inC : (f, false) ∈ nonSingleton C := Finset.mem_filter.mpr ⟨mem, nonsingle⟩
        have inD : (f, true) ∈ nonSingleton D := Finset.mem_filter.mpr ⟨fp, nonsingle⟩
        have same := (left.resolve_left (Finset.ne_empty_of_mem inC)).trans
          (right.resolve_left (Finset.ne_empty_of_mem inD)).symm
        have stays := Finset.mem_filter.mp (same ▸ inC)
        exact Or.inr ⟨by simp, stays.1⟩
      · exact Or.inl ⟨pivot, mem⟩
    · refine ⟨?_, nonsingle⟩
      by_cases pivot : q = (f, true)
      · subst q
        have inC : (f, false) ∈ nonSingleton C := Finset.mem_filter.mpr ⟨fm, nonsingle⟩
        have inD : (f, true) ∈ nonSingleton D := Finset.mem_filter.mpr ⟨mem, nonsingle⟩
        have same := (right.resolve_left (Finset.ne_empty_of_mem inD)).trans
          (left.resolve_left (Finset.ne_empty_of_mem inC)).symm
        have stays := Finset.mem_filter.mp (same ▸ inD)
        exact Or.inl ⟨by simp, stays.1⟩
      · exact Or.inr ⟨pivot, mem⟩

private theorem image_erase (A : Clause V) (v : V) (b : Bool) :
    linOfClause (A.erase (v, b)) = (linOfClause A).erase ({v}, b) := by
  apply Finset.image_erase
  rintro ⟨v, b⟩ ⟨w, c⟩ h
  change (({v} : Finset V), b) = (({w} : Finset V), c) at h
  exact Prod.ext (Finset.singleton_inj.mp (congrArg Prod.fst h))
    (congrArg (fun e : LinEq V => e.2) h)

private theorem coverResolution {F : Set (Clause V)} {ρ : List (Clause V)} {C D R : LinClause V}
    (proof : IsDerivation F ρ) (step : IsLinResolvent C D R)
    (pureC : nonSingleton C = ∅) (pureR : nonSingleton R = ∅)
    (left : Covered ρ C) (right : Covered ρ D) :
    ∃ σ, IsDerivation F σ ∧ σ.length ≤ ρ.length + 1 ∧ (∀ A ∈ ρ, A ∈ σ) ∧ Covered σ R := by
  rcases left with taut | ⟨A, memA, subA⟩
  · refine ⟨ρ, proof, by omega, fun _ mem => mem, coverImp right pureR ?_⟩
    exact fun a sat => resolvent_sat step a (taut a) sat
  rcases right with taut | ⟨B, memB, subB⟩
  · refine ⟨ρ, proof, by omega, fun _ mem => mem, coverImp (Or.inr ⟨A, memA, subA⟩) pureR ?_⟩
    exact fun a sat => resolvent_sat step a sat (taut a)
  obtain ⟨form, fm, _, rfl⟩ := step
  have size : form.card = 1 := singleton_of_mem pureC fm
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp size
  have eraseA : linOfClause (A.erase (v, false)) ⊆ C.erase ({v}, false) := by
    rw [image_erase]
    intro e mem
    obtain ⟨apart, inside⟩ := Finset.mem_erase.mp mem
    exact Finset.mem_erase.mpr ⟨apart, subA inside⟩
  have eraseB : linOfClause (B.erase (v, true)) ⊆ D.erase ({v}, true) := by
    rw [image_erase]
    intro e mem
    obtain ⟨apart, inside⟩ := Finset.mem_erase.mp mem
    exact Finset.mem_erase.mpr ⟨apart, subB inside⟩
  by_cases na : (v, false) ∈ A
  · by_cases nb : (v, true) ∈ B
    · let T := (B.erase (v, true)) ∪ (A.erase (v, false))
      have resolvent : IsResolvent B A T := ⟨v, nb, na, rfl⟩
      refine ⟨T :: ρ, .res proof memB memA resolvent, by simp, fun _ mem => List.mem_cons_of_mem _ mem,
        Or.inr ⟨T, by simp, ?_⟩⟩
      simp only [T, linOfClause, Finset.image_union]
      exact Finset.union_subset
        (eraseB.trans Finset.subset_union_right) (eraseA.trans Finset.subset_union_left)
    · rw [Finset.erase_eq_of_notMem nb] at eraseB
      exact ⟨ρ, proof, by omega, fun _ mem => mem, Or.inr ⟨B, memB, eraseB.trans Finset.subset_union_right⟩⟩
  · rw [Finset.erase_eq_of_notMem na] at eraseA
    exact ⟨ρ, proof, by omega, fun _ mem => mem, Or.inr ⟨A, memA, eraseA.trans Finset.subset_union_left⟩⟩

private theorem slice {F : Set (Clause V)} {π : List (LinClause V)} {n : ℕ}
    (trace : Counted (linOfClause '' F) n π) (budget : n ≤ 1) :
    ∃ (ρ : List (Clause V)) (S : LinClause V),
      IsDerivation F ρ ∧ ρ.length + n ≤ π.length ∧ (n = 0 → S = ∅) ∧
      (∀ C ∈ π, nonSingleton C = ∅ ∨ nonSingleton C = S) ∧
      ∀ C ∈ π, nonSingleton C = ∅ → Covered ρ C := by
  induction trace with
  | nil => exact ⟨[], ∅, .nil, by simp, fun _ => rfl, by simp, by simp⟩
  | @ax n π C trace ax ih =>
    obtain ⟨ρ, S, proof, len, zero, shape, cover⟩ := ih budget
    obtain ⟨A, mem, rfl⟩ := ax
    have empty : nonSingleton (linOfClause A) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e mem
      obtain ⟨image, shape⟩ := Finset.mem_filter.mp mem
      obtain ⟨⟨v, b⟩, _, rfl⟩ := Finset.mem_image.mp image
      simp at shape
    refine ⟨A :: ρ, S, .ax proof mem, by simp; omega, zero, ?_, ?_⟩
    · intro C hC
      rcases List.mem_cons.mp hC with rfl | hC
      · exact Or.inl empty
      · exact shape C hC
    · intro C hC pure
      rcases List.mem_cons.mp hC with rfl | hC
      · exact Or.inr ⟨A, by simp, Finset.Subset.refl _⟩
      · exact covered_mono (fun _ h => List.mem_cons_of_mem _ h) (cover C hC pure)
  | @res n π C D R trace hC hD step ih =>
    obtain ⟨ρ, S, proof, len, zero, shape, cover⟩ := ih budget
    have pieces := nonsingleton_res step (shape C hC) (shape D hD)
    have shapeR : nonSingleton R = ∅ ∨ nonSingleton R = S := by
      rw [pieces]
      rcases shape C hC with hc | hc <;> rcases shape D hD with hd | hd <;> simp [hc, hd]
    have next : ∃ σ, IsDerivation F σ ∧ σ.length ≤ ρ.length + 1 ∧
        (∀ A ∈ ρ, A ∈ σ) ∧ (nonSingleton R = ∅ → Covered σ R) := by
      by_cases pure : nonSingleton R = ∅
      · have parts := Finset.union_eq_empty.mp (pieces.symm.trans pure)
        obtain ⟨σ, valid, length, inclusion, good⟩ := coverResolution proof step parts.1 pure
          (cover C hC parts.1) (cover D hD parts.2)
        exact ⟨σ, valid, length, inclusion, fun _ => good⟩
      · exact ⟨ρ, proof, by omega, fun _ mem => mem, fun h => (pure h).elim⟩
    obtain ⟨σ, valid, length, inclusion, good⟩ := next
    refine ⟨σ, S, valid, by simp; omega, zero, ?_, ?_⟩
    · intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact shapeR
      · exact shape A hA
    · intro A hA pure
      rcases List.mem_cons.mp hA with rfl | hA
      · exact good pure
      · exact covered_mono inclusion (cover A hA pure)
  | @weak n π C D trace mem imp ih =>
    have z : n = 0 := by omega
    obtain ⟨ρ, S, proof, len, zero, shape, cover⟩ := ih (by omega)
    have oldPure (A) (mem : A ∈ π) : nonSingleton A = ∅ :=
      (shape A mem).elim id (fun h => h.trans (zero z))
    refine ⟨ρ, nonSingleton D, proof, by simp; omega, by omega, ?_, ?_⟩
    · intro A hA
      rcases List.mem_cons.mp hA with rfl | hA
      · exact Or.inr rfl
      · exact Or.inl (oldPure A hA)
    · intro A hA pure
      rcases List.mem_cons.mp hA with rfl | hA
      · exact coverImp (cover C mem (oldPure C mem)) pure imp
      · exact cover A hA pure

/-- One weakening cannot shorten an ordinary resolution refutation. The ordinary
proof uses no more than the original number of lines minus the weakening count. -/
theorem ordinaryRefutation {F : Set (Clause V)} {π : List (LinClause V)} {n : ℕ}
    (trace : Counted (linOfClause '' F) n π) (budget : n ≤ 1) (closed : ∅ ∈ π) :
    ∃ ρ : List (Clause V), IsRefutation F ρ ∧ ρ.length + n ≤ π.length := by
  obtain ⟨ρ, _, proof, len, _, _, cover⟩ := slice trace budget
  rcases cover ∅ closed (by simp [nonSingleton]) with taut | ⟨A, mem, sub⟩
  · have impossible := taut (fun _ => false)
    simp [LinClauseSat] at impossible
  · have empty : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro literal occurs
      have present := sub (Finset.mem_image_of_mem _ occurs)
      simp at present
    exact ⟨ρ, ⟨proof, empty ▸ mem⟩, len⟩

/-- The accepted 52-line ordinary lower bound transfers to refutations with
at most one weakening, with the weakening charged as one line. -/
theorem php43Lower {π : List (LinClause (Fin 4 × Fin 3))} {n : ℕ}
    (trace : Counted (linOfClause '' PHP 4 3) n π) (budget : n ≤ 1) (closed : ∅ ∈ π) :
    52 + n ≤ π.length := by
  obtain ⟨ρ, refutes, length⟩ := ordinaryRefutation trace budget closed
  by_contra! small
  exact PEqualNP.Outside.L_pcx_150 ⟨ρ, refutes, by omega⟩

end ResolutionOneWeakening
