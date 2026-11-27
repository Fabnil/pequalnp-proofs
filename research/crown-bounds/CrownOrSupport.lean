import CrownAllOrModel
import CrownOrPacking

namespace CrownOrSupport

open CrownForks CrownForest CrownFourNetwork CrownFourNormal CrownOrStages
open CrownAllOrModel CrownOrPacking CrownPairFormula Finset
open CrownProfileThree.Network (ones)

variable {I : Type}

noncomputable def stageEquiv : Flag ≃ Fin 4 :=
  Equiv.ofBijective stage ⟨by decide +kernel, by decide +kernel⟩

theorem stage_sum (w : Fin 4 → ℕ) : ∑ k : Flag, w (stage k) = ∑ j : Fin 4, w j :=
  stageEquiv.sum_comp w

variable [DecidableEq I]

def readers (N : Network I) (i : I) : Finset Flag :=
  univ.filter fun k => 0 < N.stages.rawAt (stage k) i

@[simp] theorem mem_readers (N : Network I) (i : I) (k : Flag) :
    k ∈ readers N i ↔ 0 < N.stages.rawAt (stage k) i := by
  simp [readers]

theorem raw_budget (N : Network I) (i : I) :
    (readers N i).card + reads (output N) (.inr i) ≤ N.forest.weight (ones i) := by
  have stages : (readers N i).card ≤ ∑ k : Flag, N.stages.rawAt (stage k) i := by
    calc
      (readers N i).card = ∑ _k ∈ readers N i, (1 : ℕ) := by simp
      _ ≤ ∑ k ∈ readers N i, N.stages.rawAt (stage k) i :=
        sum_le_sum fun k used => (mem_readers N i k).mp used
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  rw [stage_sum (fun k => N.stages.rawAt k i)] at stages
  rw [output_raw_read, ← N.rawTotal]
  exact Nat.add_le_add_right stages _

def support (N : Network I) (i : I) : Finset Flag :=
  active (fun i => flagValues N (singletonInput i)) i

@[simp] theorem mem_support (N : Network I) (i : I) (k : Flag) :
    k ∈ support N i ↔ flagValues N (singletonInput i) k = true := by
  simp [support, active]

theorem support_eq_readers (N : Network I) (pure : orPrefix N.forest 4)
    (independent : ∀ s t, N.readsFlag s t = 0) (i : I) : support N i = readers N i := by
  ext k
  simp only [mem_support, mem_readers, flag_iff_direct N pure independent]

theorem bits_le_of_subset (N : Network I) {i j : I} (h : support N i ⊆ support N j) (k : Flag) :
    flagValues N (singletonInput i) k ≤ flagValues N (singletonInput j) k :=
  Bool.le_iff_imp.mpr fun on => (mem_support N j k).mp (h ((mem_support N i k).mpr on))

theorem bits_eq_of_support_eq (N : Network I) {i j : I} (h : support N i = support N j) :
    flagValues N (singletonInput i) = flagValues N (singletonInput j) := by
  funext k
  exact le_antisymm (bits_le_of_subset N h.subset k) (bits_le_of_subset N h.symm.subset k)

structure Case (N : Network Ten) : Prop where
  valid : N.forest.Valid
  test : ThresholdOn N.forest.eval
  raw : ∀ i, N.forest.weight (ones i) = 2
  pure : orPrefix N.forest 4

theorem of_orPrefix (hyp : CrownFirstOr.HasOrPrefix 4) : ∃ N : Network Ten, Case N := by
  obtain ⟨p, q, r, s, h, pure, valid, test, raw⟩ := hyp
  exact ⟨⟨⟨p, q, r, s⟩, h⟩, ⟨valid, test, raw, pure⟩⟩

namespace Case

variable {N : Network Ten} (C : Case N)

include C

theorem read_bound (i : Ten) : (readers N i).card + reads (output N) (.inr i) ≤ 2 :=
  (raw_budget N i).trans (C.raw i).le

theorem tests : CrownFourGroups.IndependentTests (output N)
    (fun i => flagValues N (singletonInput i)) := passes_tests N C.pure C.test

theorem hidden_no_superset {i j : Ten} (ne : i ≠ j) (hidden : reads (output N) (.inr i) = 0)
    (includeProfile : support N i ⊆ support N j) : False :=
  hiddenProfileCannotBeIncluded _ _ C.tests ne hidden (bits_le_of_subset N includeProfile)

theorem repeated_no_superset {i j a : Ten} (ij : i ≠ j) (ia : i ≠ a) (ja : j ≠ a)
    (same : support N i = support N j) (includeProfile : support N i ⊆ support N a)
    (ri : reads (output N) (.inr i) ≤ 1) (rj : reads (output N) (.inr j) ≤ 1) : False :=
  repeatedProfileCannotBeIncluded _ _ C.tests ij ia ja (bits_eq_of_support_eq N same)
    (bits_le_of_subset N includeProfile) ri rj

end Case

end CrownOrSupport
