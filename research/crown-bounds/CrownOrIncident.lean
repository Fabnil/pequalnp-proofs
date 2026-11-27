import CrownOrSupport

namespace CrownOrSupport.Case

open CrownForks CrownFourNetwork CrownFourNormal CrownPairFormula CrownFourGroups
open CrownAllOrModel PnpResearch Finset
open scoped Classical

variable {N : Network Ten} (C : Case N)

include C in
/-- The incident-pair obstruction holds with any flag as its center. -/
theorem incident_at (a : Ten) (k : Flag) (single : support N a = {k})
    (edges : ∀ l : Flag, l ≠ k →
      ∃ i : Ten, support N i = {k, l} ∧ reads (output N) (.inr i) = 0)
    (raw : reads (output N) (.inr a) ≤ 1) : False := by
  let e : Flag ≃ Flag := Equiv.swap none k
  have center : e none = k := Equiv.swap_apply_left _ _
  have twice (b : Flag) : e (e b) = b := Equiv.swap_apply_self _ _ _
  let tag : Flag ⊕ Ten → Flag ⊕ Ten := Sum.elim (fun b => .inl (e b)) Sum.inr
  have injective : Function.Injective tag := by
    intro x y h
    cases x <;> cases y <;> simp [tag] at h ⊢ <;> assumption
  let f := rename (output N) tag
  have read (z : Flag ⊕ Ten) : reads f (tag z) = reads (output N) z := by
    simp only [f, reads, weight_rename]
    congr 1
    funext x
    simp [singletonInput, injective.eq_iff]
  have sameRead (i : Ten) : reads f (.inr i) = reads (output N) (.inr i) := read (.inr i)
  let p (i : Ten) (b : Flag) := flagValues N (singletonInput i) (e b)
  have evaluate (b : Flag → Bool) (x : Ten → Bool) :
      f.evalWith (assignment (fun u => b (e u)) x) = (output N).evalWith (assignment b x) := by
    change (rename (output N) tag).evalWith _ = _
    rw [eval_rename]
    congr 1
    funext y
    cases y with
    | inl u => exact congrArg b (twice u)
    | inr i => rfl
  have test : IndependentTests f p :=
    ⟨fun i => (evaluate _ _).trans (C.tests.1 i),
      fun i j ne => (evaluate (fun b => flagValues N (singletonInput i) b ||
        flagValues N (singletonInput j) b) _).trans (C.tests.2 i j ne)⟩
  have edgeExists (j : Fin 3) :=
    edges (e (some j)) (fun eq => Option.some_ne_none j (e.injective (eq.trans center.symm)))
  choose edge edge_read using edgeExists
  have singleBool : p a = withHead true (fun _ => false) := by
    funext b
    apply Bool.eq_iff_iff.mpr
    change flagValues N (singletonInput a) (e b) = true ↔ withHead true (fun _ => false) b = true
    rw [← mem_support, single, mem_singleton, ← center, e.injective.eq_iff]
    cases b <;> simp
  have doubleBool (j : Fin 3) : p (edge j) = withHead true (singletonInput j) := by
    funext b
    apply Bool.eq_iff_iff.mpr
    change flagValues N (singletonInput (edge j)) (e b) = true ↔
      withHead true (singletonInput j) b = true
    rw [← mem_support, (edge_read j).1, mem_insert, mem_singleton, ← center]
    simp only [e.injective.eq_iff]
    cases b <;> simp [singletonInput]
  have flagCount (j : Fin 3) : reads f (.inl (some j)) ≤ 2 := by
    have eq := read (.inl (e (some j)))
    change reads f (.inl (e (e (some j)))) = _ at eq
    rw [twice] at eq
    rw [eq]
    exact output_flag_cap N C.valid _
  exact incidentDoubleProfilesImpossible f p test a edge singleBool doubleBool
    (fun j => (sameRead _).trans (edge_read j).2) ((sameRead a).trans_le raw) flagCount

end CrownOrSupport.Case
