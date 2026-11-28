import PEqualNP.Defs
import PEqualNP.Outside.L_meta_17589
import PEqualNP.Outside.L_meta_18556

namespace PEqualNP.Outside.FanoMaskRefutation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def columns : List ℕ :=
  [189297016294346753, 155696362464247818, 218994303132237904,
   183565875465421444, 229736628136977440, 270286071508582656,
   288160007408715776, 95229015649943559, 55389823206162488,
   14003410187583936, 8521481457152, 4292497062785024,
   256463044608, 63038589501440]

private def negative : List ℕ :=
  [16256, 5889, 11778, 1539, 7300, 5125, 3078, 14600, 4361, 10250,
   6156, 12944, 4625, 8722, 4244, 12312, 4125, 9632, 1313, 9250, 1188,
   1063, 8488, 8368, 8250, 3008, 833, 2626, 2244, 2376, 2126, 720,
   595, 480, 361, 244, 127]

private def test (j : Fin 58) (i : Fin 14) : Bool :=
  (columns.getD i.val 0).testBit j.val

private def incidence (p l : Fin 7) : Prop :=
  p = l ∨ p = l + 1 ∨ p = l + 3

private instance (p l : Fin 7) : Decidable (incidence p l) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

set_option maxHeartbeats 6000000 in
private theorem pairIndex : ∀ p l : Fin 7, incidence p l →
    ∃ j : Fin 21, ∀ i : Fin 14,
      test (Fin.castAdd 37 j) i = decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) := by
  decide +kernel

set_option maxHeartbeats 6000000 in
private theorem maskIndex : ∀ k : Fin negative.length,
    ∃ j : Fin 37, ∀ i : Fin 14,
      test (Fin.natAdd 21 j) i = (negative.get k).testBit i.val := by
  decide +kernel

private def wordStep (w : List ℕ) (g : Gate) : List ℕ :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  w ++ [if g.op.eval [false, true] = true then a ||| b else a &&& b]

private def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]

private theorem readAppend (w : List α) (a d : α) (k : ℕ) :
    (w ++ [a]).getD k d = if k = w.length then a else w.getD k d := by
  by_cases h : k < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ne_of_lt h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    by_cases e : k = w.length
    · simp [e]
    · have nz : k - w.length ≠ 0 := by omega
      cases diff : k - w.length with
      | zero => exact (nz diff).elim
      | succ t =>
        have hz : w.getD k d = d := List.getD_eq_default _ _ (by omega)
        simpa [e, List.getD_eq_getElem?_getD] using hz.symm

private theorem readOfFn (f : Fin n → α) (i : ℕ) (d : α) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

private theorem getD_bits (w : List ℕ) (j k : ℕ) :
    (w.getD k 0).testBit j = (w.map (·.testBit j)).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[k]? <;> simp

private theorem gateForm (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    (h2 : g.inputs.length = 2) :
    ∃ a b o, g.inputs = [a, b] ∧ g.op = (if o = true then .or else .and) := by
  obtain ⟨op, inputs⟩ := g
  cases inputs with
  | nil => simp at h2
  | cons a inputs =>
    cases inputs with
    | nil => simp at h2
    | cons b rest =>
      have hr : rest = [] := by simpa using h2
      subst rest
      rcases hop with h | h
      · exact ⟨a, b, false, rfl, h⟩
      · exact ⟨a, b, true, rfl, h⟩

private theorem foldBits (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (w : List ℕ) (j : ℕ) :
    (gs.foldl wordStep w).map (·.testBit j) =
      gs.foldl boolStep (w.map (·.testBit j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨a, b, o, hab, hop⟩ := gateForm g (hgs g (by simp)).1 (hgs g (by simp)).2
    simp only [List.foldl_cons]
    rw [ih (fun q hq => hgs q (by simp [hq]))]
    congr 1
    have hbits (k : ℕ) :
        (w[k]?.getD 0).testBit j = (w[k]?.map (·.testBit j)).getD false := by
      cases w[k]? <;> simp
    cases o <;>
      simp [wordStep, boolStep, hab, hop, GateOp.eval, Nat.testBit_or, Nat.testBit_and,
        hbits]

private theorem evalTest {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 14 C) (j : Fin 58) :
    C.eval (List.ofFn (test j)) = ((C.gates.foldl wordStep columns).getD C.output 0).testBit j.val := by
  have inputs : columns.map (·.testBit j.val) = List.ofFn (test j) := by
    apply List.ext_getElem
    · simp [columns]
    · intro k hk hm
      simp only [List.length_map] at hk
      rw [List.getElem_map, List.getElem_ofFn]
      exact congrArg (·.testBit j.val) (List.getD_eq_getElem _ _ hk).symm
  rw [getD_bits, foldBits C.gates (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩), inputs]
  rfl

private theorem foldMono (gs : List Gate)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
    (x y : List Bool) (hlen : x.length = y.length)
    (hxy : ∀ k, x.getD k false ≤ y.getD k false) (k : ℕ) :
    (gs.foldl boolStep x).getD k false ≤ (gs.foldl boolStep y).getD k false := by
  induction gs generalizing x y with
  | nil => exact hxy k
  | cons g gs ih =>
    obtain ⟨a, b, o, hab, hop⟩ := gateForm g (hgs g (by simp)).1 (hgs g (by simp)).2
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (by simp [hq])) _ _ (by simp [boolStep, hlen])
    intro i
    simp only [boolStep, readAppend, hlen]
    by_cases e : i = y.length
    · simp only [e, ite_true, hab, hop, List.map_cons, List.map_nil]
      have ha := hxy a
      have hb := hxy b
      cases o
      · simpa [GateOp.eval] using
          Bool.le_and ((Bool.and_le_left _ _).trans ha) ((Bool.and_le_right _ _).trans hb)
      · simpa [GateOp.eval] using
          Bool.or_le (ha.trans (Bool.left_le_or _ _)) (hb.trans (Bool.right_le_or _ _))
    · simpa only [e, ite_false] using hxy i

private theorem evalMono {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 14 C)
    (x y : Fin 14 → Bool) (hxy : ∀ i, x i = true → y i = true)
    (hx : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  apply Bool.le_iff_imp.mp _ hx
  apply foldMono C.gates (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩) _ _ (by simp)
  intro k
  rw [readOfFn, readOfFn]
  by_cases hk : k < 14
  · simpa only [dite_eq_left hk, Bool.le_iff_imp] using hxy ⟨k, hk⟩
  · simp [hk]

private theorem lowerBound {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 14 C)
    (hword : (C.gates.foldl wordStep columns).getD C.output 0 = 2097151) : 27 ≤ C.size := by
  have htest (j : Fin 58) : C.eval (List.ofFn (test j)) = (2097151 : ℕ).testBit j.val := by
    rw [evalTest hC, hword]
  have yes : ∀ j : Fin 21, (2097151 : ℕ).testBit (Fin.castAdd 37 j).val = true := by decide
  have no : ∀ j : Fin 37, (2097151 : ℕ).testBit (Fin.natAdd 21 j).val = false := by decide
  have pos (p l : Fin 7) (hp : incidence p l) :
      (C.eval (List.ofFn fun i : Fin 14 => decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l))) =
        true := by
    obtain ⟨j, hj⟩ := pairIndex p l hp
    have he := funext hj
    simpa only [he, yes] using htest (Fin.castAdd 37 j)
  have neg (m : ℕ) (hm : m ∈ negative) :
      C.eval (List.ofFn fun i : Fin 14 => m.testBit i.val) = false := by
    obtain ⟨k, hk, hkm⟩ := List.mem_iff_getElem.mp hm
    obtain ⟨j, hj⟩ := maskIndex ⟨k, hk⟩
    have he := funext hj
    simpa only [he, List.get_eq_getElem, hkm, no] using htest (Fin.natAdd 21 j)
  have compute := PEqualNP.Outside.L_meta_18556
    (fun x => C.eval (List.ofFn x)) (evalMono hC) pos neg
  have mono : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using hC.1 g hg, (hC.2.2 g hg).le⟩
  apply PEqualNP.Outside.L_meta_17589 C mono
  have line : ∀ p l : Fin 7, p ∈ fanoLines l ↔ incidence p l := by decide
  simpa only [line, incidence] using compute

set_option maxHeartbeats 2000000 in
theorem refute :
    ¬ (∃ (x1 : Circuit), x1.size ≤ 26 ∧ PEqualNP.TopForm.IsAO2 14 x1 ∧
        (List.foldl
          (fun (x2 : List ℕ) (x3 : Gate) =>
            have x4 : ℕ := x2.getD (x3.inputs.getD 0 0) 0
            have x5 : ℕ := x2.getD (x3.inputs.getD 1 0) 0
            x2 ++ [if x3.op.eval [false, true] = true then x4 ||| x5 else x4 &&& x5])
          [189297016294346753, 155696362464247818, 218994303132237904,
           183565875465421444, 229736628136977440, 270286071508582656,
           288160007408715776, 95229015649943559, 55389823206162488,
           14003410187583936, 8521481457152, 4292497062785024,
           256463044608, 63038589501440] x1.gates).getD x1.output 0 = 2097151) := by
  rintro ⟨C, hsize, hC, hword⟩
  have hlo := lowerBound hC hword
  omega

end PEqualNP.Outside.FanoMaskRefutation

#print axioms PEqualNP.Outside.FanoMaskRefutation.refute
