import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LineDegTest

namespace PlaneQuadranglePairs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.HeptadCover
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity

private def label (i : Fin 26) : Fin 13 := Fin.ofNat 13 i.val

/-- Adjacency on the point wires 0–12 and line wires 13–25. -/
def Adj (u v : Fin 26) : Prop :=
  if u.val < 13 then 13 ≤ v.val ∧ label u ∈ singerLines3 (label v)
  else v.val < 13 ∧ label v ∈ singerLines3 (label u)

instance (u v : Fin 26) : Decidable (Adj u v) := by
  unfold Adj
  infer_instance

private def pointPoint (d : Fin 13) : Finset (Fin 13) :=
  ![{0, 1, 2, 5}, {0, 1, 2, 5}, {0, 1, 2, 5}, {0, 2, 3, 4}, {0, 1, 4, 6},
    {0, 1, 2, 5}, {0, 1, 2, 6}, {0, 1, 2, 7}, {0, 1, 4, 8}, {0, 2, 4, 9},
    {0, 1, 5, 10}, {0, 1, 2, 11}, {0, 1, 4, 12}] d

private def lineLine (d : Fin 13) : Finset (Fin 13) :=
  ![{2, 4, 5, 6}, {5, 6, 7, 11}, {4, 6, 7, 8}, {2, 5, 7, 8}, {2, 6, 8, 10},
    {2, 4, 7, 11}, {4, 5, 8, 10}, {2, 4, 5, 6}, {2, 5, 6, 10}, {2, 4, 6, 8},
    {2, 4, 5, 8}, {2, 4, 5, 6}, {4, 5, 6, 10}] d

private def pointLine (d : Fin 13) : Finset (Fin 13) :=
  ![{0, 1, 2, 3}, {0, 1, 2, 3}, {2, 4, 5, 6}, {0, 1, 2, 3}, {2, 4, 5, 6},
    {2, 4, 5, 6}, {2, 4, 5, 6}, {2, 4, 7, 8}, {2, 4, 5, 8}, {0, 1, 2, 3},
    {2, 5, 6, 10}, {2, 4, 6, 11}, {2, 4, 5, 12}] d

private def translate (Q : Finset (Fin 13)) (d : Fin 13) : Finset (Fin 13) :=
  Q.image (fun p => p + d)

private def containingQuad (u v : Fin 26) : Finset (Fin 13) :=
  let a := label u
  let b := label v
  if u.val < 13 then
    if v.val < 13 then translate (pointPoint (b - a)) a else translate (pointLine (a - b)) b
  else
    if v.val < 13 then translate (pointLine (b - a)) a else translate (lineLine (b - a)) a

private def quadrangleBits (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  Fin.append (fun p => decide (p ∈ Q)) (fun l => decide (l ∈ missLines singerLines3 Q))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
private theorem quadCertificate : ∀ u v : Fin 26, ¬ Adj u v →
    IsQuadrangle singerLines3 (containingQuad u v) ∧
    quadrangleBits (containingQuad u v) u = true ∧
    quadrangleBits (containingQuad u v) v = true := by
  decide +kernel

private theorem pairCertificate : ∀ u v : Fin 26, Adj u v →
    (Fin.castAdd 13 (label u) = u ∧ Fin.natAdd 13 (label v) = v ∨
     Fin.castAdd 13 (label v) = v ∧ Fin.natAdd 13 (label u) = u) := by
  decide +kernel

private theorem castPair : ∀ p l : Fin 13,
    List.ofFn (pairInput (Fin.castAdd 13 p) (Fin.natAdd 13 l)) = incidenceInput {p} {l} := by
  decide +kernel

private theorem adjForward (u v : Fin 26) (h : Adj u v) :
    (∃ p l : Fin 13, p ∈ singerLines3 l ∧
      List.ofFn (pairInput u v) = incidenceInput {p} {l}) := by
  obtain ⟨hu, hv⟩ | ⟨hv, hu⟩ := pairCertificate u v h
  · have side : u.val < 13 := by rw [← hu]; exact (label u).isLt
    have conjuncts : 13 ≤ v.val ∧ label u ∈ singerLines3 (label v) := by
      simpa [Adj, side] using h
    exact ⟨label u, label v, conjuncts.2, by simpa only [hu, hv] using castPair (label u) (label v)⟩
  · have side : ¬ u.val < 13 := by rw [← hu]; simp
    have conjuncts : v.val < 13 ∧ label v ∈ singerLines3 (label u) := by
      simpa [Adj, side] using h
    exact ⟨label v, label u, conjuncts.2, by
      rw [show pairInput u v = pairInput v u from by funext k; simp [pairInput, or_comm]]
      simpa only [hu, hv] using castPair (label v) (label u)⟩

private theorem evalMono (C : Circuit) (m : Monotone2 C) (x y : Fin 26 → Bool)
    (h : ∀ k, x k = true → y k = true) (hx : C.eval (List.ofFn x) = true) :
    C.eval (List.ofFn y) = true := by
  refine LineDegTest.W_mono C.gates (fun g hg => (m g hg).1) _ _ (by simp) ?_ C.output hx
  intro i hi
  have hb := LineDegTest.getD_false_lt hi
  have ilt : i < 26 := by simpa using hb
  rw [List.getD_eq_getElem _ _ (by simpa using ilt)] at hi ⊢
  simp only [List.getElem_ofFn] at hi ⊢
  exact h ⟨i, ilt⟩ hi

/-- The quadrangle negatives and incident positives determine every singleton or pair test. -/
theorem pairTests (C : Circuit) (m : Monotone2 C) (pos : RightOnIncidentPairs singerLines3 C)
    (neg : ∀ Q, IsQuadrangle singerLines3 Q →
      C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) :
    ∀ u v, C.eval (List.ofFn (pairInput u v)) = decide (Adj u v) := by
  intro u v
  by_cases edge : Adj u v
  · obtain ⟨p, l, inc, inputs⟩ := adjForward u v edge
    rw [inputs, decide_eq_true edge]
    exact pos l p inc
  · simp only [edge, decide_false]
    obtain ⟨arc, qu, qv⟩ := quadCertificate u v edge
    cases h : C.eval (List.ofFn (pairInput u v)) with
    | false => rfl
    | true =>
      have accepted := evalMono C m (pairInput u v) (quadrangleBits (containingQuad u v))
        (fun k hk => by
          simp only [pairInput, decide_eq_true_eq] at hk
          rcases hk with rfl | rfl
          · exact qu
          · exact qv) h
      rw [quadrangleBits, List.ofFn_fin_append] at accepted
      rw [← incidenceInput, neg _ arc] at accepted
      contradiction

end PlaneQuadranglePairs
