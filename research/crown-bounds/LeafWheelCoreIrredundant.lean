import PEqualNP.Defs
import PEqualNP.Outside.L_meta_10788

namespace LeafWheelCoreIrredundant

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_10788
open L11022RestrictSupport CircuitHelpers CircuitHelpers.Readers L10586WeightedRestriction

private def WireStats (xs : List Stat) : Prop :=
  ∀ i < xs.length, ∃ j, xs.getD i (.const false) = .wire j

private theorem wireStatsAppend {xs : List Stat} (h : WireStats xs) (j : ℕ) :
    WireStats (xs ++ [.wire j]) := by
  intro i hi
  by_cases before : i < xs.length
  · obtain ⟨w, eq⟩ := h i before
    exact ⟨w, (List.getD_append _ _ _ _ before).trans eq⟩
  · have eq : i = xs.length := by simp at hi; omega
    subst i
    exact ⟨j, by simp⟩

private theorem initialWireStats (n : ℕ) : WireStats (idStats n) := by
  intro i hi
  refine ⟨i, ?_⟩
  rw [List.getD_eq_getElem _ _ hi]
  simp [idStats]

private theorem cleanStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate)
    (hw : WireStats acc.1) (hc : CleanGate acc.1.length g) :
    ∃ g', g'.op = g.op ∧ elimStep n acc g =
      (acc.1 ++ [.wire (n + acc.2.length)], acc.2 ++ [g']) := by
  rcases hc with ⟨tag, a, ha, ins⟩ | ⟨tag, a, b, ha, hb, ins⟩
  · obtain ⟨u, hu⟩ := hw a ha
    refine ⟨⟨.not, [u]⟩, tag.symm, ?_⟩
    simp only [elimStep, tag, ins, List.map_cons, List.map_nil, hu, simplify, simpNot]
    rfl
  · obtain ⟨u, hu⟩ := hw a ha
    obtain ⟨v, hv⟩ := hw b hb
    rcases tag with tag | tag
    · refine ⟨⟨.and, [u, v]⟩, tag.symm, ?_⟩
      simp only [elimStep, tag, ins, List.map_cons, List.map_nil, hu, hv, simplify, simpAnd]
      rfl
    · refine ⟨⟨.or, [u, v]⟩, tag.symm, ?_⟩
      simp only [elimStep, tag, ins, List.map_cons, List.map_nil, hu, hv, simplify, simpOr]
      rfl

private theorem keepOperations (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hw : WireStats acc.1)
    (hc : ∀ i g, gs[i]? = some g → CleanGate (acc.1.length + i) g) :
    WireStats (elim n gs acc).1 ∧
    (elim n gs acc).2.map Gate.op = acc.2.map Gate.op ++ gs.map Gate.op := by
  induction gs generalizing acc with
  | nil => simpa [elim] using hw
  | cons g gs ih =>
    obtain ⟨g', hop, hs⟩ := cleanStep n acc g hw (by simpa using hc 0 g rfl)
    rw [elim_cons, hs]
    obtain ⟨h', eq⟩ := ih (acc.1 ++ [.wire (n + acc.2.length)], acc.2 ++ [g'])
      (wireStatsAppend hw _) (by
        intro i t ht
        have ht' : (g :: gs)[i+1]? = some t := ht
        have := hc (i+1) t ht'
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
    exact ⟨h', by simp [eq, hop, List.append_assoc]⟩

/-- Replacing a gate by an identical earlier wire deletes just that gate. -/
private theorem dropBinaryAlias {n : ℕ} (pre post : List Gate) (g : Gate) (o j : ℕ)
    (hc : CleanL n (pre ++ g :: post)) (hj : j < n + pre.length)
    (ho : o < n + (pre ++ g :: post).length)
    (heq : ∀ x : Fin n → Bool, vl (pre ++ g :: post) x (n + pre.length) =
      vl (pre ++ g :: post) x j) :
    ∃ gs' o', CleanL n gs' ∧ gs'.map Gate.op = (pre ++ post).map Gate.op ∧
      ∀ x : Fin n → Bool, vl gs' x o' = vl (pre ++ g :: post) x o := by
  let before := elim n pre (idStats n, [])
  let joined := (before.1 ++ [before.1.getD j (.const false)], before.2)
  let after := elim n post joined
  have preClean (i : ℕ) (t : Gate) (hit : pre[i]? = some t) : CleanGate (n + i) t := by
    have hi := (List.getElem?_eq_some_iff.mp hit).1
    exact hc i t (by simpa [List.getElem?_append_left hi] using hit)
  have hbefore : before.1.length = n + pre.length := by
    simp [before, elim_fst_len, idStats]
  have hjoined : joined.1.length = n + pre.length + 1 := by simp [joined, hbefore]
  have postClean (i : ℕ) (t : Gate) (hit : post[i]? = some t) : CleanGate (joined.1.length + i) t := by
    have h : (pre ++ g :: post)[pre.length + 1 + i]? = some t := by
      rw [List.getElem?_append_right (by omega)]
      simpa [show pre.length + 1 + i - pre.length = i + 1 by omega] using hit
    simpa [hjoined, Nat.add_assoc] using hc (pre.length + 1 + i) t h
  obtain ⟨hwPre, hopPre⟩ := keepOperations n pre (idStats n, []) (initialWireStats n)
    (by simpa [idStats] using preClean)
  obtain ⟨wire, hit⟩ := hwPre j (by simpa [before, hbefore] using hj)
  change before.1.getD j (.const false) = .wire wire at hit
  have wJoined : WireStats joined.1 := by
    show WireStats (before.1 ++ [before.1.getD j (.const false)])
    rw [hit]
    exact wireStatsAppend hwPre wire
  have ⟨hwPost, hopPost⟩ := keepOperations n post joined wJoined postClean
  have afterLength : after.1.length = n + (pre ++ g :: post).length := by
    simp [after, elim_fst_len, hjoined, Nat.add_assoc]
    omega
  obtain ⟨out, hout⟩ := hwPost o (show o < after.1.length by rwa [afterLength])
  have preOK : ∀ t ∈ pre, Ok t := fun t h =>
    (clean_nok _ _ hc t (List.mem_append_left _ h)).1
  have postOK : ∀ t ∈ post, Ok t := fun t h =>
    (clean_nok _ _ hc t (List.mem_append_right _ (List.mem_cons_of_mem _ h))).1
  have invPre (x : Fin n → Bool) : Inv n (List.ofFn x) (wiresFrom pre (List.ofFn x)) before :=
    inv_elim n _ (by simp) pre _ _ preOK (inv_id n x)
  let bit (x : Fin n → Bool) := g.op.eval (g.inputs.map (fun i => (wiresFrom pre (List.ofFn x)).getD i false))
  have invJoined (x : Fin n → Bool) :
      Inv n (List.ofFn x) (wiresFrom pre (List.ofFn x) ++ [bit x]) joined := by
    have hlen : (wiresFrom pre (List.ofFn x)).length = before.1.length := (invPre x).1.symm
    have hwire : ∀ i < before.1.length,
        vl (pre ++ g :: post) x i = (wiresFrom pre (List.ofFn x)).getD i false := by
      intro i hi
      unfold vl
      rw [wiresFrom_append, getD_wiresFrom _ _ _ (by rwa [hlen])]
    have atGate : vl (pre ++ g :: post) x (n + pre.length) = bit x := by
      unfold vl
      rw [wiresFrom_append]
      change (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [bit x])).getD _ _ = _
      rw [getD_wiresFrom _ _ _ (by simp [hlen, hbefore])]
      exact getD_snoc_len _ _ _ _ (by rw [hlen, hbefore])
    refine ⟨by simp [hjoined, hlen, hbefore], ?_⟩
    intro i
    by_cases eq : i = before.1.length
    · subst i
      have h := (invPre x).2 j
      change ((before.1 ++ [before.1.getD j (.const false)]).getD _ _).Valid _ ∧
        ((before.1 ++ [before.1.getD j (.const false)]).getD _ _).val _ = _
      rw [getD_snoc_eq, getD_snoc_len _ _ _ _ hlen]
      exact ⟨h.1, h.2.trans ((hwire j (by rwa [hbefore])).symm.trans ((heq x).symm.trans atGate))⟩
    · change ((before.1 ++ [before.1.getD j (.const false)]).getD _ _).Valid _ ∧
        ((before.1 ++ [before.1.getD j (.const false)]).getD _ _).val _ = _
      rw [getD_snoc_ne _ _ _ _ eq, getD_snoc_ne _ _ _ _ (by rwa [hlen])]
      exact (invPre x).2 i
  have cleanBefore : CleanL n before.2 :=
    clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) pre _ _ preOK (inv_id n _)
      (by intro p g hg; simp at hg)
  have cleanAfter : CleanL n after.2 :=
    clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) post _ _ postOK (invJoined _) cleanBefore
  refine ⟨after.2, out, cleanAfter, ?_, ?_⟩
  · simpa [after, joined, before, hopPre] using hopPost
  · intro x
    have hv := ((inv_elim n _ (by simp) post _ _ postOK (invJoined x)).2 o).2
    change (after.1.getD o (.const false)).val (wiresFrom after.2 (List.ofFn x)) = _ at hv
    rw [show after.1.getD o (.const false) = .wire out from hout] at hv
    simp only [vl, wiresFrom_append]
    exact hv

/-- In an eleven-gate clean wheel circuit with one NOT, each binary gate has a new truth table. -/
theorem noBinaryAlias {gs : List Gate} {out p j : ℕ} {g : Gate}
    (clean : CleanL 6 gs) (correct : ∀ x, vl gs x out = L10788Wheel.target x)
    (size : gs.length = 11) (one : notGateCount gs = 1)
    (hit : gs[p]? = some g) (bin : g.op = .and ∨ g.op = .or) (earlier : j < 6 + p) :
    ∃ x : Fin 6 → Bool, vl gs x (6 + p) ≠ vl gs x j := by
  by_contra! same
  have validOut : out < 6 + gs.length := by
    by_contra! invalid
    obtain ⟨x, y, hd⟩ := L10788Wheel.nonconstant
    exact hd ((correct x).symm.trans ((vl_beyond _ _ _ invalid).trans
      ((vl_beyond _ _ _ invalid).symm.trans (correct y))))
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hit
  obtain ⟨gs', out', clean', ops, eval'⟩ := dropBinaryAlias pre post g out j clean earlier validOut same
  have size' := congrArg List.length ops
  simp only [List.length_map, List.length_append, List.length_cons] at size size'
  have keepNot : notGateCount gs' = 1 := by
    have eq := congrArg (List.countP isNotGate) ops
    simp only [List.countP_map, Function.comp_def] at eq
    have hz : isNotGate g.op = false := bin.elim (fun e => by simp [e, isNotGate])
      (fun e => by simp [e, isNotGate])
    rw [notGateCount, ← List.countP_eq_length_filter] at one ⊢
    rw [eq]
    simpa [List.countP_append, hz] using one
  have count := binary_add_not gs'
  exact L10788WheelClose.signed_wheel_impossible clean'
    (fun x => (eval' x).trans (correct x)) (by omega) keepNot

/-- Neither operand of a binary gate in this circuit implies the other. -/
theorem incomparableOperands {gs : List Gate} {out p a b : ℕ} {g : Gate}
    (clean : CleanL 6 gs) (correct : ∀ x, vl gs x out = L10788Wheel.target x)
    (size : gs.length = 11) (one : notGateCount gs = 1)
    (hit : gs[p]? = some g) (bin : g.op = .and ∨ g.op = .or) (ports : g.inputs = [a, b]) :
    (∃ x : Fin 6 → Bool, vl gs x a = true ∧ vl gs x b = false) ∧
    (∃ x : Fin 6 → Bool, vl gs x a = false ∧ vl gs x b = true) := by
  have aEarly := (clean p g hit).lt a (by simp [ports])
  have bEarly := (clean p g hit).lt b (by simp [ports])
  obtain ⟨x, diffA⟩ := noBinaryAlias clean correct size one hit bin aEarly
  obtain ⟨y, diffB⟩ := noBinaryAlias clean correct size one hit bin bEarly
  rw [vl_gate gs clean x p g hit, ports] at diffA
  rw [vl_gate gs clean y p g hit, ports] at diffB
  rcases bin with andOp | orOp
  · constructor
    · refine ⟨x, ?_⟩
      cases aVal : vl gs x a <;> cases bVal : vl gs x b <;>
        simp [andOp, GateOp.eval, aVal, bVal] at diffA ⊢
    · refine ⟨y, ?_⟩
      cases aVal : vl gs y a <;> cases bVal : vl gs y b <;>
        simp [andOp, GateOp.eval, aVal, bVal] at diffB ⊢
  · constructor
    · refine ⟨y, ?_⟩
      cases aVal : vl gs y a <;> cases bVal : vl gs y b <;>
        simp [orOp, GateOp.eval, aVal, bVal] at diffB ⊢
    · refine ⟨x, ?_⟩
      cases aVal : vl gs x a <;> cases bVal : vl gs x b <;>
        simp [orOp, GateOp.eval, aVal, bVal] at diffA ⊢

end LeafWheelCoreIrredundant
