import PEqualNP.Defs
import PEqualNP.Outside.L_meta_17589
import PEqualNP.Outside.L_meta_18546

namespace PEqualNP.Outside.DoubleReadTrace

open PEqualNP.CircuitLowerBounds

def BinaryBack (n : ℕ) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
    ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j

def ReadCertificate (C : Circuit) (r s : Fin n) (d : ℕ → ℕ) : Prop :=
  d r.val ≤ 1 ∧ d s.val = 0 ∧
  ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
    (g.op = .and → d (n + j) ≤ d a + d b) ∧
    (g.op = .or → d (n + j) ≤ min (d a) (d b))

def value (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def pair (r s : Fin n) (x : Fin n) : Bool := decide (x = r ∨ x = s)

def single (s : Fin n) (x : Fin n) : Bool := decide (x = s)

def ActiveAnd (C : Circuit) (r s : Fin n) (j : ℕ) : Prop :=
  ∃ g, C.gates[j]? = some g ∧ g.op = .and ∧ value C (pair r s) (n + j) = true

def PairOnly (C : Circuit) (r s : Fin n) (w : ℕ) : Prop :=
  value C (pair r s) w = true ∧ value C (single r) w = false ∧
    value C (single s) w = false

def PairAnd (C : Circuit) (r s : Fin n) (j : ℕ) : Prop :=
  ∃ g, C.gates[j]? = some g ∧ g.op = .and ∧ PairOnly C r s (n + j)

inductive ActivePath (C : Circuit) (x : Fin n → Bool) : ℕ → ℕ → Prop where
  | here (w) : ActivePath C x w w
  | step {first w j g} : ActivePath C x first w → C.gates[j]? = some g →
      w ∈ g.inputs → value C x (n + j) = true → ActivePath C x first (n + j)

private def extend (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun k => w.getD k false))]

private theorem foldLength (gs : List Gate) (w : List Bool) :
    (gs.foldl extend w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, extend, Nat.add_comm, Nat.add_left_comm]

private theorem foldKeeps (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl extend w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [extend]; omega)]
    simp [extend, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private theorem atInput (C : Circuit) (x : Fin n → Bool) (w : Fin n) :
    value C x w.val = x w := by
  change (C.gates.foldl extend (List.ofFn x)).getD w.val false = _
  rw [foldKeeps _ _ _ (by simp)]
  have h : w.val < (List.ofFn x).length := by simp
  rw [List.getD_eq_getElem _ _ h, List.getElem_ofFn]

private theorem validOfTrue {C : Circuit} {x : Fin n → Bool} {w : ℕ}
    (h : value C x w = true) : w < n + C.gates.length := by
  by_contra! hw
  change (C.gates.foldl extend (List.ofFn x)).getD w false = true at h
  rw [List.getD_eq_default _ _ (by simpa [foldLength] using hw)] at h
  contradiction

private theorem gateValue {C : Circuit} {j : ℕ} {g : Gate} (x : Fin n → Bool)
    (hg : C.gates[j]? = some g) (back : ∀ k ∈ g.inputs, k < n + j) :
    value C x (n + j) = g.op.eval (g.inputs.map (value C x)) := by
  obtain ⟨hj, hjg⟩ := List.getElem?_eq_some_iff.mp hg
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, hjg]
  let w := (C.gates.take j).foldl extend (List.ofFn x)
  have hw : w.length = n + j := by simp [w, foldLength, Nat.min_eq_left hj.le]
  let v := g.op.eval (g.inputs.map (fun k => w.getD k false))
  let next := w ++ [v]
  have hv : n + j < next.length := by simp [next, hw]
  have rewriteValue (k : ℕ) : value C x k =
      ((C.gates.drop (j + 1)).foldl extend next).getD k false := by
    change (C.gates.foldl extend (List.ofFn x)).getD k false = _
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
    rfl
  have keep (k : ℕ) (hk : k < n+j) : value C x k = w.getD k false := by
    rw [rewriteValue, foldKeeps _ _ _ (by simp [next, hw]; omega)]
    simp [next, List.getD_eq_getElem?_getD, List.getElem?_append_left (hw.symm ▸ hk)]
  rw [rewriteValue, foldKeeps _ _ _ hv]
  have atNext : next.getD (n+j) false = v := by
    rw [← hw]
    simp [next, List.getD_eq_getElem?_getD]
  rw [atNext]
  unfold v
  congr 1
  exact List.map_congr_left (fun k hk => (keep k (back k hk)).symm)

private theorem andValue {C : Circuit} {j a b : ℕ} {g : Gate} (x : Fin n → Bool)
    (hg : C.gates[j]? = some g) (hab : g.inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) (hop : g.op = .and) :
    value C x (n + j) = (value C x a && value C x b) := by
  rw [gateValue x hg (by intro k hk; simp [hab] at hk; rcases hk with rfl | rfl <;> assumption)]
  simp [hab, hop, GateOp.eval]

private theorem orValue {C : Circuit} {j a b : ℕ} {g : Gate} (x : Fin n → Bool)
    (hg : C.gates[j]? = some g) (hab : g.inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) (hop : g.op = .or) :
    value C x (n + j) = (value C x a || value C x b) := by
  rw [gateValue x hg (by intro k hk; simp [hab] at hk; rcases hk with rfl | rfl <;> assumption)]
  simp [hab, hop, GateOp.eval]

private theorem gateFor {C : Circuit} (shape : BinaryBack n C) {w : ℕ}
    (lo : n ≤ w) (hi : w < n + C.gates.length) :
    ∃ j g a b, w = n + j ∧ C.gates[j]? = some g ∧
      (g.op = .and ∨ g.op = .or) ∧ g.inputs = [a, b] ∧ a ≠ b ∧ a < w ∧ b < w := by
  let j := w - n
  have hj : j < C.gates.length := by dsimp [j]; omega
  have hw : w = n+j := by dsimp [j]; omega
  have hg : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
  obtain ⟨hop, a, b, hab, hne, ha, hb⟩ := shape j _ hg
  exact ⟨j, _, a, b, hw, hg, hop, hab, hne, hw ▸ ha, hw ▸ hb⟩

private theorem valueMono {C : Circuit} {x y : Fin n → Bool} (shape : BinaryBack n C)
    (hxy : ∀ i, x i = true → y i = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases h : w < n
    · simpa only [atInput C x ⟨w, h⟩, atInput C y ⟨w, h⟩] using hxy ⟨w, h⟩ (by
        simpa only [atInput C x ⟨w, h⟩] using hw)
    · obtain ⟨j, g, a, b, rfl, hg, hop, hab, _, ha, hb⟩ :=
        gateFor shape (by omega) (validOfTrue hw)
      rcases hop with hop | hop
      · rw [andValue x hg hab ha hb hop, Bool.and_eq_true] at hw
        rw [andValue y hg hab ha hb hop, Bool.and_eq_true]
        exact ⟨ih a ha hw.1, ih b hb hw.2⟩
      · rw [orValue x hg hab ha hb hop, Bool.or_eq_true] at hw
        rw [orValue y hg hab ha hb hop, Bool.or_eq_true]
        exact hw.imp (ih a ha) (ih b hb)

private theorem single_mono_pair {C : Circuit} (shape : BinaryBack n C) (r s : Fin n) (w : ℕ) :
    value C (single s) w = true → value C (pair r s) w = true := by
  apply valueMono shape _ w
  intro i hi
  simp only [single, decide_eq_true_eq] at hi
  simp [pair, hi]

def Merge (C : Circuit) (r s : Fin n) (j : ℕ) : Prop :=
  ∃ g a b, C.gates[j]? = some g ∧ g.op = .and ∧ g.inputs = [a, b] ∧
    value C (pair r s) a = true ∧ value C (pair r s) b = true ∧
    value C (single s) a = false ∧ value C (single s) b = false

private def quota (C : Circuit) (s : Fin n) (w : ℕ) : ℕ :=
  if value C (single s) w = true then 0 else 1

private theorem heavyMerge {C : Circuit} {r s : Fin n} {d : ℕ → ℕ}
    (shape : BinaryBack n C) (cert : ReadCertificate C r s d) (w : ℕ)
    (hw : value C (pair r s) w = true) (heavy : quota C s w < d w) :
    ∃ j, Merge C r s j ∧ ActivePath C (pair r s) (n + j) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w < n
    · let i : Fin n := ⟨w, h⟩
      have hi : i = r ∨ i = s := by
        have hi := (atInput C (pair r s) i).symm.trans hw
        simpa [pair] using hi
      rcases hi with hir | his
      · by_cases hrs : r = s
        · have hws : w = s.val := congrArg Fin.val (hir.trans hrs)
          rw [hws, cert.2.1] at heavy
          omega
        · have hf : value C (single s) w = false := by
            change value C (single s) i.val = false
            rw [atInput]
            simp [hir, single, hrs]
          have hit : w = r.val := congrArg Fin.val hir
          have hd : 1 < d r.val := by
            simp [quota, hf] at heavy
            rwa [hit] at heavy
          exact (not_lt_of_ge cert.1 hd).elim
      · have hws : w = s.val := congrArg Fin.val his
        rw [hws, cert.2.1] at heavy
        omega
    · obtain ⟨j, g, a, b, rfl, hg, hop, hab, _, ha, hb⟩ :=
        gateFor shape (by omega) (validOfTrue hw)
      have extendA (htrue : value C (pair r s) a = true) (hq : quota C s a < d a) :
          ∃ k, Merge C r s k ∧ ActivePath C (pair r s) (n + k) (n + j) := by
        obtain ⟨k, hk, hp⟩ := ih a ha htrue hq
        exact ⟨k, hk, .step hp hg (by simp [hab]) hw⟩
      have extendB (htrue : value C (pair r s) b = true) (hq : quota C s b < d b) :
          ∃ k, Merge C r s k ∧ ActivePath C (pair r s) (n + k) (n + j) := by
        obtain ⟨k, hk, hp⟩ := ih b hb htrue hq
        exact ⟨k, hk, .step hp hg (by simp [hab]) hw⟩
      rcases hop with hop | hop
      · have hbnd := (cert.2.2 j g a b hg hab).1 hop
        have hon := Bool.and_eq_true_iff.mp ((andValue (pair r s) hg hab ha hb hop).symm.trans hw)
        by_cases hea : quota C s a < d a
        · exact extendA hon.1 hea
        by_cases heb : quota C s b < d b
        · exact extendB hon.2 heb
        have ho := andValue (single s) hg hab ha hb hop
        cases ca : value C (single s) a <;> cases cb : value C (single s) b <;>
          simp [quota, ho, ca, cb] at hea heb heavy
        · exact ⟨j, ⟨g, a, b, hg, hop, hab, hon.1, hon.2, ca, cb⟩, .here _⟩
        all_goals omega
      · have hbnd := (cert.2.2 j g a b hg hab).2 hop
        have hone := orValue (pair r s) hg hab ha hb hop
        have hoff := orValue (single s) hg hab ha hb hop
        have eA (hc : value C (single s) a = value C (single s) (n + j))
            (hp : value C (pair r s) a = true) :
            ∃ k, Merge C r s k ∧ ActivePath C (pair r s) (n + k) (n + j) := by
          apply extendA hp
          have hq : quota C s a = quota C s (n+j) := by simp [quota, hc]
          have hda := (Nat.le_min.mp hbnd).1
          omega
        have eB (hc : value C (single s) b = value C (single s) (n + j))
            (hp : value C (pair r s) b = true) :
            ∃ k, Merge C r s k ∧ ActivePath C (pair r s) (n + k) (n + j) := by
          apply extendB hp
          have hq : quota C s b = quota C s (n+j) := by simp [quota, hc]
          have hdb := (Nat.le_min.mp hbnd).2
          omega
        cases hc : value C (single s) (n+j)
        · rw [hc] at hoff
          have hcold := Bool.or_eq_false_iff.mp hoff.symm
          rcases Bool.or_eq_true_iff.mp (hone.symm.trans hw) with hp | hp
          · exact eA (hcold.1.trans hc.symm) hp
          · exact eB (hcold.2.trans hc.symm) hp
        · rw [hc] at hoff
          rcases Bool.or_eq_true_iff.mp hoff.symm with ho | ho
          · exact eA (ho.trans hc.symm) (single_mono_pair shape r s a ho)
          · exact eB (ho.trans hc.symm) (single_mono_pair shape r s b ho)

/-- A weight of at least two requires a merge on a path that is active on the pair. -/
theorem overlap_of_certificate {C : Circuit} {r s : Fin n} {d : ℕ → ℕ}
    (shape : BinaryBack n C) (cert : ReadCertificate C r s d) {w : ℕ}
    (hw : value C (pair r s) w = true) (h : 2 ≤ d w) :
    ∃ j, Merge C r s j ∧ ActivePath C (pair r s) (n + j) w := by
  apply heavyMerge shape cert w hw
  unfold quota
  split <;> omega

def Cross (C : Circuit) (r s : Fin n) (j : ℕ) : Prop :=
  ∃ g a b, C.gates[j]? = some g ∧ g.op = .and ∧ g.inputs = [a, b] ∧
    PairOnly C r s (n + j) ∧
    (value C (single r) a = true ∨ value C (single r) b = true) ∧
    (value C (single s) a = true ∨ value C (single s) b = true)

private theorem pairComm (r s : Fin n) : pair r s = pair s r := by
  funext i
  simp [pair, or_comm]

private theorem crossComm {C : Circuit} {r s : Fin n} {j : ℕ} (h : Cross C r s j) :
    Cross C s r j := by
  obtain ⟨g, a, b, hg, hop, hab, ⟨hpair, hr, hs⟩, ha, hb⟩ := h
  rw [pairComm r s] at hpair
  exact ⟨g, a, b, hg, hop, hab, ⟨hpair, hs, hr⟩, hb, ha⟩

private theorem noPairOnlyInput {C : Circuit} {r s : Fin n} {w : ℕ} (hw : w < n) :
    ¬ PairOnly C r s w := by
  rintro ⟨hp, hr, hs⟩
  let i : Fin n := ⟨w, hw⟩
  have h : i = r ∨ i = s := by
    have hi := (atInput C (pair r s) i).symm.trans hp
    simpa [pair] using hi
  rcases h with h | h
  · have hi := (atInput C (single r) i).symm.trans hr
    simp [single, h] at hi
  · have hi := (atInput C (single s) i).symm.trans hs
    simp [single, h] at hi

private theorem earliestPairOnly {C : Circuit} {r s : Fin n} {w : ℕ}
    (shape : BinaryBack n C) (hw : PairOnly C r s w)
    (before : ∀ v < w, ¬ PairOnly C r s v) : ∃ j, Cross C r s j := by
  have hn : n ≤ w := by
    by_contra! h
    exact noPairOnlyInput h hw
  obtain ⟨j, g, a, b, rfl, hg, hop, hab, _, ha, hb⟩ :=
    gateFor shape hn (validOfTrue hw.1)
  rcases hop with hop | hop
  · have live := Bool.and_eq_true_iff.mp ((andValue (pair r s) hg hab ha hb hop).symm.trans hw.1)
    have left : value C (single r) a = true ∨ value C (single r) b = true := by
      by_contra! no
      have ra : value C (single r) a = false := by simpa using no.1
      have rb : value C (single r) b = false := by simpa using no.2
      have sa : value C (single s) a = true := by
        cases h : value C (single s) a
        · exact (before _ ha ⟨live.1, ra, h⟩).elim
        · rfl
      have sb : value C (single s) b = true := by
        cases h : value C (single s) b
        · exact (before _ hb ⟨live.2, rb, h⟩).elim
        · rfl
      have key := (andValue (single s) hg hab ha hb hop).symm.trans hw.2.2
      simp [sa, sb] at key
    have right : value C (single s) a = true ∨ value C (single s) b = true := by
      by_contra! no
      have sa : value C (single s) a = false := by simpa using no.1
      have sb : value C (single s) b = false := by simpa using no.2
      have ra : value C (single r) a = true := by
        cases h : value C (single r) a
        · exact (before _ ha ⟨live.1, h, sa⟩).elim
        · rfl
      have rb : value C (single r) b = true := by
        cases h : value C (single r) b
        · exact (before _ hb ⟨live.2, h, sb⟩).elim
        · rfl
      have key := (andValue (single r) hg hab ha hb hop).symm.trans hw.2.1
      simp [ra, rb] at key
    exact ⟨j, g, a, b, hg, hop, hab, hw, left, right⟩
  · have hr := Bool.or_eq_false_iff.mp ((orValue (single r) hg hab ha hb hop).symm.trans hw.2.1)
    have hs := Bool.or_eq_false_iff.mp ((orValue (single s) hg hab ha hb hop).symm.trans hw.2.2)
    rcases Bool.or_eq_true_iff.mp ((orValue (pair r s) hg hab ha hb hop).symm.trans hw.1) with hl | hl
    · exact (before _ ha ⟨hl, hr.1, hs.1⟩).elim
    · exact (before _ hb ⟨hl, hr.2, hs.2⟩).elim

theorem cross_of_pairOnly {C : Circuit} {r s : Fin n} {w : ℕ}
    (shape : BinaryBack n C) (hw : PairOnly C r s w) : ∃ j, Cross C r s j := by
  classical
  have hex : ∃ w, PairOnly C r s w := ⟨w, hw⟩
  exact earliestPairOnly shape (Nat.find_spec hex) (fun _ h => Nat.find_min hex h)

private theorem mergeActive {C : Circuit} {r s : Fin n} {j : ℕ}
    (shape : BinaryBack n C) (hm : Merge C r s j) : ActiveAnd C r s j := by
  obtain ⟨g, a, b, hg, hop, hab, ha, hb, _, _⟩ := hm
  obtain ⟨_, c, d, hcd, _, hc, hd⟩ := shape j g hg
  obtain ⟨hca, he⟩ := List.cons.inj (hcd.symm.trans hab)
  have hdb := (List.cons.inj he).1
  subst c
  subst d
  exact ⟨g, hg, hop, (andValue (pair r s) hg hab hc hd hop).trans (by simp [ha, hb])⟩

private theorem crossActive {C : Circuit} {r s : Fin n} {j : ℕ} (h : Cross C r s j) :
    ActiveAnd C r s j := by
  obtain ⟨g, _, _, hg, hop, _, hw, _⟩ := h
  exact ⟨g, hg, hop, hw.1⟩

private theorem cross_ne_merge {C : Circuit} {r s : Fin n} {i j : ℕ}
    (hx : Cross C r s i) (hm : Merge C r s j) : i ≠ j := by
  rintro rfl
  obtain ⟨g, a, b, hg, _, hab, _, _, hor⟩ := hx
  obtain ⟨f, u, v, hf, _, huv, _, _, hu, hv⟩ := hm
  have e := Option.some.inj (hg.symm.trans hf)
  subst f
  obtain ⟨hau, he⟩ := List.cons.inj (hab.symm.trans huv)
  have hbv := (List.cons.inj he).1
  subst u
  subst v
  simp [hu, hv] at hor

inductive OrPath (C : Circuit) (n : ℕ) : ℕ → ℕ → Prop where
  | here (w) : OrPath C n w w
  | step {u j w g} : C.gates[j]? = some g → g.op = .or → u ∈ g.inputs →
      OrPath C n (n + j) w → OrPath C n u w

theorem readsEarlier {C : Circuit} (shape : BinaryBack n C) {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) {u : ℕ} (hu : u ∈ g.inputs) : u < n + j := by
  obtain ⟨_, a, b, hab, _, ha, hb⟩ := shape j g hg
  simp [hab] at hu
  rcases hu with rfl | rfl <;> assumption

theorem OrPath.order {C : Circuit} {u v : ℕ} (p : OrPath C n u v)
    (shape : BinaryBack n C) : u ≤ v := by
  induction p with
  | here => exact le_rfl
  | step hg _ hu _ ih => exact (readsEarlier shape hg hu).le.trans ih

theorem OrPath.implies {C : Circuit} {u v : ℕ} (p : OrPath C n u v)
    (shape : BinaryBack n C) (x : Fin n → Bool) :
    value C x u = true → value C x v = true := by
  induction p with
  | here => exact id
  | step hg hop hu _ ih =>
    intro hx
    apply ih
    rw [gateValue x hg (fun _ hin => readsEarlier shape hg hin), hop, GateOp.eval]
    exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨_, hu, hx⟩, rfl⟩

private theorem OrPath.appendReader {C : Circuit} {u v j : ℕ} {g : Gate}
    (p : OrPath C n u v) (hg : C.gates[j]? = some g) (hop : g.op = .or) (hv : v ∈ g.inputs) :
    OrPath C n u (n + j) := by
  induction p with
  | here => exact .step hg hop hv (.here _)
  | step hh hhop hu _ ih => exact .step hh hhop hu (ih hv)

private theorem ActivePath.order {C : Circuit} {x : Fin n → Bool} {u v : ℕ}
    (p : ActivePath C x u v) (shape : BinaryBack n C) : u ≤ v := by
  induction p with
  | here => exact le_rfl
  | step _ hg hu _ ih => exact ih.trans (readsEarlier shape hg hu).le

private theorem ActivePath.afterLastAnd {C : Circuit} {r s : Fin n} {u v : ℕ}
    (p : ActivePath C (pair r s) u v) (shape : BinaryBack n C)
    (only : ∀ j, u < n + j → ¬ ActiveAnd C r s j) : OrPath C n u v := by
  induction p with
  | here => exact .here _
  | step hp hg hw hval ih =>
    have hl := lt_of_le_of_lt (hp.order shape) (readsEarlier shape hg hw)
    have hop := (shape _ _ hg).1
    rcases hop with hand | hor
    · exact (only _ hl ⟨_, hg, hand, hval⟩).elim
    · exact ih.appendReader hg hor hw

private theorem ActivePath.endsTrue {C : Circuit} {x : Fin n → Bool} {u v : ℕ}
    (p : ActivePath C x u v) (start : value C x u = true) : value C x v = true := by
  cases p with
  | here => exact start
  | step _ _ _ hval => exact hval

private theorem ActivePath.afterLastPairAnd {C : Circuit} {r s : Fin n} {u v : ℕ}
    (p : ActivePath C (pair r s) u v) (shape : BinaryBack n C)
    (start : value C (pair r s) u = true)
    (only : ∀ j, u < n + j → ¬ PairAnd C r s j) (finish : PairOnly C r s v) :
    OrPath C n u v := by
  induction p with
  | here => exact .here _
  | @step w j g hp hg hw _ ih =>
    have hl := lt_of_le_of_lt (hp.order shape) (readsEarlier shape hg hw)
    obtain ⟨hop, a, b, hab, _, ha, hb⟩ := shape _ _ hg
    rcases hop with hand | hor
    · exact (only _ hl ⟨_, hg, hand, finish⟩).elim
    · have hr := Bool.or_eq_false_iff.mp ((orValue (single r) hg hab ha hb hor).symm.trans finish.2.1)
      have hs := Bool.or_eq_false_iff.mp ((orValue (single s) hg hab ha hb hor).symm.trans finish.2.2)
      have prev : PairOnly C r s w := by
        have live := hp.endsTrue start
        simp [hab] at hw
        rcases hw with rfl | rfl
        · exact ⟨live, hr.1, hs.1⟩
        · exact ⟨live, hr.2, hs.2⟩
      exact (ih prev).appendReader hg hor hw

private theorem sharedBefore {C : Circuit} {r s : Fin n} {root join : ℕ}
    (shape : BinaryBack n C)
    (only : ∀ j, PairAnd C r s j → j ≠ join → j = root)
    (u : ℕ) (hu : u < n + join) (hp : PairOnly C r s u) :
    OrPath C n (n + root) u := by
  induction u using Nat.strong_induction_on with
  | ind u ih =>
    have hge : n ≤ u := by
      by_contra! h
      exact noPairOnlyInput h hp
    obtain ⟨j, g, a, b, rfl, hg, hop, hab, _, ha, hb⟩ :=
      gateFor shape hge (validOfTrue hp.1)
    rcases hop with hop | hop
    · have hj := only j ⟨g, hg, hop, hp⟩ (by omega)
      rw [hj]
      exact .here _
    · have hr := Bool.or_eq_false_iff.mp ((orValue (single r) hg hab ha hb hop).symm.trans hp.2.1)
      have hs := Bool.or_eq_false_iff.mp ((orValue (single s) hg hab ha hb hop).symm.trans hp.2.2)
      rcases Bool.or_eq_true_iff.mp ((orValue (pair r s) hg hab ha hb hop).symm.trans hp.1) with hp | hp
      · exact (ih a ha (by omega) ⟨hp, hr.1, hs.1⟩).appendReader hg hop (by simp [hab])
      · exact (ih b hb (by omega) ⟨hp, hr.2, hs.2⟩).appendReader hg hop (by simp [hab])

/-- If both endpoints are repeated and the pair activates only two ANDs, the later merge
has two operands that are false on both singletons and that both contain the first cross term. -/
theorem three_active_ands_or_shared_source {C : Circuit} {r s : Fin n} {d e : ℕ → ℕ}
    (shape : BinaryBack n C) (hr : ReadCertificate C r s d) (hs : ReadCertificate C s r e)
    (hw : PairOnly C r s C.output) (hd : 2 ≤ d C.output) (he : 2 ≤ e C.output) :
    (∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ActiveAnd C r s i ∧ ActiveAnd C r s j ∧ ActiveAnd C r s k) ∨
    ∃ i j g a b, i < j ∧ Cross C r s i ∧ C.gates[j]? = some g ∧ g.op = .and ∧
      g.inputs = [a,b] ∧ PairOnly C r s a ∧ PairOnly C r s b ∧
      OrPath C n (n + i) a ∧ OrPath C n (n + i) b ∧ OrPath C n (n + j) C.output := by
  classical
  obtain ⟨i, hi⟩ := cross_of_pairOnly shape hw
  obtain ⟨j, hj, hjpath⟩ := overlap_of_certificate shape hr hw.1 hd
  have hrev : value C (pair s r) C.output = true := by rw [← pairComm r s]; exact hw.1
  obtain ⟨k, hk, _⟩ := overlap_of_certificate shape hs hrev he
  have ai := crossActive hi
  have aj := mergeActive shape hj
  have ak := mergeActive shape hk
  rw [ActiveAnd, ← pairComm r s] at ak
  have i_ne_j := cross_ne_merge hi hj
  have i_ne_k := cross_ne_merge (crossComm hi) hk
  by_cases three : ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ActiveAnd C r s i ∧ ActiveAnd C r s j ∧ ActiveAnd C r s k
  · exact Or.inl three
  right
  have same : j = k := by
    by_contra! ne
    exact three ⟨i, j, k, i_ne_j, i_ne_k, ne, ai, aj, ak⟩
  subst k
  have only (k : ℕ) (h : ActiveAnd C r s k) (hn : k ≠ j) : k = i := by
    by_contra! hne
    exact three ⟨i, j, k, i_ne_j, hne.symm, hn.symm, ai, aj, h⟩
  obtain ⟨g, a, b, hg, hop, hab, hain, hbin, haoff, hboff⟩ := hj
  obtain ⟨f, u, v, hf, _, huv, _, _, huoff, hvoff⟩ := hk
  have efg := Option.some.inj (hg.symm.trans hf)
  subst f
  obtain ⟨haeq, heq⟩ := List.cons.inj (hab.symm.trans huv)
  have hveq := (List.cons.inj heq).1
  subst u
  subst v
  obtain ⟨_, c, d, hcd, _, hc, hh⟩ := shape j g hg
  obtain ⟨hceq, heq'⟩ := List.cons.inj (hcd.symm.trans hab)
  have hdeq := (List.cons.inj heq').1
  subst c
  subst d
  have ha : PairOnly C r s a := ⟨hain, huoff, haoff⟩
  have hb : PairOnly C r s b := ⟨hbin, hvoff, hboff⟩
  have onlyPair (k : ℕ) (h : PairAnd C r s k) (hn : k ≠ j) : k = i := by
    obtain ⟨g, hg, hop, hp⟩ := h
    exact only k ⟨g, hg, hop, hp.1⟩ hn
  have pa := sharedBefore shape onlyPair a hc ha
  have pb := sharedBefore shape onlyPair b hh hb
  have earlier := lt_of_le_of_lt (pa.order shape) hc
  have hout : OrPath C n (n + j) C.output := hjpath.afterLastAnd shape (by
    intro k hka hak
    have hki := only k hak (by omega)
    omega)
  exact ⟨i, j, g, a, b, by omega, hi, hg, hop, hab, ha, hb, pa, pb, hout⟩

theorem OrPath.forkOrCompare {C : Circuit} {u a b : ℕ}
    (pa : OrPath C n u a) (pb : OrPath C n u b) :
    OrPath C n a b ∨ OrPath C n b a ∨
      ∃ (w j k : ℕ) (g h : Gate), j ≠ k ∧ C.gates[j]? = some g ∧ C.gates[k]? = some h ∧
        g.op = .or ∧ h.op = .or ∧ w ∈ g.inputs ∧ w ∈ h.inputs ∧
        OrPath C n w a ∧ OrPath C n w b := by
  induction pa generalizing b with
  | here => exact Or.inl pb
  | @step u j a g hg hop hu pt ih =>
    cases pb with
    | here => exact Or.inr (Or.inl (.step hg hop hu pt))
    | @step _ k b h hh hhop hv qt =>
      by_cases same : j = k
      · subst k
        exact ih qt
      · exact Or.inr (Or.inr ⟨u, j, k, g, h, same, hg, hh, hop, hhop, hu, hv,
          .step hg hop hu pt, .step hh hhop hv qt⟩)

open PEqualNP.MetaComplexity PEqualNP.CircuitMoves PEqualNP.Outside.L_meta_18546.Er

private theorem monoOfShape {C : Circuit} (shape : BinaryBack n C) : Monotone2 C := by
  intro g hg
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hg
  obtain ⟨hop, a, b, hab, _⟩ := shape j g hj
  exact ⟨by simpa using hop, by simp [hab]⟩

private theorem relateErasure {C : Circuit} (x : Fin n → Bool) {j p : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hp : p < n + j)
    (rel : Bool → Bool → Prop) (refl : ∀ b, rel b b)
    (preserved : ∀ g ∈ C.gates, Hop rel g)
    (localRel : rel (value C x (n + j)) (value C x p)) :
    rel (C.eval (List.ofFn x)) ((eraseGate n C j p).eval (List.ofFn x)) := by
  obtain ⟨hj, hjg⟩ := List.getElem?_eq_some_iff.mp hg
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hpre : pre.length = j := by simp [pre, Nat.min_eq_left hj.le]
  have split : C.gates = pre ++ g :: post := by
    dsimp [pre, post]
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, hjg]
  have hlen : (run pre (List.ofFn x)).length = n + j := by rw [run_len, List.length_ofFn, hpre]
  have evalGate : value C x (n + j) = gv g (run pre (List.ofFn x)) := by
    rw [value, wires_run, split, run_app, run_cons, run_low _ _ _ (by simp [hlen])]
    simp [hlen]
  have low : value C x p = (run pre (List.ofFn x)).getD p false :=
    wire_low n C pre post g split _ (by simp) _ (by rwa [hpre])
  rw [evalGate, low] at localRel
  have h := erase_rel rel refl n C p pre post g split (by rwa [hpre])
    (List.ofFn x) (by simp) (fun q hq => preserved q (List.mem_of_mem_drop hq)) localRel
  simpa only [hpre] using h

private theorem eraseWhenAlias {C : Circuit} (x : Fin n → Bool) {j p : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hp : p < n + j)
    (same : value C x (n + j) = value C x p) :
    (eraseGate n C j p).eval (List.ofFn x) = C.eval (List.ofFn x) :=
  (relateErasure x hg hp Eq (fun _ => rfl) (fun g _ => hop_eq g) same).symm

private theorem eraseSize {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (p n : ℕ) :
    (eraseGate n C j p).size + 1 = C.size := by
  simp [Circuit.size, eraseGate, hj, Nat.min_eq_left hj.le]
  omega

private theorem eraseMono {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (p n : ℕ)
    (hm : Monotone2 C) : Monotone2 (eraseGate n C j p) := by
  simp only [eraseGate, ite_eq_left hj]
  intro g hg
  simp only [List.mem_append, List.mem_map] at hg
  rcases hg with hpre | ⟨g', hpost, rfl⟩
  · exact hm _ (List.mem_of_mem_take hpre)
  · simpa using hm g' (List.mem_of_mem_drop hpost)

private theorem eraseBelow {C : Circuit} {j : ℕ}
    (hj : j < C.gates.length) (p : ℕ) (x : Fin n → Bool) (w : ℕ) (hw : w < n + j) :
    value (eraseGate n C j p) x w = value C x w := by
  change ((eraseGate n C j p).gates.foldl extend (List.ofFn x)).getD w false =
    (C.gates.foldl extend (List.ofFn x)).getD w false
  conv_rhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
  simp only [eraseGate, ite_eq_left hj, List.foldl_append]
  have h : w < ((C.gates.take j).foldl extend (List.ofFn x)).length := by
    simpa [foldLength, Nat.min_eq_left hj.le] using hw
  rw [foldKeeps _ _ _ h, foldKeeps _ _ _ h]

private theorem eraseEarlierGate {C : Circuit} {j k : ℕ}
    (hj : j < C.gates.length) (hk : k < j) (p n : ℕ) :
    (eraseGate n C j p).gates[k]? = C.gates[k]? := by
  have ht : k < (C.gates.take j).length := by simpa [Nat.min_eq_left hj.le] using hk
  simp [eraseGate, hj, List.getElem?_append_left ht, hk]

private theorem siblingOfReader {C : Circuit} (shape : BinaryBack n C) {j w : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hr : w ∈ g.inputs) :
    ∃ p < n + j, g.inputs = [w, p] ∨ g.inputs = [p, w] := by
  obtain ⟨_, a, b, hab, _, ha, hb⟩ := shape j g hg
  rw [hab] at hr
  simp at hr
  rcases hr with rfl | rfl
  · exact ⟨_, hb, Or.inl hab⟩
  · exact ⟨_, ha, Or.inr hab⟩

private theorem orAliasWhenFalse {C : Circuit} (x : Fin n → Bool) {j p w : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) (hop : g.op = .or) (hp : p < n + j) (hw : w < n + j)
    (order : g.inputs = [w, p] ∨ g.inputs = [p, w]) (hfalse : value C x w = false) :
    value C x (n + j) = value C x p := by
  rcases order with h | h
  · simp [orValue x hg h hw hp hop, hfalse]
  · simp [orValue x hg h hp hw hop, hfalse]

private def finalOr (n : ℕ) (C : Circuit) (w : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, w]⟩], n + C.size⟩

private theorem finalOrValue (C : Circuit) (w : ℕ) (x : Fin n → Bool) :
    (finalOr n C w).eval (List.ofFn x) = (C.eval (List.ofFn x) || value C x w) := by
  let ws := C.gates.foldl extend (List.ofFn x)
  have hlen : ws.length = n + C.size := by simp [ws, foldLength, Circuit.size]
  change ((C.gates ++ [(⟨.or, [C.output, w]⟩ : Gate)]).foldl extend (List.ofFn x)).getD
    (n + C.size) false = _
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ← hlen]
  change (extend ws _).getD ws.length false =
    (ws.getD C.output false || ws.getD w false)
  simp [extend, List.getD_eq_getElem?_getD, GateOp.eval]

private theorem finalOrMono {C : Circuit} (hm : Monotone2 C) (w n : ℕ) :
    Monotone2 (finalOr n C w) := by
  intro g hg
  simp only [finalOr, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact hm _ hg
  · simp

private theorem shrinkFork {C : Circuit} (shape : BinaryBack n C)
    {j k w : ℕ} {g h : Gate}
    (order : j < k) (hg : C.gates[j]? = some g) (hh : C.gates[k]? = some h)
    (og : g.op = .or) (oh : h.op = .or) (wg : w ∈ g.inputs) (wh : w ∈ h.inputs)
    (below : ∀ x : Fin n → Bool, value C x w = true → C.eval (List.ofFn x) = true) :
    ∃ D, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨p, hp, pg⟩ := siblingOfReader shape hg wg
  obtain ⟨q, hq, qh⟩ := siblingOfReader shape hh wh
  have hkj := (List.getElem?_eq_some_iff.mp hh).1
  have hwj := readsEarlier shape hg wg
  have hwk := readsEarlier shape hh wh
  let A := eraseGate n C k q
  have hgA : A.gates[j]? = some g := (eraseEarlierGate hkj order q n).trans hg
  have hjA := (List.getElem?_eq_some_iff.mp hgA).1
  let B := eraseGate n A j p
  have hA : A.size + 1 = C.size := eraseSize hkj q n
  have hB : B.size + 1 = A.size := eraseSize hjA p n
  have monoA : Monotone2 A := eraseMono hkj q n (monoOfShape shape)
  have monoB : Monotone2 B := eraseMono hjA p n monoA
  refine ⟨finalOr n B w, finalOrMono monoB w n, ?_, ?_⟩
  · simp only [finalOr, Circuit.size, List.length_append, List.length_singleton]
    change B.size + 1 < C.size
    omega
  · intro x
    have vA : value A x w = value C x w := eraseBelow hkj q x w hwk
    have vB : value B x w = value A x w := eraseBelow hjA p x w hwj
    rw [finalOrValue, vB, vA]
    cases e : value C x w
    · have eA : A.eval (List.ofFn x) = C.eval (List.ofFn x) :=
        eraseWhenAlias x hh hq (orAliasWhenFalse x hh oh hq hwk qh e)
      have eB : B.eval (List.ofFn x) = A.eval (List.ofFn x) :=
        eraseWhenAlias x hgA hp (orAliasWhenFalse x hgA og hp hwj pg (vA.trans e))
      simp [eB, eA]
    · simp [below x e]

private theorem shrinkAndReader {C : Circuit} (shape : BinaryBack n C)
    {w j : ℕ} {g : Gate} (hg : C.gates[j]? = some g) (hop : g.op = .and) (hr : w ∈ g.inputs)
    (below : ∀ x : Fin n → Bool, value C x w = true → C.eval (List.ofFn x) = true) :
    ∃ D, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  have hw := readsEarlier shape hg hr
  refine ⟨eraseGate n C j w, eraseMono hj w n (monoOfShape shape), ?_, ?_⟩
  · have h := eraseSize hj w n
    omega
  · intro x
    have implication : value C x (n+j) = true → value C x w = true := by
      intro h
      rw [gateValue x hg (fun _ hm => readsEarlier shape hg hm), hop, GateOp.eval] at h
      exact List.all_eq_true.mp h _ (List.mem_map_of_mem hr)
    cases e : C.eval (List.ofFn x)
    · have hwfalse : value C x w = false := by
        cases h : value C x w
        · rfl
        · have h' := below x h
          rw [e] at h'
          contradiction
      have hgfalse : value C x (n+j) = false := by
        cases h : value C x (n+j)
        · rfl
        · rw [hwfalse] at implication
          have := implication h
          contradiction
      exact (eraseWhenAlias x hg hw (hgfalse.trans hwfalse.symm)).trans e
    · have hp (q : Gate) (hq : q ∈ C.gates) :
          Hop (fun a b => a = true → b = true) q := by
        obtain ⟨k, hk⟩ := List.getElem?_of_mem hq
        exact hop_le q (shape k q hk).1
      exact relateErasure x hg hw (fun a b => a = true → b = true)
        (fun _ h => h) hp implication e

/-- An AND never reads a wire implying the output of a minimum monotone circuit. -/
theorem no_and_reader_of_below_output {C : Circuit} (shape : BinaryBack n C) {w j : ℕ} {g : Gate}
    (minimal : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (below : ∀ x : Fin n → Bool, value C x w = true → C.eval (List.ofFn x) = true)
    (hg : C.gates[j]? = some g) (hr : w ∈ g.inputs) : g.op ≠ .and := by
  intro hand
  obtain ⟨D, hm, hsz, hval⟩ := shrinkAndReader shape hg hand hr below
  exact (not_lt_of_ge (minimal D hm hval) hsz)

/-- Every wire implying the output of a minimum monotone circuit has at most one reader. -/
theorem one_reader_of_below_output {C : Circuit} (shape : BinaryBack n C) (w : ℕ)
    (minimal : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (below : ∀ x : Fin n → Bool, value C x w = true → C.eval (List.ofFn x) = true) :
    ((Finset.range C.gates.length).filter fun j =>
      w ∈ (NestedCover.gateAt C j).inputs).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro j hj k hk
  obtain ⟨hj, hjw⟩ := Finset.mem_filter.mp hj
  obtain ⟨hk, hkw⟩ := Finset.mem_filter.mp hk
  have hj' := Finset.mem_range.mp hj
  have hk' := Finset.mem_range.mp hk
  have getJ : C.gates[j]? = some (NestedCover.gateAt C j) := by
    simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, hj']
  have getK : C.gates[k]? = some (NestedCover.gateAt C k) := by
    simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, hk']
  have oj := ((shape j _ getJ).1).resolve_left (no_and_reader_of_below_output shape minimal below getJ hjw)
  have ok := ((shape k _ getK).1).resolve_left (no_and_reader_of_below_output shape minimal below getK hkw)
  by_contra ne
  rcases lt_or_gt_of_ne ne with before | before
  · obtain ⟨D, hm, hsz, hval⟩ := shrinkFork shape before getJ getK oj ok hjw hkw below
    exact (not_lt_of_ge (minimal D hm hval) hsz)
  · obtain ⟨D, hm, hsz, hval⟩ := shrinkFork shape before getK getJ ok oj hkw hjw below
    exact (not_lt_of_ge (minimal D hm hval) hsz)

private theorem shrinkShared {C : Circuit} (shape : BinaryBack n C)
    {i j a b : ℕ} {g : Gate} (hg : C.gates[j]? = some g) (hop : g.op = .and)
    (hab : g.inputs = [a, b])
    (pa : OrPath C n (n + i) a) (pb : OrPath C n (n + i) b)
    (hout : OrPath C n (n + j) C.output) :
    ∃ D, Monotone2 D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have ha := readsEarlier shape hg (show a ∈ g.inputs by simp [hab])
  have hb := readsEarlier shape hg (show b ∈ g.inputs by simp [hab])
  have hj := (List.getElem?_eq_some_iff.mp hg).1
  rcases pa.forkOrCompare pb with ab | ba | ⟨w, k, l, u, v, hne, hu, hv, ou, ov, wu, wv, wA, wB⟩
  · refine ⟨eraseGate n C j a, eraseMono hj a n (monoOfShape shape), ?_, ?_⟩
    · have hz := eraseSize hj a n
      omega
    · intro x
      apply eraseWhenAlias x hg ha
      rw [andValue x hg hab ha hb hop]
      cases e : value C x a
      · rfl
      · simp [ab.implies shape x e]
  · refine ⟨eraseGate n C j b, eraseMono hj b n (monoOfShape shape), ?_, ?_⟩
    · have hz := eraseSize hj b n
      omega
    · intro x
      apply eraseWhenAlias x hg hb
      rw [andValue x hg hab ha hb hop]
      cases e : value C x b
      · simp
      · simp [ba.implies shape x e]
  · have below (x : Fin n → Bool) (hx : value C x w = true) : C.eval (List.ofFn x) = true := by
      apply hout.implies shape x
      simp [andValue x hg hab ha hb hop, wA.implies shape x hx, wB.implies shape x hx]
    rcases lt_or_gt_of_ne hne with h | h
    · exact shrinkFork shape h hu hv ou ov wu wv below
    · exact shrinkFork shape h hv hu ov ou wv wu below

/-- In a least monotone circuit, a certificate of double re-reading needs at least three
AND gates that evaluate to true on the edge. -/
theorem three_active_ands_of_minimal {C : Circuit} {r s : Fin n} {d e : ℕ → ℕ}
    (shape : BinaryBack n C) (hr : ReadCertificate C r s d) (hs : ReadCertificate C s r e)
    (hw : PairOnly C r s C.output) (hd : 2 ≤ d C.output) (he : 2 ≤ e C.output)
    (minimal : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ActiveAnd C r s i ∧ ActiveAnd C r s j ∧ ActiveAnd C r s k := by
  rcases three_active_ands_or_shared_source shape hr hs hw hd he with
    h | ⟨i, j, g, a, b, _, _, hg, hop, hab, _, _, pa, pb, hout⟩
  · exact h
  · obtain ⟨D, hD, hsz, hval⟩ := shrinkShared shape hg hop hab pa pb hout
    exact (not_lt_of_ge (minimal D hD hval) hsz).elim

/-- A merge that repeats both endpoints requires three pair-only ANDs in a least circuit,
even if an arbitrary number of other ANDs turn on at one of the endpoint singletons. -/
theorem three_pair_ands_of_common_merge {C : Circuit} {r s : Fin n} {j : ℕ}
    (shape : BinaryBack n C) (mr : Merge C r s j) (ms : Merge C s r j)
    (path : ActivePath C (pair r s) (n + j) C.output)
    (hout : PairOnly C r s C.output)
    (minimal : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      PairAnd C r s i ∧ PairAnd C r s j ∧ PairAnd C r s k := by
  classical
  by_contra noThree
  obtain ⟨i, hi⟩ := cross_of_pairOnly shape hout
  have ine := cross_ne_merge hi mr
  have hpi : PairAnd C r s i := by
    obtain ⟨g, _, _, hg, hop, _, hp, _⟩ := hi
    exact ⟨g, hg, hop, hp⟩
  obtain ⟨g, a, b, hg, hop, hab, haon, hbon, has, hbs⟩ := mr
  obtain ⟨h, a', b', hh, _, hab', _, _, har', hbr'⟩ := ms
  have he := Option.some.inj (hg.symm.trans hh)
  subst h
  obtain ⟨ea, eb⟩ := List.cons.inj (hab.symm.trans hab')
  have eb' := (List.cons.inj eb).1
  subst a'
  subst b'
  have ha : PairOnly C r s a := ⟨haon, har', has⟩
  have hb : PairOnly C r s b := ⟨hbon, hbr', hbs⟩
  have hla := readsEarlier shape hg (show a ∈ g.inputs by simp [hab])
  have hlb := readsEarlier shape hg (show b ∈ g.inputs by simp [hab])
  have hpj : PairOnly C r s (n + j) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [andValue (pair r s) hg hab hla hlb hop, haon, hbon]
    · simp [andValue (single r) hg hab hla hlb hop, har']
    · simp [andValue (single s) hg hab hla hlb hop, has]
  have only (k : ℕ) (h : PairAnd C r s k) (hn : k ≠ j) : k = i := by
    by_contra! ne
    exact noThree ⟨i, j, k, ine, ne.symm, hn.symm, hpi, ⟨g, hg, hop, hpj⟩, h⟩
  have pa := sharedBefore shape only a hla ha
  have pb := sharedBefore shape only b hlb hb
  have root_lt := lt_of_le_of_lt (pa.order shape) hla
  have last : OrPath C n (n + j) C.output := path.afterLastPairAnd shape hpj.1 (by
    intro k hk h
    have e := only k h (by omega)
    omega) hout
  obtain ⟨D, hm, hsz, hval⟩ := shrinkShared shape hg hop hab pa pb last
  exact (not_lt_of_ge (minimal D hm hval) hsz)

private theorem minimalFano (C : Circuit) (hsize : C.size ≤ 27)
    (compute : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      PEqualNP.Outside.L_meta_17589_aux.FanoE x) :
    ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size := by
  intro D hm hval
  have hlo := PEqualNP.Outside.L_meta_17589_aux.fano27 D hm (fun x => by rw [hval, compute])
  omega

theorem fano_sound_wire_readers (C : Circuit) (hsize : C.size ≤ 27)
    (shape : BinaryBack 14 C)
    (compute : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      PEqualNP.Outside.L_meta_17589_aux.FanoE x)
    (w : ℕ) (below : ∀ x : Fin 14 → Bool, value C x w = true →
      PEqualNP.Outside.L_meta_17589_aux.FanoE x) :
    (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → w ∈ g.inputs → g.op ≠ .and) ∧
    ((Finset.range C.gates.length).filter fun j =>
      w ∈ (NestedCover.gateAt C j).inputs).card ≤ 1 := by
  have b (x : Fin 14 → Bool) (h : value C x w = true) :
      C.eval (List.ofFn x) = true := (compute x).mpr (below x h)
  exact ⟨fun _ _ hg hw => no_and_reader_of_below_output shape (minimalFano C hsize compute) b hg hw,
    one_reader_of_below_output shape w (minimalFano C hsize compute) b⟩

theorem fano_double_read_active_ands (C : Circuit) (hsize : C.size ≤ 27)
    (shape : BinaryBack 14 C)
    (compute : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      PEqualNP.Outside.L_meta_17589_aux.FanoE x)
    (weights : ∀ s : Bool, ∃ d : ℕ → ℕ,
      ReadCertificate C (if s then (7 : Fin 14) else 0) (if s then (0 : Fin 14) else 7) d ∧
      2 ≤ d C.output) :
    ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ ActiveAnd C (0 : Fin 14) 7 i ∧
      ActiveAnd C (0 : Fin 14) 7 j ∧ ActiveAnd C (0 : Fin 14) 7 k := by
  obtain ⟨d, hd, hd'⟩ := weights false
  obtain ⟨e, he, he'⟩ := weights true
  have hw : PairOnly C (0 : Fin 14) 7 C.output := by
    refine ⟨(compute _).mpr (by unfold PEqualNP.Outside.L_meta_17589_aux.FanoE; decide), ?_, ?_⟩
    · cases h : value C (single (0 : Fin 14)) C.output
      · rfl
      · exact False.elim ((by unfold PEqualNP.Outside.L_meta_17589_aux.FanoE; decide :
          ¬ PEqualNP.Outside.L_meta_17589_aux.FanoE (single (0 : Fin 14)))
          ((compute _).mp h))
    · cases h : value C (single (7 : Fin 14)) C.output
      · rfl
      · exact False.elim ((by unfold PEqualNP.Outside.L_meta_17589_aux.FanoE; decide :
          ¬ PEqualNP.Outside.L_meta_17589_aux.FanoE (single (7 : Fin 14)))
          ((compute _).mp h))
  exact three_active_ands_of_minimal shape hd he hw hd' he' (minimalFano C hsize compute)

end PEqualNP.Outside.DoubleReadTrace

#print axioms PEqualNP.Outside.DoubleReadTrace.overlap_of_certificate
#print axioms PEqualNP.Outside.DoubleReadTrace.three_active_ands_or_shared_source
#print axioms PEqualNP.Outside.DoubleReadTrace.fano_double_read_active_ands
#print axioms PEqualNP.Outside.DoubleReadTrace.three_pair_ands_of_common_merge
#print axioms PEqualNP.Outside.DoubleReadTrace.one_reader_of_below_output
#print axioms PEqualNP.Outside.DoubleReadTrace.fano_sound_wire_readers
