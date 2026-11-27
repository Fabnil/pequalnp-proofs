import PEqualNP.Defs
import PEqualNP.MetaComplexity.L154

namespace PlaneCompletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def edges : List (ℕ × ℕ) :=
  [(0, 16), (0, 22), (0, 24), (1, 13), (1, 17), (1, 23), (2, 13), (2, 14),
   (2, 18), (2, 24), (3, 14), (3, 15), (3, 19), (4, 13), (4, 15), (4, 16),
   (4, 20), (5, 14), (5, 16), (5, 17), (5, 21), (6, 15), (6, 17), (6, 18),
   (6, 22), (7, 16), (7, 18), (7, 19), (7, 23), (8, 17), (8, 19), (8, 20),
   (8, 24), (9, 18), (9, 20), (9, 21), (10, 13), (10, 19), (10, 21), (10, 22),
   (11, 14), (11, 20), (11, 22), (11, 23), (12, 15), (12, 21), (12, 23), (12, 24)]

def deleted (x : Fin 25 → Bool) : Prop :=
  ∃ a b : Fin 25, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true

def incidence (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

instance (p l : Fin 13) : Decidable (incidence p l) := by unfold incidence; infer_instance

def plane (x : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, incidence p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true

def rename (w : ℕ) : ℕ :=
  ([12, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 18, 19,
    20, 21, 22, 23, 24] : List ℕ).getD w (w + 5)

private theorem renameInput : ∀ w : Fin 25, rename w.val < 26 := by decide +kernel

private theorem renameGateWire {w : ℕ} (hw : 25 ≤ w) : rename w = w + 5 :=
  List.getD_eq_default _ _ hw

def embed (w : Fin 25) : Fin 26 := ⟨rename w.val, renameInput w⟩

def star (x : Fin 26 → Bool) : Bool := x 25 && ((x 12 || x 0) || (x 2 || x 8))

private def oldPoint (p : Fin 13) : Fin 25 := Fin.ofNat 25 ((p.val + 1) % 13)
private def oldLine (l : Fin 13) : Fin 25 := Fin.ofNat 25 (13 + l.val)

private theorem pointEmbed : ∀ p, embed (oldPoint p) = Fin.castAdd 13 p := by decide +kernel
private theorem lineEmbed : ∀ l : Fin 13, l ≠ 12 → embed (oldLine l) = Fin.natAdd 13 l := by
  decide +kernel

private theorem originalIncidences : ∀ p l : Fin 13, incidence p l → l ≠ 12 →
    ((oldPoint p).val, (oldLine l).val) ∈ edges := by decide +kernel

private theorem embeddedIncidences : ∀ a b : Fin 25, (a.val, b.val) ∈ edges →
    ∃ p l : Fin 13, incidence p l ∧ embed a = Fin.castAdd 13 p ∧ embed b = Fin.natAdd 13 l := by
  decide +kernel

private theorem lastLine : ∀ p : Fin 13, incidence p 12 ↔ p = 12 ∨ p = 0 ∨ p = 2 ∨ p = 8 := by
  decide +kernel

theorem planeSplit (x : Fin 26 → Bool) : plane x ↔ deleted (fun w => x (embed w)) ∨ star x = true := by
  constructor
  · rintro ⟨p, l, inc, hp, hl⟩
    by_cases h : l = 12
    · subst l
      apply Or.inr
      have h25 : x 25 = true := hl
      rcases (lastLine p).mp inc with rfl | rfl | rfl | rfl
      · have hp' : x 12 = true := hp
        simp [star, h25, hp']
      · have hp' : x 0 = true := hp
        simp [star, h25, hp']
      · have hp' : x 2 = true := hp
        simp [star, h25, hp']
      · have hp' : x 8 = true := hp
        simp [star, h25, hp']
    · exact Or.inl ⟨oldPoint p, oldLine l, originalIncidences p l inc h,
        by simpa only [pointEmbed] using hp, by simpa only [lineEmbed l h] using hl⟩
  · rintro (⟨a, b, hab, ha, hb⟩ | h)
    · obtain ⟨p, l, inc, pa, lb⟩ := embeddedIncidences a b hab
      exact ⟨p, l, inc, pa ▸ ha, lb ▸ hb⟩
    · simp only [star, Bool.and_eq_true, Bool.or_eq_true] at h
      rcases h with ⟨hl, (hp | hp) | hp | hp⟩
      · exact ⟨12, 12, by decide, hp, hl⟩
      · exact ⟨0, 12, by decide, hp, hl⟩
      · exact ⟨2, 12, by decide, hp, hl⟩
      · exact ⟨8, 12, by decide, hp, hl⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem stepLength (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

private theorem stepOld (w : List Bool) (g : Gate) {i : ℕ} (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := List.getD_append _ _ _ _ hi

private theorem stepNew (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp [step, List.getD_eq_getElem?_getD]

private theorem runLength (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, stepLength, List.length_cons]; omega

private theorem runOld (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons, ih _ (by rw [stepLength]; omega), stepOld _ _ hi]

private theorem inputAt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by simp [List.getD_eq_getElem?_getD, hi]

private def renamed (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩

private def Agree (w w' : List Bool) : Prop :=
  w'.length = w.length + 5 ∧ 25 ≤ w.length ∧ ∀ i, w'.getD (rename i) false = w.getD i false

private theorem runAgree (gs : List Gate) (w w' : List Bool) (h : Agree w w') :
    Agree (gs.foldl step w) ((gs.map renamed).foldl step w') := by
  induction gs generalizing w w' with
  | nil => exact h
  | cons g gs ih =>
    obtain ⟨hl, h25, hv⟩ := h
    refine ih _ _ ⟨by rw [stepLength, stepLength, hl], by rw [stepLength]; omega, fun i => ?_⟩
    rcases lt_trichotomy i w.length with hi | rfl | hi
    · have hi' : rename i < w'.length := by
        by_cases h : i < 25
        · exact (renameInput ⟨i, h⟩).trans_le (by omega)
        · rw [renameGateWire (by omega)]; omega
      rw [stepOld _ _ hi', stepOld _ _ hi, hv]
    · rw [renameGateWire h25, ← hl, stepNew, stepNew]
      simp only [renamed, List.map_map, Function.comp_def, hv]
    · rw [renameGateWire (by omega), List.getD_eq_default _ _ (by rw [stepLength]; omega),
        List.getD_eq_default _ _ (by rw [stepLength]; omega)]

private def starGates : List Gate :=
  [⟨.or, [12, 0]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [26, 27]⟩, ⟨.and, [25, 28]⟩]

private def starWires (x : Fin 26 → Bool) : List Bool := starGates.foldl step (List.ofFn x)

private theorem starWiresLength (x : Fin 26 → Bool) : (starWires x).length = 30 := by
  rw [starWires, runLength, List.length_ofFn]; rfl

private theorem starValue (x : Fin 26 → Bool) : (starWires x).getD 29 false = star x := by
  simp [starWires, starGates, step, GateOp.eval, star]

private theorem starAgree (x : Fin 26 → Bool) : Agree (List.ofFn fun i => x (embed i)) (starWires x) := by
  refine ⟨by rw [starWiresLength, List.length_ofFn], by rw [List.length_ofFn], fun i => ?_⟩
  by_cases h : i < 25
  · rw [starWires, runOld _ _ _ (by rw [List.length_ofFn]; exact renameInput ⟨i, h⟩),
      inputAt _ _ (renameInput ⟨i, h⟩), inputAt _ _ h]
    rfl
  · rw [renameGateWire (by omega), List.getD_eq_default _ _ (by rw [starWiresLength]; omega),
      List.getD_eq_default _ _ (by rw [List.length_ofFn]; omega)]

private def joinGate (C : Circuit) : Gate := ⟨.or, [rename C.output, 29]⟩

def complete (C : Circuit) : Circuit :=
  ⟨starGates ++ C.gates.map renamed ++ [joinGate C], C.size + 30⟩

theorem completeSize (C : Circuit) : (complete C).size = C.size + 5 := by
  simp [complete, Circuit.size, starGates]

theorem completeMonotone {C : Circuit} (h : Monotone2 C) : Monotone2 (complete C) := by
  simp only [Monotone2, complete, List.forall_mem_append, List.forall_mem_map]
  exact ⟨⟨by simp [starGates], fun g hg => by simpa [renamed] using h g hg⟩, by simp [joinGate]⟩

theorem completeEval (C : Circuit) (x : Fin 26 → Bool) :
    (complete C).eval (List.ofFn x) = (C.eval (List.ofFn fun i => x (embed i)) || star x) := by
  let w := (C.gates.map renamed).foldl step (starWires x)
  have h := (runAgree C.gates _ _ (starAgree x)).2.2 C.output
  change w.getD (rename C.output) false = C.eval (List.ofFn fun i => x (embed i)) at h
  have hn : w.length = C.size + 30 := by
    simp only [w, runLength, starWiresLength, List.length_map, Circuit.size]; omega
  have hstar : w.getD 29 false = star x := by
    change ((C.gates.map renamed).foldl step (starWires x)).getD 29 false = star x
    rw [runOld _ _ _ (by rw [starWiresLength]; decide), starValue]
  change ((starGates ++ C.gates.map renamed ++ [joinGate C]).foldl step
    (List.ofFn x)).getD (C.size + 30) false = _
  rw [List.foldl_append, List.foldl_append]
  change (step w (joinGate C)).getD (C.size + 30) false = _
  rw [← hn, stepNew]
  change GateOp.or.eval [w.getD (rename C.output) false, w.getD 29 false] = _
  have boolOr : ∀ a b : Bool, GateOp.or.eval [a, b] = (a || b) := by decide
  rw [boolOr, h, hstar]

theorem completeCorrect {C : Circuit}
    (h : ∀ x, C.eval (List.ofFn x) = true ↔ deleted x) :
    ∀ x, (complete C).eval (List.ofFn x) = true ↔ plane x := by
  intro x
  rw [completeEval, Bool.or_eq_true, h, planeSplit]

theorem planeLowerBoundImpliesDeletedLowerBound
    (lower : ∀ C : Circuit, Monotone2 C → (∀ x, C.eval (List.ofFn x) = true ↔ plane x) → 64 ≤ C.size)
    (C : Circuit) (monotone : Monotone2 C) (correct : ∀ x, C.eval (List.ofFn x) = true ↔ deleted x) :
    59 ≤ C.size := by
  have h := lower (complete C) (completeMonotone monotone) (completeCorrect correct)
  rw [completeSize] at h
  omega

def AtMostTwo {n : ℕ} (x : Fin n → Bool) : Prop :=
  ∀ a b c, x a = true → x b = true → x c = true → a = b ∨ a = c ∨ b = c

theorem pairSmall {n : ℕ} (u v : Fin n) : AtMostTwo (pairInput u v) := by
  intro a b c ha hb hc
  simp only [pairInput, decide_eq_true_eq] at ha hb hc
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;> simp [ha, hb, hc]

private def starGateAt (j : ℕ) : Gate := starGates.getD j ⟨.or, []⟩

private theorem completeGateCases (C : Circuit) (j : ℕ) (hj : j < C.gates.length + 5) :
    (j < 4 ∧ gateAt (complete C) j = starGateAt j) ∨
    (∃ k < C.gates.length, j = 4 + k ∧ gateAt (complete C) j = renamed (gateAt C k)) ∨
    (j = 4 + C.gates.length ∧ gateAt (complete C) j = joinGate C) := by
  by_cases h : j < 4
  · refine Or.inl ⟨h, ?_⟩
    simp only [gateAt, complete, starGateAt, List.append_assoc]
    rw [List.getD_append _ _ _ _ (by simpa [starGates] using h)]
  · let k := j - 4
    have hjk : j = 4 + k := by dsimp [k]; omega
    have hget : gateAt (complete C) j = (C.gates.map renamed ++ [joinGate C]).getD k ⟨.or, []⟩ := by
      simp only [gateAt, complete, List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by simp [starGates]; omega)]
      rfl
    by_cases hk : k < C.gates.length
    · refine Or.inr (Or.inl ⟨k, hk, hjk, ?_⟩)
      rw [hget, List.getD_append _ _ _ _ (by simpa using hk)]
      simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    · have heq : k = C.gates.length := by omega
      refine Or.inr (Or.inr ⟨hjk.trans (congrArg (4 + ·) heq), ?_⟩)
      rw [hget, List.getD_append_right _ _ _ _ (by simp [heq])]
      simp [heq]

private theorem oldOutputBound {C : Circuit}
    (h : ∀ x, AtMostTwo x → (C.eval (List.ofFn x) = true ↔ deleted x)) :
    C.output < 25 + C.gates.length := by
  let x : Fin 25 → Bool := pairInput 0 16
  have hx : deleted x := ⟨0, 16, by decide, by decide, by decide⟩
  have ht := (h x (pairSmall 0 16)).mpr hx
  by_contra! hn
  change (C.gates.foldl step (List.ofFn x)).getD C.output false = true at ht
  rw [List.getD_eq_default _ _ (by rw [runLength, List.length_ofFn]; exact hn)] at ht
  cases ht

private theorem renameBelow {w k : ℕ} (h : w < 25 + k) : rename w < 26 + (4 + k) := by
  by_cases small : w < 25
  · exact (renameInput ⟨w, small⟩).trans_le (by omega)
  · rw [renameGateWire (by omega)]; omega

private theorem starReadsBack : ∀ j : Fin 4,
    (starGateAt j.val).inputs.all (fun w => decide (w < 26 + j.val)) = true := by decide

theorem completeAO2 {C : Circuit} (h : IsAO2 25 C)
    (correct : ∀ x, AtMostTwo x → (C.eval (List.ofFn x) = true ↔ deleted x)) : IsAO2 26 (complete C) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [AndOrOnly, complete, List.forall_mem_append, List.forall_mem_map]
    exact ⟨⟨by simp [starGates], fun g hg => by simpa [renamed] using h.1 g hg⟩, by simp [joinGate]⟩
  · intro j hj w hw
    have hj' : j < C.gates.length + 5 := by
      change j < (complete C).size at hj
      rw [completeSize] at hj
      exact hj
    rcases completeGateCases C j hj' with ⟨hj4, atStar⟩ | ⟨k, hk, rfl, atOld⟩ | ⟨rfl, atJoin⟩
    · rw [atStar] at hw
      exact of_decide_eq_true (List.all_eq_true.mp (starReadsBack ⟨j, hj4⟩) w hw)
    · rw [atOld, renamed] at hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      exact renameBelow (h.2.1 k hk v hv)
    · rw [atJoin, joinGate] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact renameBelow (oldOutputBound correct)
      · omega
  · simp only [complete, List.forall_mem_append, List.forall_mem_map]
    exact ⟨⟨by simp [starGates], fun g hg => by simpa [renamed] using h.2.2 g hg⟩, by simp [joinGate]⟩

private theorem renameDistinctInputs : ∀ a b : Fin 25, rename a.val = rename b.val → a = b := by decide

private theorem renameInjective : Function.Injective rename := by
  intro a b h
  by_cases ha : a < 25 <;> by_cases hb : b < 25
  · exact congrArg Fin.val (renameDistinctInputs ⟨a, ha⟩ ⟨b, hb⟩ h)
  · have hs : rename a < 26 := renameInput ⟨a, ha⟩
    rw [renameGateWire (w := b) (by omega)] at h
    omega
  · have hs : rename b < 26 := renameInput ⟨b, hb⟩
    rw [renameGateWire (w := a) (by omega)] at h
    omega
  · rw [renameGateWire (w := a) (by omega), renameGateWire (w := b) (by omega)] at h
    omega

private theorem pullbackSmall {x : Fin 26 → Bool} (h : AtMostTwo x) :
    AtMostTwo (fun w => x (embed w)) := by
  intro a b c ha hb hc
  have injective : Function.Injective embed := fun u v e =>
    Fin.ext (renameInjective (congrArg Fin.val e))
  rcases h (embed a) (embed b) (embed c) ha hb hc with hab | hac | hbc
  · exact Or.inl (injective hab)
  · exact Or.inr (Or.inl (injective hac))
  · exact Or.inr (Or.inr (injective hbc))

theorem completeCorrectOnSmall {C : Circuit}
    (h : ∀ x, AtMostTwo x → (C.eval (List.ofFn x) = true ↔ deleted x)) :
    ∀ x, AtMostTwo x → ((complete C).eval (List.ofFn x) = true ↔ plane x) := by
  intro x hx
  rw [completeEval, Bool.or_eq_true, h _ (pullbackSmall hx), planeSplit]

private theorem renameAvoidsStar (w : ℕ) : rename w ≠ 29 := by
  by_cases h : w < 25
  · have hs := renameInput ⟨w, h⟩
    exact ne_of_lt (hs.trans (by decide))
  · rw [renameGateWire (by omega)]; omega

theorem completeDistinct {C : Circuit} (h : ∀ g ∈ C.gates, g.inputs.Nodup) :
    ∀ g ∈ (complete C).gates, g.inputs.Nodup := by
  simp only [complete, List.forall_mem_append, List.forall_mem_map]
  refine ⟨⟨by simp [starGates], fun g hg => List.Nodup.map renameInjective (h g hg)⟩, ?_⟩
  simp [joinGate, renameAvoidsStar]

def SoundAndOnSmall (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, (gateAt C j).op = GateOp.and → ∀ x : Fin n → Bool, AtMostTwo x →
    (C.wires (List.ofFn x)).getD (n + j) false = true → C.eval (List.ofFn x) = true

private theorem starAndIndex : ∀ j : Fin 4, (starGateAt j.val).op = GateOp.and → j.val = 3 := by
  let _ : DecidableEq GateOp := gateOpDecEq
  decide

private theorem completeWires (C : Circuit) (x : Fin 26 → Bool) :
    (complete C).wires (List.ofFn x) = step ((C.gates.map renamed).foldl step (starWires x)) (joinGate C) := by
  change (starGates ++ C.gates.map renamed ++ [joinGate C]).foldl step (List.ofFn x) = _
  rw [List.foldl_append, List.foldl_append]
  rfl

theorem completeSoundOnSmall {C : Circuit} (h : SoundAndOnSmall 25 C) :
    SoundAndOnSmall 26 (complete C) := by
  intro j op x small active
  have hj : j < C.gates.length + 5 := by
    by_contra! hg
    have hg' : (complete C).gates.length ≤ j := by
      change (complete C).size ≤ j
      rw [completeSize]
      exact hg
    rw [gateAt, List.getD_eq_default _ _ hg'] at op
    cases op
  rw [completeEval]
  rcases completeGateCases C j hj with ⟨hj4, atStar⟩ | ⟨k, hk, rfl, atOld⟩ | ⟨rfl, atJoin⟩
  · rw [atStar] at op
    have eq := starAndIndex ⟨j, hj4⟩ op
    change j = 3 at eq
    subst j
    have hs : star x = true := by
      rw [completeWires, stepOld _ _ (by rw [runLength, starWiresLength]; omega),
        runOld _ _ _ (by rw [starWiresLength]; decide), starValue] at active
      exact active
    simp [hs]
  · have oldAnd : (gateAt C k).op = GateOp.and := by simpa [atOld, renamed] using op
    have preserved := (runAgree C.gates _ _ (starAgree x)).2.2 (25 + k)
    have val : (C.wires (List.ofFn fun i => x (embed i))).getD (25 + k) false = true := by
      rw [completeWires, stepOld _ _ (by rw [runLength, starWiresLength, List.length_map]; omega)] at active
      rw [renameGateWire (by omega)] at preserved
      have eq : 25 + k + 5 = 26 + (4 + k) := by omega
      rw [eq] at preserved
      exact preserved.symm.trans active
    rw [Bool.or_eq_true]
    exact Or.inl (h k oldAnd _ (pullbackSmall small) val)
  · rw [atJoin, joinGate] at op
    cases op

def G : SimpleGraph (Fin 25) := PEqualNP.EdgeOwnership.edgeGraph 25 edges

instance : DecidableRel G.Adj :=
  inferInstanceAs (DecidableRel (PEqualNP.EdgeOwnership.edgeGraph 25 edges).Adj)

def rightCover : Finset (Fin 25) := Finset.univ.filter fun i => 13 ≤ i.val

private theorem coverCorrect : ∀ u v : Fin 25, G.Adj u v → u ∈ rightCover ∨ v ∈ rightCover := by
  decide +kernel

private theorem noLoops : ∀ u v : Fin 25, (u.val, v.val) ∈ edges → u ≠ v := by decide +kernel

theorem graphEdges : G.edgeFinset.card = 48 := by decide +kernel

theorem rightCoverCard : rightCover.card = 12 := by decide +kernel

theorem commonNeighbors : ∀ u v : Fin 25, u ≠ v →
    (Finset.univ.filter (fun w => G.Adj u w ∧ G.Adj v w)).card ≤ 1 := by decide +kernel

private def matchLeft (i : Fin 12) : Fin 25 := Fin.castLE (by decide) i

private def matchRight (i : Fin 12) : Fin 25 :=
  Fin.ofNat 25 (([24, 23, 13, 15, 16, 17, 22, 18, 20, 21, 19, 14] : List ℕ).getD i.val 0)

private def matchEnd (i : Fin 12) (left : Bool) : Fin 25 :=
  if left then matchLeft i else matchRight i

private theorem matchEdges : ∀ i : Fin 12, G.Adj (matchLeft i) (matchRight i) := by decide +kernel

private theorem matchDisjoint : ∀ i j : Fin 12, i ≠ j → ∀ a b : Bool, matchEnd i a ≠ matchEnd j b := by
  decide +kernel

theorem minCover (T : Finset (Fin 25)) (h : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) : 12 ≤ T.card := by
  let f (i : Fin 12) := matchEnd i (decide (matchLeft i ∈ T))
  have hf : Function.Injective f := by
    intro i j e
    by_contra ij
    exact matchDisjoint i j ij _ _ e
  have subset : (Finset.univ.image f) ⊆ T := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    rcases h _ _ (matchEdges i) with hi | hi
    · simp [f, matchEnd, hi]
    · by_cases hleft : matchLeft i ∈ T
      · simp [f, matchEnd, hleft]
      · simpa [f, matchEnd, hleft] using hi
  calc 12 = (Finset.univ.image f).card := by rw [Finset.card_image_of_injective _ hf]; simp
    _ ≤ T.card := Finset.card_le_card subset

theorem upperBound59 : ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 59 ∧
    ∀ x, C.eval (List.ofFn x) = true ↔ deleted x := by
  obtain ⟨C, fan, noNot, sem, size⟩ := PEqualNP.MetaComplexity.L154 25 G rightCover
    ⟨0, 16, by decide⟩ coverCorrect
  rw [graphEdges, rightCoverCard] at size
  refine ⟨C, ?_, by omega, ?_⟩
  · intro g hg
    obtain ⟨op, len⟩ := fan g hg
    refine ⟨?_, len⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    rcases op with and | or | not
    · exact Or.inl and
    · exact Or.inr or
    · exact (noNot g hg not).elim
  · intro x
    have hx := congrFun sem x
    change C.eval (List.ofFn x) = _ at hx
    rw [hx, decide_eq_true_eq]
    constructor
    · rintro ⟨u, v, ⟨_, uv | vu⟩, hu, hv⟩
      · exact ⟨u, v, uv, hu, hv⟩
      · exact ⟨v, u, vu, hv, hu⟩
    · rintro ⟨u, v, uv, hu, hv⟩
      exact ⟨u, v, ⟨noLoops u v uv, Or.inl uv⟩, hu, hv⟩

end PlaneCompletion
