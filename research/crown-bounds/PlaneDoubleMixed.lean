import PEqualNP.Defs

-- Uses the accepted project proofs L-meta-8097 and L-meta-8099.

namespace PEqualNP.Outside.L_meta_8097

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem fuelS {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) : ∀ (k : ℕ) (i : Fin C.size), (i : ℕ) < k → ∀ d e : ℕ, (i : ℕ) < d → (i : ℕ) < e → gateValFuel C U d i = gateValFuel C U e i := by
  intro k
  induction k with
  | zero => intro i hi; omega
  | succ k ih =>
    intro i hi d e hd he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
    have hs : ∀ (B : Finset (Fin n)) (F : Finset (Fin C.size)), sideTrue U B F i (gateValFuel C U d) = sideTrue U B F i (gateValFuel C U e) := by
      intro B F
      unfold sideTrue
      congr 1
      apply propext
      refine or_congr_right (exists_congr fun j => and_congr_right fun _ => and_congr_right fun hj => ?_)
      have hj' : (j : ℕ) < (i : ℕ) := hj
      rw [ih j (by omega) d e (by omega) (by omega)]
    simp only [Nat.succ_eq_add_one, gateValFuel]
    rw [hs, hs]

theorem gv {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) && sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have h : C.gateVal U i = gateValFuel C U (C.size + 1) i := fuelS C U (i + 1) i (by omega) _ _ i.isLt (by have := i.isLt; omega)
  rw [h]
  rfl


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8097

theorem PEqualNP.Outside.L_meta_8097 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → ∀ (x6 : Finset (Fin x1)), (∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → x7 ∈ x6 ∨ x8 ∈ x6) → (∀ x8 ⊆ x6, (∀ (x10 x11 : Fin x1), x3.Adj x10 x11 → x10 ∈ x8 ∨ x11 ∈ x8) → x6 ⊆ x8) → ∃ (x9 : Finset (Fin x2.size)) (x10 : Finset (Fin x2.size)), Disjoint x9 x10 ∧ x9.biUnion x2.leftVars ∪ x10.biUnion x2.rightVars = x6 := by
  intro n C G hC hout X hcov hmin
  classical
  let I : Finset (Fin n) := Finset.univ \ X
  have hI : C.eval I = false := by
    cases h : C.eval I
    · rfl
    · obtain ⟨a, ha, b, hb, hab⟩ := (hC I).1 h
      simp only [I, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha hb
      rcases hcov a b hab with h' | h'
      · exact absurd h' ha
      · exact absurd h' hb
  let sl : Fin C.size → Bool := fun g => PEqualNP.AndCount.AndCountCircuit.sideTrue I (C.leftVars g) (C.leftGates g) g (C.gateVal I)
  let sr : Fin C.size → Bool := fun g => PEqualNP.AndCount.AndCountCircuit.sideTrue I (C.rightVars g) (C.rightGates g) g (C.gateVal I)
  let A : Finset (Fin C.size) := Finset.univ.filter fun g => sl g = false
  let B : Finset (Fin C.size) := Finset.univ.filter fun g => sl g = true ∧ sr g = false
  have hnot : ∀ (V : Finset (Fin n)) (F : Finset (Fin C.size)) (g : Fin C.size), PEqualNP.AndCount.AndCountCircuit.sideTrue I V F g (C.gateVal I) = false → ∀ x ∈ V, x ∈ X := by
    intro V F g h x hx
    simp only [PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_false_iff_not] at h
    by_contra hxX
    exact h (Or.inl ⟨x, hx, by simp [I, hxX]⟩)
  refine ⟨A, B, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro g h1 h2
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2; cases h2.1
  · apply Finset.Subset.antisymm
    · intro x hx
      simp only [Finset.mem_union, Finset.mem_biUnion, A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rcases hx with ⟨g, hg, hx⟩ | ⟨g, hg, hx⟩
      · exact hnot _ _ g hg x hx
      · exact hnot _ _ g hg.2 x hx
    · intro x hxX
      by_contra hx
      simp only [Finset.mem_union, Finset.mem_biUnion, A, B, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_exists, not_and] at hx
      obtain ⟨hx1, hx2⟩ := hx
      -- an edge from x to the independent set
      have hedge : ∃ b, b ∉ X ∧ G.Adj x b := by
        by_contra hcon
        push_neg at hcon
        have := hmin (X.erase x) (Finset.erase_subset _ _) (by
          intro a b hab
          rcases hcov a b hab with ha | hb
          · by_cases hax : a = x
            · subst hax
              right
              rw [Finset.mem_erase]
              refine ⟨fun e => G.loopless.irrefl a (by rw [e] at hab; exact hab), ?_⟩
              by_contra hb
              exact hcon b hb hab
            · exact Or.inl (Finset.mem_erase.2 ⟨hax, ha⟩)
          · by_cases hbx : b = x
            · subst hbx
              left
              rw [Finset.mem_erase]
              refine ⟨fun e => G.loopless.irrefl b (by rw [e] at hab; exact hab), ?_⟩
              by_contra ha
              exact hcon a ha hab.symm
            · exact Or.inr (Finset.mem_erase.2 ⟨hbx, hb⟩)) hxX
        simp at this
      obtain ⟨b, hb, hxb⟩ := hedge
      let J : Finset (Fin n) := insert x I
      have hJ : C.eval J = true := (hC J).2 ⟨x, by simp [J], b, by simp [J, I, hb], hxb⟩
      have hval : ∀ k, ∀ g : Fin C.size, (g : ℕ) < k → C.gateVal I g = false → C.gateVal J g = false := by
        intro k
        induction k with
        | zero => intro g hg; omega
        | succ k ih =>
          intro g hg h
          have hs : ∀ (V : Finset (Fin n)) (F : Finset (Fin C.size)), x ∉ V → PEqualNP.AndCount.AndCountCircuit.sideTrue I V F g (C.gateVal I) = false → PEqualNP.AndCount.AndCountCircuit.sideTrue J V F g (C.gateVal J) = false := by
            intro V F hxV h
            simp only [PEqualNP.AndCount.AndCountCircuit.sideTrue, decide_eq_false_iff_not] at h ⊢
            rintro (⟨w, hw, hwJ⟩ | ⟨j, hj, hjg, hjt⟩)
            · rcases Finset.mem_insert.1 hwJ with rfl | hwI
              · exact hxV hw
              · exact h (Or.inl ⟨w, hw, hwI⟩)
            · refine h (Or.inr ⟨j, hj, hjg, ?_⟩)
              by_contra hjI
              have hj' : (j : ℕ) < (g : ℕ) := hjg
              rw [ih j (by omega) (by simpa using hjI)] at hjt
              cases hjt
          rw [PEqualNP.Outside.L_meta_8097.gv, Bool.and_eq_false_iff] at h ⊢
          cases hl : sl g
          · exact Or.inl (hs _ _ (hx1 g hl) hl)
          · rcases h with h | h
            · rw [show PEqualNP.AndCount.AndCountCircuit.sideTrue I (C.leftVars g) (C.leftGates g) g (C.gateVal I) = sl g from rfl, hl] at h; cases h
            · exact Or.inr (hs _ _ (hx2 g ⟨hl, h⟩) h)
      simp only [PEqualNP.AndCount.AndCountCircuit.eval, hout, decide_eq_true_eq, decide_eq_false_iff_not] at hJ hI
      rcases hJ with ⟨w, hw, _⟩ | ⟨j, hj, hjt⟩
      · simp at hw
      · have : C.gateVal I j = false := by
          by_contra h
          exact hI (Or.inr ⟨j, hj, by simpa using h⟩)
        rw [hval C.size j j.isLt this] at hjt
        cases hjt

namespace PEqualNP.Outside.L_meta_8099

open PEqualNP.AndCount

-- Every gate true at fuel d leads to a gate whose two sides both meet U by bare variables.
theorem fuel_witness {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true →
      ∃ k : Fin C.size, (∃ v ∈ C.leftVars k, v ∈ U) ∧ (∃ v ∈ C.rightVars k, v ∈ U) := by
  intro d
  induction d with
  | zero =>
    intro i h
    simp [AndCountCircuit.gateValFuel] at h
  | succ d ih =>
    intro i h
    simp only [AndCountCircuit.gateValFuel, Bool.and_eq_true,
      AndCountCircuit.sideTrue, decide_eq_true_eq] at h
    obtain ⟨hl, hr⟩ := h
    rcases hl with hl | ⟨j, _, _, hj⟩
    · rcases hr with hr | ⟨j, _, _, hj⟩
      · exact ⟨i, hl, hr⟩
      · exact ih j hj
    · exact ih j hj

end PEqualNP.Outside.L_meta_8099

theorem PEqualNP.Outside.L_meta_8099 : ∀ (x1 : ℕ) (x2 : PEqualNP.AndCount.AndCountCircuit x1) (x3 : SimpleGraph (Fin x1)), x2.Computes x3 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) → ∀ (x7 x8 : Fin x1), x3.Adj x7 x8 → ∃ (x10 : Fin x2.size), x7 ∈ x2.leftVars x10 ∧ x8 ∈ x2.rightVars x10 ∨ x8 ∈ x2.leftVars x10 ∧ x7 ∈ x2.rightVars x10 := by
  classical
  intro n C G hC hOut hDisj a b hab
  have hEv : C.eval {a, b} = true :=
    (hC {a, b}).mpr ⟨a, by simp, b, by simp, hab⟩
  rw [PEqualNP.AndCount.AndCountCircuit.eval, decide_eq_true_eq] at hEv
  rcases hEv with ⟨v, hv, _⟩ | ⟨j, _, hj⟩
  · rw [hOut] at hv
    simp at hv
  · obtain ⟨k, ⟨v, hvl, hvU⟩, ⟨w, hwr, hwU⟩⟩ :=
      PEqualNP.Outside.L_meta_8099.fuel_witness C {a, b} C.size j hj
    refine ⟨k, ?_⟩
    have hd := hDisj k
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvU hwU
    rcases hvU with rfl | rfl <;> rcases hwU with rfl | rfl
    · exact absurd hwr (Finset.disjoint_left.mp hd hvl)
    · exact Or.inl ⟨hvl, hwr⟩
    · exact Or.inr ⟨hvl, hwr⟩
    · exact absurd hwr (Finset.disjoint_left.mp hd hvl)

namespace PlaneCoverReadSets

variable {V : Type} [Fintype V] [DecidableEq V]
variable {J : Type} [Fintype J] [DecidableEq J]

def colorClass (color : V → Bool) (c : Bool) : Finset V :=
  Finset.univ.filter fun v => color v = c

def neighbors (adj : V → V → Prop) [DecidableRel adj] (v : V) : Finset V :=
  Finset.univ.filter (adj v)

def Covers (adj : V → V → Prop) (C : Finset V) : Prop :=
  ∀ v w, adj v w → v ∈ C ∨ w ∈ C

def MinimalCover (adj : V → V → Prop) (C : Finset V) : Prop :=
  Covers adj C ∧ ∀ C' ⊆ C, Covers adj C' → C ⊆ C'

def sideCover (adj : V → V → Prop) [DecidableRel adj] (color : V → Bool)
    (c : Bool) (S : Finset V) : Finset V :=
  (colorClass color c \ S) ∪ S.biUnion (neighbors adj)

/-- A vertex outside the selected small set has a neighbor outside the
neighborhood union, because each selected vertex accounts for at most one. -/
private theorem neighborOutside (adj : V → V → Prop) [DecidableRel adj]
    {S : Finset V} {v : V} (misses : v ∉ S)
    (thin : ∀ v w, v ≠ w → ((neighbors adj v) ∩ (neighbors adj w)).card ≤ 1)
    (small : S.card < (neighbors adj v).card) : ∃ w ∈ neighbors adj v, w ∉ S.biUnion (neighbors adj) := by
  classical
  have identity : (neighbors adj v) ∩ S.biUnion (neighbors adj) =
      S.biUnion (fun u => neighbors adj v ∩ neighbors adj u) := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hv, u, hu, hwu⟩
      exact ⟨u, hu, hv, hwu⟩
    · rintro ⟨u, hu, hv, hwu⟩
      exact ⟨hv, u, hu, hwu⟩
  have bound : ((neighbors adj v) ∩ S.biUnion (neighbors adj)).card ≤ S.card := by
    rw [identity]
    calc
      _ ≤ ∑ u ∈ S, (neighbors adj v ∩ neighbors adj u).card := Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ S, 1 := Finset.sum_le_sum (fun u hu => thin v u (fun eq => misses (eq ▸ hu)))
      _ = S.card := by simp
  by_contra! covered
  have sub : neighbors adj v ⊆ neighbors adj v ∩ S.biUnion (neighbors adj) := by
    intro w mem
    exact Finset.mem_inter.mpr ⟨mem, covered w mem⟩
  exact (not_le_of_gt small) ((Finset.card_le_card sub).trans bound)

/-- On a regular bipartite incidence graph with at most one common neighbor,
omitting fewer than one degree's worth of vertices on a color class gives a
minimal cover by adding their neighbors. -/
theorem smallSideCover (adj : V → V → Prop) [DecidableRel adj] (color : V → Bool)
    (symmetric : Std.Symm adj) (bipartite : ∀ v w, adj v w → color v ≠ color w)
    {d : ℕ} (degree : ∀ v, (neighbors adj v).card = d)
    (thin : ∀ v w, v ≠ w → ((neighbors adj v) ∩ (neighbors adj w)).card ≤ 1)
    (c : Bool) (S : Finset V) (side : S ⊆ colorClass color c)
    (small : S.card < d) : MinimalCover adj (sideCover adj color c S) := by
  classical
  have colors (v : V) (mem : v ∈ S) : color v = c := (Finset.mem_filter.mp (side mem)).2
  have outsideHalo (v : V) (same : color v = c) : v ∉ S.biUnion (neighbors adj) := by
    intro hit
    obtain ⟨w, mem, incident⟩ := Finset.mem_biUnion.mp hit
    exact bipartite w v (Finset.mem_filter.mp incident).2 ((colors w mem).trans same.symm)
  have coverOnSide (v w : V) (incident : adj v w) (colored : color v = c) :
      v ∈ sideCover adj color c S ∨ w ∈ sideCover adj color c S := by
    by_cases hv : v ∈ S
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨v, hv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, incident⟩⟩))
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, colored⟩, hv⟩))
  refine ⟨?_, ?_⟩
  · intro v w incident
    by_cases same : color v = c
    · exact coverOnSide v w incident same
    · have other : color w = c := by
        have opp := bipartite v w incident
        cases hv : color v <;> cases hw : color w <;> cases c <;> simp_all
      exact (coverOnSide w v (symmetric.symm _ _ incident) other).symm
  · intro C sub cv v mem
    rcases Finset.mem_union.mp mem with own | halo
    · obtain ⟨onSide, misses⟩ := Finset.mem_sdiff.mp own
      have same := (Finset.mem_filter.mp onSide).2
      obtain ⟨w, near, outside⟩ := neighborOutside adj misses thin (by simpa [degree] using small)
      have incident := (Finset.mem_filter.mp near).2
      have notCover : w ∉ sideCover adj color c S := by
        intro member
        rcases Finset.mem_union.mp member with left | right
        · exact bipartite v w incident (same.trans (Finset.mem_filter.mp (Finset.mem_sdiff.mp left).1).2.symm)
        · exact outside right
      exact (cv v w incident).resolve_right (fun hit => notCover (sub hit))
    · obtain ⟨w, chosen, near⟩ := Finset.mem_biUnion.mp halo
      have notCover : w ∉ sideCover adj color c S := by
        intro member
        rcases Finset.mem_union.mp member with left | right
        · exact (Finset.mem_sdiff.mp left).2 chosen
        · exact outsideHalo w (colors w chosen) right
      exact (cv w v (Finset.mem_filter.mp near).2).resolve_left (fun hit => notCover (sub hit))

def Reads (sides : J → Finset V) (v : V) : Finset J :=
  Finset.univ.filter fun j => v ∈ sides j

/-- The local consequence of representing every minimal cover by operand
sides. Each of its vertices is in some side contained in the cover. -/
def RealizesCovers (adj : V → V → Prop) (sides : J → Finset V) : Prop :=
  ∀ C, MinimalCover adj C → ∀ v ∈ C, ∃ j, v ∈ sides j ∧ sides j ⊆ C

omit [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J] in
private theorem twoToOne {A : Finset V} {B : Finset J} {Q : V → J → Prop}
    (many : B.card < A.card) (step : ∀ v ∈ A, ∃ w ∈ B, Q v w) :
    ∃ w ∈ B, ∃ u ∈ A, ∃ v ∈ A, u ≠ v ∧ Q u w ∧ Q v w := by
  classical
  have chooseOne (a : {x // x ∈ A}) : ∃ b : {x // x ∈ B}, Q a.val b.val := by
    obtain ⟨w, hit, rel⟩ := step a.val a.property
    exact ⟨⟨w, hit⟩, rel⟩
  choose f prop using chooseOne
  have notInj : ¬ Function.Injective f := by
    intro inj
    have count := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_coe] at count
    omega
  obtain ⟨u, v, equal, distinct⟩ := Function.not_injective_iff.mp notInj
  exact ⟨(f u).val, (f u).property, u.val, u.property, v.val, v.property,
    fun h => distinct (Subtype.ext h), prop u, equal ▸ prop v⟩

omit [Fintype J] [DecidableEq J] in
/-- A selected operand must be pure for each vertex, because the whole
vertex's color class is a minimal cover. -/
theorem pureSide (adj : V → V → Prop) [DecidableRel adj] (color : V → Bool)
    (symmetric : Std.Symm adj) (bipartite : ∀ v w, adj v w → color v ≠ color w)
    {d : ℕ} (pos : 0 < d) (degree : ∀ v, (neighbors adj v).card = d)
    (thin : ∀ v w, v ≠ w → ((neighbors adj v) ∩ (neighbors adj w)).card ≤ 1)
    (sides : J → Finset V) (realizes : RealizesCovers adj sides) (v : V) :
    ∃ j, v ∈ sides j ∧ sides j ⊆ colorClass color (color v) := by
  have mini := smallSideCover adj color symmetric bipartite degree thin (color v) ∅ (by simp) (by simpa using pos)
  have whole : MinimalCover adj (colorClass color (color v)) := by simpa [sideCover] using mini
  exact realizes _ whole v (by simp [colorClass])

def ColorSingleton (color : V → Bool) (S : Finset V) (v : V) : Prop :=
  v ∈ S ∧ ∀ u ∈ S, color u = color v → u = v

omit [DecidableEq J] in
/-- Under the read cap, every vertex has an operand containing no other
vertex of its color. Two neighbors must use the same operand to cover it. -/
theorem isolatedColorSide (adj : V → V → Prop) [DecidableRel adj] (color : V → Bool)
    (symmetric : Std.Symm adj) (bipartite : ∀ v w, adj v w → color v ≠ color w)
    {d : ℕ} (large : 1 < d) (degree : ∀ v, (neighbors adj v).card = d)
    (thin : ∀ v w, v ≠ w → ((neighbors adj v) ∩ (neighbors adj w)).card ≤ 1)
    (sides : J → Finset V) (realizes : RealizesCovers adj sides)
    (bound : ∀ v, (Reads sides v).card < d) (v : V) : ∃ j, ColorSingleton color (sides j) v := by
  classical
  have chooseSide (w : V) (neighbor : w ∈ neighbors adj v) : ∃ j ∈ Reads sides v,
      sides j ⊆ sideCover adj color (color w) {w} := by
    have incident := (Finset.mem_filter.mp neighbor).2
    have mini := smallSideCover adj color symmetric bipartite degree thin (color w) {w}
      (by simp [colorClass]) (by simpa using large)
    have included : v ∈ sideCover adj color (color w) {w} := by
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨w, by simp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, symmetric.symm _ _ incident⟩⟩)
    obtain ⟨j, use, sub⟩ := realizes _ mini v included
    exact ⟨j, by simp [Reads, use], sub⟩
  obtain ⟨j, used, u, nu, w, nw, apart, subU, subW⟩ :=
    twoToOne (A := neighbors adj v) (B := Reads sides v) (by simpa [degree] using bound v) chooseSide
  refine ⟨j, (Finset.mem_filter.mp used).2, ?_⟩
  have nearU := (Finset.mem_filter.mp nu).2
  have nearW := (Finset.mem_filter.mp nw).2
  have into (s : V) (near : adj v s) (sub : sides j ⊆ sideCover adj color (color s) {s})
      (a : V) (mem : a ∈ sides j) (same : color a = color v) : a ∈ neighbors adj s := by
    rcases Finset.mem_union.mp (sub mem) with left | right
    · have wrong := (Finset.mem_filter.mp (Finset.mem_sdiff.mp left).1).2
      exact (bipartite v s near (same.symm.trans wrong)).elim
    · simpa using right
  intro a mem same
  have once := thin u w apart
  apply (Finset.card_le_one.mp once)
  · exact Finset.mem_inter.mpr ⟨into u nearU subU a mem same, into w nearW subW a mem same⟩
  · exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, symmetric.symm _ _ nearU⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, symmetric.symm _ _ nearW⟩⟩

noncomputable def pairSides (color : V → Bool) (sides : J → Finset V) : Finset J := by
  classical
  exact Finset.univ.filter fun j => ∃ v w, color v ≠ color w ∧ sides j = {v, w}

/-- If there are fewer operand sides than vertices, collisions in the choice
of isolating sides must be two-vertex sides. Each color also needs a pure
side outside the image of that choice. -/
theorem pairSidesBound (color : V → Bool) (sides : J → Finset V)
    (pure : ∀ v, ∃ j, v ∈ sides j ∧ sides j ⊆ colorClass color (color v))
    (isolated : ∀ v, ∃ j, ColorSingleton color (sides j) v)
    (smaller : Fintype.card J < Fintype.card V) :
    ∃ shared : Finset J, shared ⊆ pairSides color sides ∧
      (shared : Set J).PairwiseDisjoint sides ∧ Fintype.card V + 2 ≤ Fintype.card J + shared.card := by
  classical
  have selection (v : V) : ∃ j, ColorSingleton color (sides j) v ∧
      ((∃ k, sides k = {v}) → sides j = {v}) := by
    by_cases single : ∃ k, sides k = {v}
    · obtain ⟨j, eq⟩ := single
      exact ⟨j, by simp [eq, ColorSingleton], fun _ => eq⟩
    · obtain ⟨j, iso⟩ := isolated v
      exact ⟨j, iso, fun h => (single h).elim⟩
  choose pick properties using selection
  have oppOfCollision {u v : V} (apart : u ≠ v) (eq : pick u = pick v) : color u ≠ color v := by
    intro same
    exact apart ((properties u).1.2 v (eq.symm ▸ (properties v).1.1) same.symm).symm
  have twoOfCollision {u v : V} (apart : u ≠ v) (eq : pick u = pick v) :
      sides (pick u) = {u, v} := by
    have opp := oppOfCollision apart eq
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro mem
      by_cases same : color x = color u
      · exact Or.inl ((properties u).1.2 x mem same)
      · have other : color x = color v := by
          cases hu : color u <;> cases hv : color v <;> cases hx : color x <;> simp_all
        exact Or.inr ((properties v).1.2 x (eq ▸ mem) other)
    · rintro (xu | xv)
      · exact xu.symm ▸ (properties u).1.1
      · exact xv.symm ▸ (eq.symm ▸ (properties v).1.1)
  have missing (v : V) (noSingle : ¬ ∃ j, sides j = {v}) :
      ∃ j, v ∈ sides j ∧ sides j ⊆ colorClass color (color v) ∧ ∀ x, pick x ≠ j := by
    obtain ⟨j, hit, pureJ⟩ := pure v
    refine ⟨j, hit, pureJ, ?_⟩
    intro x eq
    have hx := eq ▸ (properties x).1.1
    have colored := (Finset.mem_filter.mp (pureJ hx)).2
    have sideSingle : sides j = {x} := by
      ext u
      simp only [Finset.mem_singleton]
      constructor
      · intro hu
        exact (properties x).1.2 u (eq.symm ▸ hu)
          (((Finset.mem_filter.mp (pureJ hu)).2).trans colored.symm)
      · rintro rfl
        exact hx
    have vx : v = x := by simpa [sideSingle] using hit
    exact noSingle ⟨j, by simpa [vx] using sideSingle⟩
  obtain ⟨u, v, apart, eq⟩ := Fintype.exists_ne_map_eq_of_card_lt pick smaller
  have pair := twoOfCollision apart eq
  have noSingleU : ¬ ∃ j, sides j = {u} := by
    intro single
    have distinct := (properties u).2 single
    have : v ∈ ({u} : Finset V) := by rw [← distinct, pair]; simp
    exact apart (Finset.mem_singleton.mp this).symm
  have noSingleV : ¬ ∃ j, sides j = {v} := by
    intro single
    have distinct := (properties v).2 single
    have : u ∈ ({v} : Finset V) := by rw [← distinct, ← eq, pair]; simp
    exact apart (Finset.mem_singleton.mp this)
  obtain ⟨a, au, _, missingA⟩ := missing u noSingleU
  obtain ⟨b, _, pureB, missingB⟩ := missing v noSingleV
  have ab : a ≠ b := by
    intro same
    exact oppOfCollision apart eq ((Finset.mem_filter.mp (pureB (same ▸ au))).2)
  let live := (Finset.univ.erase a).erase b
  have maps (x : V) : pick x ∈ live := by simp [live, missingA, missingB]
  have liveCard : live.card + 2 = Fintype.card J := by
    have ha : a ∈ (Finset.univ : Finset J) := Finset.mem_univ _
    have hb : b ∈ (Finset.univ : Finset J).erase a := by simp [Ne.symm ab]
    have := Finset.card_erase_add_one ha
    have := Finset.card_erase_add_one hb
    simp only [Finset.card_univ] at *
    dsimp [live]
    omega
  let fiber (j : J) := Finset.univ.filter fun x => pick x = j
  let shared := live.filter fun j => 1 < (fiber j).card
  have equality (j : J) (large : 1 < (fiber j).card) :
      ∃ x y, color x ≠ color y ∧ sides j = {x, y} ∧ fiber j = {x, y} := by
    obtain ⟨x, y, hx, hy, xy⟩ := Finset.one_lt_card_iff.mp large
    have xj := (Finset.mem_filter.mp hx).2
    have yj := (Finset.mem_filter.mp hy).2
    have same := xj.trans yj.symm
    have pairJ : sides j = {x, y} := xj ▸ twoOfCollision xy same
    refine ⟨x, y, oppOfCollision xy same, pairJ, Finset.Subset.antisymm ?_ ?_⟩
    · intro z hz
      have zj := (Finset.mem_filter.mp hz).2
      have mem : z ∈ sides j := zj ▸ (properties z).1.1
      exact pairJ ▸ mem
    · intro z hz
      rcases Finset.mem_insert.mp hz with zx | zy
      · exact zx.symm ▸ hx
      · exact (Finset.mem_singleton.mp zy).symm ▸ hy
  have fiberBound (j : J) : (fiber j).card ≤ 1 + if 1 < (fiber j).card then 1 else 0 := by
    split_ifs with large
    · obtain ⟨x, y, _, _, eqFiber⟩ := equality j large
      rw [eqFiber]
      exact Finset.card_le_two
    · omega
  have counts := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V) live pick
  simp only [maps, Finset.filter_true, Finset.card_univ] at counts
  have size : Fintype.card V ≤ live.card + shared.card := calc
    _ = ∑ j ∈ live, (fiber j).card := counts.symm
    _ ≤ ∑ j ∈ live, (1 + if 1 < (fiber j).card then 1 else 0) :=
      Finset.sum_le_sum (fun j _ => fiberBound j)
    _ = live.card + shared.card := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [shared]
  refine ⟨shared, ?_, ?_, by omega⟩
  · intro j hj
    obtain ⟨x, y, opp, eqSide, _⟩ := equality j (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, y, opp, eqSide⟩
  · intro j hj k hk different
    obtain ⟨_, _, _, sj, fj⟩ := equality j (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
    obtain ⟨_, _, _, sk, fk⟩ := equality k (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2
    change Disjoint (sides j) (sides k)
    rw [sj.trans fj.symm, sk.trans fk.symm]
    exact Finset.disjoint_left.mpr (fun _ hj hitK => different
      ((Finset.mem_filter.mp hj).2.symm.trans (Finset.mem_filter.mp hitK).2))

def planeRel (u v : Fin 42) : Prop :=
  u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ [0, 5, 7, 17, 20]

instance : DecidableRel planeRel := fun u v =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ (v.val + 21 - u.val) % 21 ∈ [0, 5, 7, 17, 20]))

def planeGraph : SimpleGraph (Fin 42) := SimpleGraph.fromRel planeRel

instance : DecidableRel planeGraph.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel planeRel).Adj)

def planeColor (v : Fin 42) : Bool := decide (v.val < 21)

def operand {k : ℕ} (A B : Fin k → Finset (Fin 42)) (j : Fin k × Bool) : Finset (Fin 42) :=
  if j.2 then A j.1 else B j.1

private theorem operandReads {k : ℕ} {A B : Fin k → Finset (Fin 42)}
    (separate : ∀ j, Disjoint (A j) (B j)) (v : Fin 42) :
    (Reads (operand A B) v).card = {j : Fin k | v ∈ A j ∨ v ∈ B j}.ncard := by
  classical
  let both := (Finset.univ : Finset (Fin k)).filter fun j => v ∈ A j ∨ v ∈ B j
  have onto : (Reads (operand A B) v).image Prod.fst = both := by
    ext j
    simp only [both, Reads, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, b⟩, hit, rfl⟩
      cases b with
      | true => exact Or.inl (by simpa [operand] using hit)
      | false => exact Or.inr (by simpa [operand] using hit)
    · rintro (left | right)
      · exact ⟨(j, true), by simpa [operand] using left, rfl⟩
      · exact ⟨(j, false), by simpa [operand] using right, rfl⟩
  have one : Set.InjOn Prod.fst (↑(Reads (operand A B) v) : Set (Fin k × Bool)) := by
    rintro ⟨i, s⟩ hs ⟨j, t⟩ ht (eq : i = j)
    subst j
    have hitS := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
    have hitT := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    cases s <;> cases t <;> try rfl
    · exact (Finset.disjoint_left.mp (separate i) (by simpa [operand] using hitT)
        (by simpa [operand] using hitS)).elim
    · exact (Finset.disjoint_left.mp (separate i) (by simpa [operand] using hitS)
        (by simpa [operand] using hitT)).elim
  have setBoth : ({j : Fin k | v ∈ A j ∨ v ∈ B j} : Set (Fin k)) = ↑both := by
    ext j
    simp [both]
  rw [setBoth, Set.ncard_coe_finset, ← onto, Finset.card_image_of_injOn one]

private theorem operandsRealize {k : ℕ} (A B : Fin k → Finset (Fin 42))
    (represent : ∀ C, MinimalCover planeGraph.Adj C → ∃ U W : Finset (Fin k),
      Disjoint U W ∧ U.biUnion A ∪ W.biUnion B = C) :
    RealizesCovers planeGraph.Adj (operand A B) := by
  intro C minimal v mem
  obtain ⟨U, W, _, union⟩ := represent C minimal
  rw [← union] at mem
  rcases Finset.mem_union.mp mem with first | second
  · obtain ⟨j, chosen, hit⟩ := Finset.mem_biUnion.mp first
    refine ⟨(j, true), by simpa [operand] using hit, ?_⟩
    intro u hu
    rw [← union]
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, chosen, by simpa [operand] using hu⟩)
  · obtain ⟨j, chosen, hit⟩ := Finset.mem_biUnion.mp second
    refine ⟨(j, false), by simpa [operand] using hit, ?_⟩
    intro u hu
    rw [← union]
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, chosen, by simpa [operand] using hu⟩)

private theorem planeBipartite : ∀ u v, planeGraph.Adj u v → planeColor u ≠ planeColor v := by
  decide +kernel

private theorem planeDegree : ∀ v, (neighbors planeGraph.Adj v).card = 5 := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
private theorem planeThin : ∀ u v, u ≠ v →
    ((neighbors planeGraph.Adj u) ∩ (neighbors planeGraph.Adj v)).card ≤ 1 := by
  decide +kernel

/-- A family satisfying the read and cover conditions of L-meta-8101 has at
least four vertex-disjoint operand sides of one point and one line each. -/
theorem planeFourPairSides (A B : Fin 20 → Finset (Fin 42))
    (separate : ∀ j, Disjoint (A j) (B j))
    (readBound : ∀ v, {j : Fin 20 | v ∈ A j ∨ v ∈ B j}.ncard ≤ 4)
    (represent : ∀ C, MinimalCover planeGraph.Adj C → ∃ U W : Finset (Fin 20),
      Disjoint U W ∧ U.biUnion A ∪ W.biUnion B = C) :
    ∃ shared : Finset (Fin 20 × Bool), shared ⊆ pairSides planeColor (operand A B) ∧
      (shared : Set (Fin 20 × Bool)).PairwiseDisjoint (operand A B) ∧ 4 ≤ shared.card := by
  have symm : Std.Symm planeGraph.Adj := ⟨fun _ _ h => h.symm⟩
  have realizes := operandsRealize A B represent
  have below (v : Fin 42) : (Reads (operand A B) v).card < 5 := by
    have bound := readBound v
    rw [operandReads separate]
    omega
  obtain ⟨shared, pairs, disjoint, bound⟩ := pairSidesBound planeColor (operand A B)
    (pureSide planeGraph.Adj planeColor symm planeBipartite (by decide) planeDegree planeThin _ realizes)
    (isolatedColorSide planeGraph.Adj planeColor symm planeBipartite (by decide)
      planeDegree planeThin _ realizes below) (by decide)
  have sideCount : Fintype.card (Fin 20 × Bool) = 40 := by decide
  rw [sideCount, Fintype.card_fin] at bound
  exact ⟨shared, pairs, disjoint, by omega⟩

end PlaneCoverReadSets

namespace AndCountCover

open PEqualNP.AndCount AndCountCircuit

private theorem sideCongr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k))
    (i : Fin k) (v w : Fin k → Bool) (agree : ∀ j < i, v j = w j) :
    sideTrue U B F i v = sideTrue U B F i w := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (h | ⟨j, hj, earlier, hit⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, earlier, (agree j earlier).symm.trans hit⟩
  · rintro (h | ⟨j, hj, earlier, hit⟩)
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, earlier, (agree j earlier).trans hit⟩

private theorem fuelAgree {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d e : ℕ) (i : Fin C.size), i.val < d → i.val < e →
      C.gateValFuel U d i = C.gateValFuel U e i := by
  intro d
  induction d with
  | zero => omega
  | succ d ih =>
    intro e i hd he
    cases e with
    | zero => omega
    | succ e =>
      have agree : ∀ j : Fin C.size, j < i → C.gateValFuel U d j = C.gateValFuel U e j := by
        intro j earlier
        exact ih e j (by omega) (by omega)
      simp only [gateValFuel]
      rw [sideCongr U _ _ i _ _ agree, sideCongr U _ _ i _ _ agree]

theorem gateEquation {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
      sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have full : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    fuelAgree C U C.size (i.val + 1) i i.isLt (Nat.lt_succ_self _)
  have agree : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j :=
    fun j earlier => fuelAgree C U i.val C.size j earlier j.isLt
  rw [full, gateValFuel, sideCongr U _ _ i _ _ agree, sideCongr U _ _ i _ _ agree]

theorem distinguishInput {n : ℕ} (C : AndCountCircuit n) (empty : C.outVars = ∅)
    (p q : Fin n) (U : Finset (Fin n)) (present : q ∈ U)
    (essential : C.eval (insert p U) ≠ C.eval U) :
    ∃ i, (p ∈ C.leftVars i ∧ q ∉ C.leftVars i) ∨ (p ∈ C.rightVars i ∧ q ∉ C.rightVars i) := by
  by_contra absent
  have equal (i : Fin C.size) : C.gateVal (insert p U) i = C.gateVal U i := by
    refine (wellFounded_lt (α := Fin C.size)).induction
      (C := fun j => C.gateVal (insert p U) j = C.gateVal U j) i ?_
    intro i ih
    have evalSide (B : Finset (Fin n)) (F : Finset (Fin C.size)) (contained : p ∈ B → q ∈ B) :
        sideTrue (insert p U) B F i (C.gateVal (insert p U)) = sideTrue U B F i (C.gateVal U) := by
      rw [sideCongr (insert p U) B F i _ _ ih]
      unfold sideTrue
      apply decide_eq_decide.mpr
      constructor
      · rintro (⟨v, hv, member⟩ | gates)
        · rcases Finset.mem_insert.mp member with rfl | old
          · exact Or.inl ⟨q, contained hv, present⟩
          · exact Or.inl ⟨v, hv, old⟩
        · exact Or.inr gates
      · rintro (⟨v, hv, member⟩ | gates)
        · exact Or.inl ⟨v, hv, Finset.mem_insert_of_mem member⟩
        · exact Or.inr gates
    have left : p ∈ C.leftVars i → q ∈ C.leftVars i := by
      intro hp
      by_contra hq
      exact absent ⟨i, Or.inl ⟨hp, hq⟩⟩
    have right : p ∈ C.rightVars i → q ∈ C.rightVars i := by
      intro hp
      by_contra hq
      exact absent ⟨i, Or.inr ⟨hp, hq⟩⟩
    rw [gateEquation C (insert p U) i, gateEquation C U i, evalSide _ _ left, evalSide _ _ right]
  exact essential (by simp [eval, empty, equal])

theorem separateRead {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (computes : C.Computes G) (empty : C.outVars = ∅) {p q w : Fin n}
    (adjacent : G.Adj p w) (miss : ¬ G.Adj q w) :
    ∃ i, (p ∈ C.leftVars i ∧ q ∉ C.leftVars i) ∨ (p ∈ C.rightVars i ∧ q ∉ C.rightVars i) := by
  apply distinguishInput C empty p q {q, w} (by simp)
  intro equal
  have on := (computes (insert p {q,w})).mpr ⟨p, by simp, w, by simp, adjacent⟩
  rw [equal] at on
  obtain ⟨a, ha, b, hb, edge⟩ := (computes {q,w}).mp on
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact G.loopless.irrefl _ edge
  · exact miss edge
  · exact miss edge.symm
  · exact G.loopless.irrefl _ edge

theorem readsOfSharedSide {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (computes : C.Computes G) (empty : C.outVars = ∅)
    (separate : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    {p q w : Fin n} (adjacent : G.Adj p w) (miss : ¬ G.Adj q w) (i : Fin C.size)
    (shared : (p ∈ C.leftVars i ∧ q ∈ C.leftVars i) ∨ (p ∈ C.rightVars i ∧ q ∈ C.rightVars i)) :
    2 ≤ {j : Fin C.size | p ∈ C.leftVars j ∨ p ∈ C.rightVars j}.ncard := by
  obtain ⟨j, other⟩ := separateRead C G computes empty adjacent miss
  have distinct : i ≠ j := by
    rintro rfl
    rcases shared with ⟨hl, ql⟩ | ⟨hr, qr⟩ <;> rcases other with ⟨jl, nq⟩ | ⟨jr, nq⟩
    · exact nq ql
    · exact Finset.disjoint_left.mp (separate i) hl jr
    · exact Finset.disjoint_left.mp (separate i) jl hr
    · exact nq qr
  let reads := Finset.univ.filter fun g : Fin C.size => p ∈ C.leftVars g ∨ p ∈ C.rightVars g
  have found : ({i, j} : Finset (Fin C.size)) ⊆ reads := by
    intro k mem
    rcases Finset.mem_insert.mp mem with rfl | eq
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, shared.imp And.left And.left⟩
    · rw [Finset.mem_singleton.mp eq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, other.imp And.left And.left⟩
  have repr : {g : Fin C.size | p ∈ C.leftVars g ∨ p ∈ C.rightVars g} = ↑reads := by
    ext g
    simp [reads]
  rw [repr, Set.ncard_coe_finset, ← Finset.card_pair distinct]
  exact Finset.card_le_card found

end AndCountCover

namespace PlaneMixedReadBounds

open PEqualNP.AndCount PlaneCoverReadSets

private theorem neighborMissedByOpposite {p q : Fin 42} (opposite : planeColor p ≠ planeColor q) :
    ∃ w, planeGraph.Adj p w ∧ ¬ planeGraph.Adj q w := by
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by rw [planeDegree]; decide :
    0 < (neighbors planeGraph.Adj p).card)
  have near := (Finset.mem_filter.mp hw).2
  have colors := planeBipartite p w near
  have same : planeColor q = planeColor w := by
    cases hp : planeColor p <;> cases hq : planeColor q <;> cases hw : planeColor w <;> simp_all
  exact ⟨w, near, fun e => planeBipartite q w e same⟩

def side (C : AndCountCircuit 42) : Fin C.size × Bool → Finset (Fin 42) :=
  operand C.leftVars C.rightVars

theorem twiceOnMixedSide (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (separate : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (j : Fin C.size × Bool) {p q : Fin 42} (opposite : planeColor p ≠ planeColor q)
    (hp : p ∈ side C j) (hq : q ∈ side C j) :
    2 ≤ {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i}.ncard := by
  obtain ⟨w, edge, miss⟩ := neighborMissedByOpposite opposite
  apply AndCountCover.readsOfSharedSide C planeGraph computes empty separate edge miss j.1
  obtain ⟨i, b⟩ := j
  cases b
  · exact Or.inr ⟨by simpa [side, operand] using hp, by simpa [side, operand] using hq⟩
  · exact Or.inl ⟨by simpa [side, operand] using hp, by simpa [side, operand] using hq⟩

set_option maxHeartbeats 1000000 in
theorem secondSideAtTwoReads (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (separate : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (j : Fin C.size × Bool) {p q : Fin 42} (opposite : planeColor p ≠ planeColor q)
    (pair : side C j = {p, q})
    (count : {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i}.ncard = 2) :
    ∃ k ≠ j, p ∈ side C k ∧ side C k ⊆ insert p (neighbors planeGraph.Adj q) := by
  let adjacent := planeGraph.Adj
  have symmetric : Std.Symm adjacent := ⟨fun _ _ e => e.symm⟩
  have repr : RealizesCovers adjacent (side C) :=
    operandsRealize C.leftVars C.rightVars
      (fun T min => PEqualNP.Outside.L_meta_8097 42 C planeGraph computes empty T min.1 min.2)
  obtain ⟨k, hasP, pure⟩ := pureSide adjacent planeColor symmetric planeBipartite (by decide)
    planeDegree planeThin (side C) repr p
  have hasQ : q ∈ side C j := by simp [pair]
  have qOut : q ∉ colorClass planeColor (planeColor p) := by
    simpa [colorClass] using opposite.symm
  have different : k ≠ j := fun eq => qOut (pure (eq.symm ▸ hasQ))
  let read := Reads (side C) p
  have card : read.card = 2 := (operandReads separate p).trans count
  have setEq : ({k, j} : Finset (Fin C.size × Bool)) = read := by
    apply Finset.eq_of_subset_of_card_le
    · intro i mem
      rcases Finset.mem_insert.mp mem with rfl | eq
      · simp [read, Reads, hasP]
      · rw [Finset.mem_singleton.mp eq]
        simp [read, Reads, pair]
    · rw [Finset.card_pair different, card]
  have contains (w : Fin 42) (near : adjacent p w) :
      side C k ⊆ sideCover adjacent planeColor (planeColor q) {q, w} := by
    have cw : planeColor w = planeColor q := by
      have hw := planeBipartite p w near
      cases hp : planeColor p <;> cases hq : planeColor q <;> cases hc : planeColor w <;> simp_all
    have colors : ({q, w} : Finset (Fin 42)) ⊆ colorClass planeColor (planeColor q) := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | singleton
      · simp [colorClass]
      · rw [Finset.mem_singleton.mp singleton]
        simp [colorClass, cw]
    have small : ({q, w} : Finset (Fin 42)).card < 5 := Finset.card_le_two.trans_lt (by decide)
    have min := smallSideCover adjacent planeColor symmetric planeBipartite planeDegree planeThin
      (planeColor q) {q, w} colors small
    have hp : p ∈ sideCover adjacent planeColor (planeColor q) {q, w} :=
      Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, by simp,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, near.symm⟩⟩)
    have hq : q ∉ sideCover adjacent planeColor (planeColor q) {q, w} := by
      intro mem
      rcases Finset.mem_union.mp mem with same | differentColor
      · exact (Finset.mem_sdiff.mp same).2 (by simp)
      · obtain ⟨v, hv, hit⟩ := Finset.mem_biUnion.mp differentColor
        exact planeBipartite v q (Finset.mem_filter.mp hit).2 (Finset.mem_filter.mp (colors hv)).2
    obtain ⟨i, hi, subset⟩ := repr _ min p hp
    have used : i ∈ read := by simp [read, Reads, hi]
    rw [← setEq] at used
    rcases Finset.mem_insert.mp used with rfl | eq
    · exact subset
    · exact (hq (subset ((Finset.mem_singleton.mp eq).symm ▸ hasQ))).elim
  refine ⟨k, different, hasP, ?_⟩
  intro x hx
  by_cases eq : x = p
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert.mpr
  right
  by_contra out
  have always (w : Fin 42) (hw : w ∈ neighbors adjacent p) : w ∈ neighbors adjacent x := by
    have near := (Finset.mem_filter.mp hw).2
    rcases Finset.mem_union.mp (contains w near hx) with same | halo
    · exact (opposite ((Finset.mem_filter.mp (pure hx)).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_sdiff.mp same).1).2)).elim
    · obtain ⟨v, hv, incident⟩ := Finset.mem_biUnion.mp halo
      rcases Finset.mem_insert.mp hv with rfl | hmem
      · exact (out incident).elim
      · have vw := Finset.mem_singleton.mp hmem
        subst v
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp incident).2.symm⟩
  have includes : neighbors adjacent p ⊆ neighbors adjacent p ∩ neighbors adjacent x :=
    fun w hw => Finset.mem_inter.mpr ⟨hw, always w hw⟩
  have le := (Finset.card_le_card includes).trans (planeThin p x (Ne.symm eq))
  rw [planeDegree] at le
  omega

set_option maxHeartbeats 4000000 in
theorem fourMixedSides (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (separate : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (size : C.size = 20)
    (readBound : ∀ v, {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard ≤ 4) :
    ∃ shared : Finset (Fin C.size × Bool),
      (shared : Set (Fin C.size × Bool)).PairwiseDisjoint (side C) ∧ 4 ≤ shared.card ∧
      ∀ j ∈ shared, (∃ p q, planeColor p ≠ planeColor q ∧ side C j = {p, q}) ∧
        ∀ v ∈ side C j, 2 ≤ {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard := by
  classical
  have chooseSides (k : ℕ) (A B : Fin k → Finset (Fin 42)) (count : k = 20)
      (sep : ∀ i, Disjoint (A i) (B i))
      (cap : ∀ v, {i : Fin k | v ∈ A i ∨ v ∈ B i}.ncard ≤ 4)
      (repr : ∀ T, MinimalCover planeGraph.Adj T → ∃ L R : Finset (Fin k),
        Disjoint L R ∧ L.biUnion A ∪ R.biUnion B = T) :
      ∃ shared : Finset (Fin k × Bool),
        shared ⊆ pairSides planeColor (fun j => if j.2 then A j.1 else B j.1) ∧
        (shared : Set (Fin k × Bool)).PairwiseDisjoint (fun j => if j.2 then A j.1 else B j.1) ∧
        4 ≤ shared.card := by
    subst k
    exact planeFourPairSides A B sep cap repr
  obtain ⟨shared, pair, disjoint, enough⟩ := chooseSides C.size C.leftVars C.rightVars size
    separate readBound (fun T min => PEqualNP.Outside.L_meta_8097 42 C planeGraph computes empty T min.1 min.2)
  change shared ⊆ pairSides planeColor (side C) at pair
  refine ⟨shared, disjoint, enough, fun j hj => ?_⟩
  have extent : ∃ p q, planeColor p ≠ planeColor q ∧ side C j = {p, q} := by
    simpa only [pairSides, Finset.mem_filter, Finset.mem_univ, true_and] using pair hj
  obtain ⟨p, q, opposite, eq⟩ := extent
  refine ⟨⟨p, q, opposite, eq⟩, ?_⟩
  have hp : p ∈ side C j := by simp [eq]
  have hq : q ∈ side C j := by simp [eq]
  intro v mem
  rw [eq] at mem
  rcases Finset.mem_insert.mp mem with rfl | h
  · exact twiceOnMixedSide C computes empty separate j opposite hp hq
  · rw [Finset.mem_singleton.mp h]
    exact twiceOnMixedSide C computes empty separate j opposite.symm hq hp

end PlaneMixedReadBounds

namespace AndCountTransfer

open PEqualNP.AndCount AndCountCircuit

def bareVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (left : Bool) : Finset (Fin n) :=
  if left then C.leftVars i else C.rightVars i

def sources {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (left : Bool) : Finset (Fin C.size) :=
  if left then C.leftGates i else C.rightGates i

def sideValue {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) (left : Bool) : Bool :=
  sideTrue U (bareVars C i left) (sources C i left) i (C.gateVal U)

private theorem onBoth {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = true ↔ ∀ left, sideValue C U i left = true := by
  rw [AndCountCover.gateEquation C U i, Bool.and_eq_true]
  constructor
  · intro h left
    cases left
    · exact h.2
    · exact h.1
  · intro h
    exact ⟨h true, h false⟩

theorem directlyOn {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (reads : ∀ left, ∃ v ∈ bareVars C i left, v ∈ U) : C.gateVal U i = true := by
  apply (onBoth C U i).mpr
  intro left
  exact decide_eq_true (Or.inl (reads left))

private theorem sideTransfer {n : ℕ} {C : AndCountCircuit n} {U W : Finset (Fin n)}
    {i : Fin C.size} {left : Bool}
    (bare : ∀ v ∈ bareVars C i left, v ∈ U → v ∈ W)
    (previous : ∀ k < i, C.gateVal U k = true → C.gateVal W k = true) :
    sideValue C U i left = true → sideValue C W i left = true := by
  simp only [sideValue, sideTrue, decide_eq_true_eq]
  rintro (⟨v, hv, mem⟩ | ⟨k, read, earlier, on⟩)
  · exact Or.inl ⟨v, hv, bare v hv mem⟩
  · exact Or.inr ⟨k, read, earlier, previous k earlier on⟩

theorem gatesBefore {n : ℕ} (C : AndCountCircuit n) (U W : Finset (Fin n)) (bound : ℕ)
    (step : ∀ i : Fin C.size, i.val < bound →
      (C.gateVal U i = true → C.gateVal W i = true) ∨
      ∀ left v, v ∈ bareVars C i left → v ∈ U → v ∈ W) :
    ∀ i : Fin C.size, i.val < bound → C.gateVal U i = true → C.gateVal W i = true := by
  intro i
  refine (wellFounded_lt (α := Fin C.size)).induction
    (C := fun j => j.val < bound → C.gateVal U j = true → C.gateVal W j = true) i ?_
  intro i ih less hot
  rcases step i less with known | bare
  · exact known hot
  · apply (onBoth C W i).mpr
    intro left
    exact sideTransfer (bare left) (fun k earlier => ih k earlier (Nat.lt_trans earlier less))
      ((onBoth C U i).mp hot left)

theorem outputFromTwo {n : ℕ} (C : AndCountCircuit n) (empty : C.outVars = ∅)
    (U W : Finset (Fin n)) (i k : Fin C.size)
    (only : ∀ j, j ≠ i → j ≠ k → ∀ left v, v ∈ bareVars C j left → v ∉ U)
    (a : C.gateVal U i = true → C.gateVal W i = true)
    (b : C.gateVal U k = true → C.gateVal W k = true)
    (on : C.eval U = true) : C.eval W = true := by
  have step (j : Fin C.size) (_ : j.val < C.size) :
      (C.gateVal U j = true → C.gateVal W j = true) ∨
      ∀ left v, v ∈ bareVars C j left → v ∈ U → v ∈ W := by
    by_cases same : j = i
    · subst j
      exact Or.inl a
    by_cases same' : j = k
    · subst j
      exact Or.inl b
    exact Or.inr fun left v hv inU => (only j same same' left v hv inU).elim
  simp only [eval, empty, Finset.notMem_empty, false_and, exists_false, false_or, decide_eq_true_eq] at on ⊢
  obtain ⟨j, read, hot⟩ := on
  exact ⟨j, read, gatesBefore C U W C.size step j j.isLt hot⟩

private theorem noneAtEmpty {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    C.gateVal ∅ i = false := by
  have off (d : ℕ) : ∀ j : Fin C.size, C.gateValFuel ∅ d j = false := by
    induction d with
    | zero => intro j; rfl
    | succ d ih => intro j; simp [gateValFuel, sideTrue, ih]
  exact off _ i

set_option maxHeartbeats 1000000 in
theorem forcedOperand {n : ℕ} (C : AndCountCircuit n) (empty : C.outVars = ∅)
    (U W : Finset (Fin n)) (i k : Fin C.size) (side : Bool)
    (only : ∀ j, j ≠ i → j ≠ k → ∀ left v, v ∈ bareVars C j left → v ∉ U)
    (silent : ∀ v ∈ bareVars C i side, v ∉ U)
    (positive : C.eval U = true) (negative : C.eval W = false) (cross : C.gateVal W k = true) :
    C.gateVal U i = true ∧ k < i ∧
      ∀ X, C.gateVal X k = true → sideValue C X i side = true := by
  have on : C.gateVal U i = true := by
    by_contra off
    have yes := outputFromTwo C empty U W i k only (fun h => (off h).elim) (fun _ => cross) positive
    rw [negative] at yes
    contradiction
  have operand := (onBoth C U i).mp on side
  have blocked (X : Finset (Fin n)) (backup : k < i → C.gateVal X k = true) :
      sideValue C X i side = true := by
    have step (j : Fin C.size) (early : j.val < i.val) :
        (C.gateVal U j = true → C.gateVal X j = true) ∨
        ∀ left v, v ∈ bareVars C j left → v ∈ U → v ∈ X := by
      by_cases eq : j = k
      · subst j
        exact Or.inl (fun _ => backup early)
      exact Or.inr (fun left v hv inU => (only j (ne_of_lt early) eq left v hv inU).elim)
    exact sideTransfer (fun v hv inU => (silent v hv inU).elim)
      (gatesBefore C U X i.val step) operand
  have earlier : k < i := by
    by_contra h
    have impossible := blocked ∅ (fun lt => (h lt).elim)
    simp [sideValue, sideTrue, noneAtEmpty] at impossible
  exact ⟨on, earlier, fun X hx => blocked X (fun _ => hx)⟩

private theorem gateMono {n : ℕ} (C : AndCountCircuit n) {U W : Finset (Fin n)}
    (sub : U ⊆ W) (i : Fin C.size) : C.gateVal U i = true → C.gateVal W i = true :=
  gatesBefore C U W C.size (fun _ _ => Or.inr (fun _ _ _ hit => sub hit)) i i.isLt

private theorem falseOnIndependentSides {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (computes : C.Computes G) (color : Fin n → Bool)
    (bipartite : ∀ v w, G.Adj v w → color v ≠ color w)
    (P L : Finset (Fin n)) (points : ∀ v ∈ P, color v = true) (lines : ∀ w ∈ L, color w = false)
    (miss : ∀ v ∈ P, ∀ w ∈ L, ¬ G.Adj v w) : C.eval (P ∪ L) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨v,hv,w,hw,adj⟩ := (computes _).mp h
  rcases Finset.mem_union.mp hv with hp | hl <;> rcases Finset.mem_union.mp hw with hq | hk
  · exact (bipartite v w adj) ((points v hp).trans (points w hq).symm)
  · exact miss v hp w hk adj
  · exact miss w hq v hl adj.symm
  · exact (bipartite v w adj) ((lines v hl).trans (lines w hk).symm)

set_option maxHeartbeats 2000000 in
theorem rectangleForSharedGate {n : ℕ} (C : AndCountCircuit n) (G : SimpleGraph (Fin n))
    (computes : C.Computes G) (empty : C.outVars = ∅) (color : Fin n → Bool)
    (bipartite : ∀ v w, G.Adj v w → color v ≠ color w)
    (A B P Q R S : Finset (Fin n)) (i k h : Fin C.size)
    (onlyA : ∀ j, j ≠ i → j ≠ k → ∀ left v, v ∈ bareVars C j left → v ∉ A)
    (onlyB : ∀ j, j ≠ i → j ≠ h → ∀ left v, v ∈ bareVars C j left → v ∉ B)
    (silentA : ∀ v ∈ bareVars C i false, v ∉ A) (silentB : ∀ v ∈ bareVars C i true, v ∉ B)
    (onA : C.eval A = true) (onB : C.eval B = true)
    (points : ∀ v ∈ P ∪ R, color v = true) (lines : ∀ w ∈ Q ∪ S, color w = false)
    (missA : ∀ v ∈ P, ∀ w ∈ Q, ¬ G.Adj v w) (missB : ∀ v ∈ R, ∀ w ∈ S, ¬ G.Adj v w)
    (crossA : ∀ v ∈ P, ∀ w ∈ Q, C.gateVal {v,w} k = true)
    (crossB : ∀ v ∈ R, ∀ w ∈ S, C.gateVal {v,w} h = true) :
    (∀ v ∈ P, ∀ w ∈ S, G.Adj v w) ∨ (∀ v ∈ R, ∀ w ∈ Q, G.Adj v w) := by
  by_contra! both
  obtain ⟨⟨p,hp,s,hs,noPS⟩,⟨r,hr,q,hq,noRQ⟩⟩ := both
  have pp := points p (Finset.mem_union_left _ hp)
  have pq := lines q (Finset.mem_union_left _ hq)
  have pr := points r (Finset.mem_union_right _ hr)
  have ps := lines s (Finset.mem_union_right _ hs)
  have offPQ : C.eval {p,q} = false := by
    rw [← Finset.singleton_union p {q}]
    apply falseOnIndependentSides C G computes color bipartite {p} {q}
    · simpa using pp
    · simpa using pq
    · simpa using missA p hp q hq
  have offRS : C.eval {r,s} = false := by
    rw [← Finset.singleton_union r {s}]
    apply falseOnIndependentSides C G computes color bipartite {r} {s}
    · simpa using pr
    · simpa using ps
    · simpa using missB r hr s hs
  have forceR := (forcedOperand C empty A {p,q} i k false onlyA silentA onA offPQ (crossA p hp q hq)).2.2
  have forceL := (forcedOperand C empty B {r,s} i h true onlyB silentB onB offRS (crossB r hr s hs)).2.2
  let U : Finset (Fin n) := {p,r} ∪ {q,s}
  have off : C.eval U = false := by
    apply falseOnIndependentSides C G computes color bipartite {p,r} {q,s}
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl <;> assumption
    · intro v hv w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact missA _ hp _ hq
      · exact noPS
      · exact noRQ
      · exact missB _ hr _ hs
  have kOn : C.gateVal U k = true := gateMono C (by simp [U, Finset.insert_subset_iff]) k (crossA p hp q hq)
  have hOn : C.gateVal U h = true := gateMono C (by simp [U, Finset.insert_subset_iff]) h (crossB r hr s hs)
  have iOn : C.gateVal U i = true := (onBoth C U i).mpr (fun b => by
    cases b
    · exact forceR U kOn
    · exact forceL U hOn)
  have output := outputFromTwo C empty A U i k onlyA (fun _ => iOn) (fun _ => kOn) onA
  rw [off] at output
  contradiction

end AndCountTransfer

namespace PlaneDoubleMixed

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PlaneCoverReadSets PlaneMixedReadBounds AndCountTransfer

private theorem readPositions (C : AndCountCircuit 42) (sep : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (v : Fin 42) (a b : Fin C.size × Bool) (different : a ≠ b)
    (av : v ∈ side C a) (bv : v ∈ side C b)
    (count : {i : Fin C.size | v ∈ C.leftVars i ∨ v ∈ C.rightVars i}.ncard = 2) :
    Reads (side C) v = {a,b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rcases Finset.mem_insert.mp hj with rfl | eq
    · simp [Reads,av]
    · rw [Finset.mem_singleton.mp eq]
      simp [Reads,bv]
  · change (Reads (operand C.leftVars C.rightVars) v).card ≤ _
    rw [operandReads sep, count, Finset.card_pair different]

private theorem sideAfter (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (sep : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    {p l : Fin 42} (inc : planeGraph.Adj p l) (s t : Fin C.size × Bool)
    (pair : side C s = {p,l}) (different : s ≠ t) (hit : p ∈ side C t)
    (count : {i : Fin C.size | p ∈ C.leftVars i ∨ p ∈ C.rightVars i}.ncard = 2) :
    side C t ⊆ neighbors planeGraph.Adj l := by
  have hp : p ∈ side C s := by simp [pair]
  have eq := readPositions C sep p s t different hp hit count
  obtain ⟨w, different', pw, sub⟩ := secondSideAtTwoReads C computes empty sep s (planeBipartite _ _ inc) pair count
  have hw : w ∈ Reads (side C) p := by simp [Reads,pw]
  rw [eq] at hw
  have wt : w = t := Finset.mem_singleton.mp ((Finset.mem_insert.mp hw).resolve_left different')
  rw [wt] at sub
  have near : p ∈ neighbors planeGraph.Adj l := Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc.symm⟩
  simpa [Finset.insert_eq_of_mem near] using sub

set_option maxHeartbeats 1000000 in
private theorem crossingAtTwo (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (sep : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (p l : Fin 42) (inc : planeGraph.Adj p l) (i : Fin C.size) (d : Bool)
    (pair : side C (i,d) = {p,l})
    (pCount : {j : Fin C.size | p ∈ C.leftVars j ∨ p ∈ C.rightVars j}.ncard = 2)
    (lCount : {j : Fin C.size | l ∈ C.leftVars j ∨ l ∈ C.rightVars j}.ncard = 2) :
    ∃ k : Fin C.size, ∃ b : Bool, k ≠ i ∧ p ∈ side C (k,b) ∧ l ∈ side C (k,!b) ∧
      side C (k,b) ⊆ neighbors planeGraph.Adj l ∧ side C (k,!b) ⊆ neighbors planeGraph.Adj p ∧
      ∀ j, j ≠ i → j ≠ k → ∀ a v, v ∈ bareVars C j a → v ∉ ({p,l} : Finset (Fin 42)) := by
  obtain ⟨k, crossing⟩ := PEqualNP.Outside.L_meta_8099 42 C planeGraph computes empty sep p l inc
  have chooseSide : ∃ b, p ∈ side C (k,b) ∧ l ∈ side C (k,!b) := by
    rcases crossing with sideL | sideR
    · exact ⟨true,sideL⟩
    · exact ⟨false,sideR.2,sideR.1⟩
  obtain ⟨b,hp,hl⟩ := chooseSide
  have hp₀ : p ∈ side C (i,d) := by simp [pair]
  have hl₀ : l ∈ side C (i,d) := by simp [pair]
  have ne : k ≠ i := by
    intro equal
    subst k
    cases b <;> cases d <;> simp [side, operand] at hp hl hp₀ hl₀
    · exact Finset.disjoint_left.mp (sep i) hl hl₀
    · exact Finset.disjoint_left.mp (sep i) hp₀ hp
    · exact Finset.disjoint_left.mp (sep i) hp hp₀
    · exact Finset.disjoint_left.mp (sep i) hl₀ hl
  have separateSlots (v : Bool) : (i,d) ≠ (k,v) := fun eq => ne (congrArg Prod.fst eq).symm
  have pAfter := sideAfter C computes empty sep inc (i,d) (k,b) pair (separateSlots b) hp pCount
  have lPair : side C (i,d) = {l,p} := by rw [pair, Finset.pair_comm]
  have lAfter := sideAfter C computes empty sep inc.symm (i,d) (k,!b) lPair (separateSlots (!b)) hl lCount
  have pReads := readPositions C sep p (i,d) (k,b) (separateSlots b) hp₀ hp pCount
  have lReads := readPositions C sep l (i,d) (k,!b) (separateSlots (!b)) hl₀ hl lCount
  refine ⟨k,b,ne,hp,hl,pAfter,lAfter,fun j different other a v hit mem => ?_⟩
  have excludes (t : Fin 42) (f : Bool) (ev : Reads (side C) t = {(i,d),(k,f)})
      (h : t ∈ side C (j,a)) : False := by
    have used : (j,a) ∈ Reads (side C) t := by simp [Reads,h]
    rw [ev, Finset.mem_insert, Finset.mem_singleton] at used
    exact used.elim (fun eq => different (congrArg Prod.fst eq)) (fun eq => other (congrArg Prod.fst eq))
  rcases Finset.mem_insert.mp mem with eq | one
  · subst v
    exact excludes p b pReads hit
  · have eq := Finset.mem_singleton.mp one
    subst v
    exact excludes l (!b) lReads hit

private theorem noSquare (P Q : Finset (Fin 42)) (pc : 1 < P.card) (qc : 1 < Q.card)
    (complete : ∀ p ∈ P, ∀ l ∈ Q, planeGraph.Adj p l) : False := by
  obtain ⟨p,q,hp,hq,ne⟩ := Finset.one_lt_card_iff.mp pc
  obtain ⟨l,m,hl,hm,diff⟩ := Finset.one_lt_card_iff.mp qc
  have common (z) (hz : z ∈ Q) : z ∈ neighbors planeGraph.Adj p ∩ neighbors planeGraph.Adj q := by
    simp [neighbors, complete p hp z hz, complete q hq z hz]
  exact diff (Finset.card_le_one.mp (planeThin p q ne) l (common l hl) m (common m hm))

private theorem oppositeHalo {p l x y : Fin 42} (inc : planeGraph.Adj p l)
    (xp : x ≠ p) (yl : y ≠ l) (xl : x ∈ neighbors planeGraph.Adj l)
    (yp : y ∈ neighbors planeGraph.Adj p) : ¬ planeGraph.Adj x y := by
  intro bad
  have nearL : l ∈ neighbors planeGraph.Adj p ∩ neighbors planeGraph.Adj x := by
    simp [neighbors, inc, (Finset.mem_filter.mp xl).2.symm]
  have nearY : y ∈ neighbors planeGraph.Adj p ∩ neighbors planeGraph.Adj x := by
    simp [neighbors, (Finset.mem_filter.mp yp).2, bad]
  exact yl (Finset.card_le_one.mp (planeThin p x xp.symm) y nearY l nearL)

set_option maxHeartbeats 3000000 in
theorem shortSecondOperand (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (sep : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (p l q m : Fin 42) (i : Fin C.size)
    (pPoint : planeColor p = true) (lLine : planeColor l = false)
    (qPoint : planeColor q = true) (mLine : planeColor m = false)
    (incA : planeGraph.Adj p l) (incB : planeGraph.Adj q m)
    (left : C.leftVars i = {p,l}) (right : C.rightVars i = {q,m})
    (twice : ∀ v ∈ ({p,l,q,m} : Finset (Fin 42)),
      {j : Fin C.size | v ∈ C.leftVars j ∨ v ∈ C.rightVars j}.ncard = 2) :
    ∃ s : Fin C.size × Bool, s.1 ≠ i ∧ (side C s).card ≤ 2 ∧
      ((side C s) ∩ {p,l,q,m}).Nonempty := by
  obtain ⟨k,b,kne,hp,hl,Ap,Al,onlyA⟩ := crossingAtTwo C computes empty sep p l incA i true left
    (twice p (by simp)) (twice l (by simp))
  obtain ⟨h,c,hne,hq,hm,Bq,Bm,onlyB⟩ := crossingAtTwo C computes empty sep q m incB i false right
    (twice q (by simp)) (twice m (by simp))
  by_contra noShort
  have long (j : Fin C.size) (d : Bool) (v : Fin 42) (neq : j ≠ i)
      (hit : v ∈ side C (j,d)) (four : v ∈ ({p,l,q,m} : Finset (Fin 42))) :
      1 < ((side C (j,d)).erase v).card := by
    have ht : ¬ (side C (j,d)).card ≤ 2 := fun hc => noShort
      ⟨(j,d),neq,hc,v,Finset.mem_inter.mpr ⟨hit,four⟩⟩
    have eq := Finset.card_erase_add_one hit
    omega
  let P := (side C (k,b)).erase p
  let L := (side C (k,!b)).erase l
  let Q := (side C (h,c)).erase q
  let M := (side C (h,!c)).erase m
  have pLarge : 1 < P.card := long k b p kne hp (by simp)
  have lLarge : 1 < L.card := long k (!b) l kne hl (by simp)
  have qLarge : 1 < Q.card := long h c q hne hq (by simp)
  have mLarge : 1 < M.card := long h (!c) m hne hm (by simp)
  have colorNear {v w : Fin 42} {d : Bool} (eq : planeColor v = d)
      (near : w ∈ neighbors planeGraph.Adj v) : planeColor w = !d := by
    have different := planeBipartite v w (Finset.mem_filter.mp near).2
    rw [eq] at different
    cases d <;> cases hw : planeColor w <;> simp_all
  have colorP (x : Fin 42) (mem : x ∈ P ∪ Q) : planeColor x = true := by
    rcases Finset.mem_union.mp mem with hx | hx
    · exact colorNear lLine (Ap (Finset.mem_erase.mp hx).2)
    · exact colorNear mLine (Bq (Finset.mem_erase.mp hx).2)
  have colorL (y : Fin 42) (mem : y ∈ L ∪ M) : planeColor y = false := by
    rcases Finset.mem_union.mp mem with hy | hy
    · exact colorNear pPoint (Al (Finset.mem_erase.mp hy).2)
    · exact colorNear qPoint (Bm (Finset.mem_erase.mp hy).2)
  have silence (d : Bool) (v : Fin 42) (hv : v ∈ bareVars C i (!d)) : v ∉ bareVars C i d := by
    intro h
    cases d
    · exact Finset.disjoint_left.mp (sep i) hv h
    · exact Finset.disjoint_left.mp (sep i) h hv
  have cross (j : Fin C.size) (d : Bool) {v w : Fin 42}
      (x : v ∈ side C (j,d)) (y : w ∈ side C (j,!d)) : C.gateVal {v,w} j = true := by
    apply directlyOn
    intro a
    cases d <;> cases a
    · exact ⟨v,x,by simp⟩
    · exact ⟨w,y,by simp⟩
    · exact ⟨w,y,by simp⟩
    · exact ⟨v,x,by simp⟩
  have rect := rectangleForSharedGate C planeGraph computes empty planeColor planeBipartite
    {p,l} {q,m} P L Q M i k h onlyA onlyB
    (fun v hv hit => silence true v hv (show v ∈ C.leftVars i from left.symm ▸ hit))
    (fun v hv hit => silence false v hv (show v ∈ C.rightVars i from right.symm ▸ hit))
    ((computes _).mpr ⟨p,by simp,l,by simp,incA⟩)
    ((computes _).mpr ⟨q,by simp,m,by simp,incB⟩) colorP colorL
    (fun _ hx _ hy => oppositeHalo incA (Finset.mem_erase.mp hx).1 (Finset.mem_erase.mp hy).1
      (Ap (Finset.mem_erase.mp hx).2) (Al (Finset.mem_erase.mp hy).2))
    (fun _ hx _ hy => oppositeHalo incB (Finset.mem_erase.mp hx).1 (Finset.mem_erase.mp hy).1
      (Bq (Finset.mem_erase.mp hx).2) (Bm (Finset.mem_erase.mp hy).2))
    (fun _ hx _ hy => cross k b (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hy).2)
    (fun _ hx _ hy => cross h c (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hy).2)
  exact rect.elim (noSquare P M pLarge mLarge) (noSquare Q L qLarge lLarge)

end PlaneDoubleMixed
