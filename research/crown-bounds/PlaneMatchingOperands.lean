import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Finite

-- Uses the accepted cover representation of L-meta-8097.

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

namespace PlaneMatchingExtension

open PlaneCoverReadSets
open scoped BigOperators

abbrev V := Fin 42

def halo (S : Finset V) : Finset V := S.biUnion (neighbors planeGraph.Adj)

private def entry (p l : V) : ℕ := if planeGraph.Adj p l then 1 else 0

private theorem firstMoment (S : Finset V) :
    (∑ l ∈ halo S, ∑ p ∈ S, entry p l) = 5 * S.card := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ _p ∈ S, 5 := by
      apply Finset.sum_congr rfl
      intro p hp
      have eq : (halo S).filter (planeGraph.Adj p) = neighbors planeGraph.Adj p := by
        ext l
        simp only [Finset.mem_filter, neighbors, Finset.mem_univ, true_and]
        exact ⟨And.right, fun near => ⟨Finset.mem_biUnion.mpr
          ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, near⟩⟩, near⟩⟩
      simp only [entry, Finset.sum_boole, Nat.cast_id, eq, planeDegree]
    _ = _ := by simp [Nat.mul_comm]

private theorem secondMoment (S : Finset V) :
    (∑ l ∈ halo S, (∑ p ∈ S, entry p l) ^ 2) ≤ S.card * (S.card + 4) := by
  have swap (p : V) : (∑ l ∈ halo S, ∑ q ∈ S, entry p l * entry q l) =
      ∑ q ∈ S, ∑ l ∈ halo S, entry p l * entry q l := Finset.sum_comm
  have count (p q : V) :
      (∑ l ∈ halo S, entry p l * entry q l) ≤ if p = q then 5 else 1 := by
    have terms (l : V) : entry p l * entry q l = if planeGraph.Adj p l ∧ planeGraph.Adj q l then 1 else 0 := by
      by_cases h₁ : planeGraph.Adj p l <;> by_cases h₂ : planeGraph.Adj q l <;> simp [entry, h₁, h₂]
    simp_rw [terms]
    rw [Finset.sum_boole]
    have incl : ((halo S).filter fun l => planeGraph.Adj p l ∧ planeGraph.Adj q l) ⊆
        neighbors planeGraph.Adj p ∩ neighbors planeGraph.Adj q := by
      intro l hl
      have h := (Finset.mem_filter.mp hl).2
      simpa [neighbors] using h
    apply (Finset.card_le_card incl).trans
    by_cases equal : p = q
    · subst q
      simp [planeDegree]
    · simpa [equal] using planeThin p q equal
  calc
    _ = ∑ l ∈ halo S, ∑ p ∈ S, ∑ q ∈ S, entry p l * entry q l := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact Nat.mul_comm _ _
    _ = ∑ p ∈ S, ∑ q ∈ S, ∑ l ∈ halo S, entry p l * entry q l := by
      rw [Finset.sum_comm]
      simp only [swap]
    _ ≤ ∑ p ∈ S, ∑ q ∈ S, if p = q then 5 else 1 :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => count p q
    _ = _ := by
      have inner (p : V) (hp : p ∈ S) : (∑ q ∈ S, if p = q then 5 else 1) = S.card + 4 := by
        simp_rw [show ∀ q : V, (if p = q then 5 else 1 : ℕ) = 1 + if q = p then 4 else 0 by
          intro q
          by_cases h : p = q <;> simp [h, eq_comm]]
        simp [Finset.sum_add_distrib, hp]
      rw [Finset.sum_congr rfl inner]
      simp

private theorem finiteGap : ∀ k : Fin 18, 0 < k.val →
    (k.val + 3) * (k.val * (k.val + 4)) < (5*k.val)^2 := by
  decide +kernel

theorem smallSetExpansion (S : Finset V) (positive : S.Nonempty) (small : S.card ≤ 17) :
    S.card + 4 ≤ (halo S).card := by
  have cauchy : (∑ l ∈ halo S, ∑ p ∈ S, entry p l) ^ 2 ≤
      (halo S).card * ∑ l ∈ halo S, (∑ p ∈ S, entry p l) ^ 2 := by
    simpa using (Finset.sum_mul_sq_le_sq_mul_sq (halo S) (fun _ => (1 : ℕ))
      (fun l => ∑ p ∈ S, entry p l))
  rw [firstMoment S] at cauchy
  have bound := cauchy.trans (Nat.mul_le_mul_left _ (secondMoment S))
  by_contra! bad
  have le : (halo S).card ≤ S.card + 3 := by omega
  have below := Nat.mul_le_mul_right (S.card*(S.card+4)) le
  have above := finiteGap ⟨S.card, by omega⟩ (Finset.card_pos.mpr positive)
  exact (not_le_of_gt above) (bound.trans below)

def points : Finset V := colorClass planeColor true
def lines : Finset V := colorClass planeColor false

private theorem pointsCard : points.card = 21 := by decide +kernel
private theorem linesCard : lines.card = 21 := by decide +kernel

private theorem pointOrLine (p : V) : p ∈ points ↔ p ∉ lines := by
  cases h : planeColor p <;> simp [points, lines, colorClass, h]

private theorem edgeFromPoint {p l : V} (pos : p ∈ points) (inc : planeGraph.Adj p l) : l ∈ lines := by
  have h := (Finset.mem_filter.mp pos).2
  have other := planeBipartite p l inc
  rw [h] at other
  simpa [lines, colorClass] using Ne.symm other

set_option maxHeartbeats 1000000 in
theorem matchAfterFour (P L : Finset V) (pts : P ⊆ points) (lns : L ⊆ lines)
    (pc : P.card = 4) (lc : L.card = 4) :
    ∃ m : {p // p ∈ points \ P} ≃ {l // l ∈ lines \ L},
      ∀ p, planeGraph.Adj p.val (m p).val := by
  let Q := points \ P
  let R := lines \ L
  have qCard : Q.card = 17 := by simp [Q, Finset.card_sdiff_of_subset pts, pointsCard, pc]
  have rCard : R.card = 17 := by simp [R, Finset.card_sdiff_of_subset lns, linesCard, lc]
  let possible (p : {v // v ∈ Q}) := neighbors planeGraph.Adj p.val \ L
  have hall (A : Finset {p // p ∈ Q}) : A.card ≤ (A.biUnion possible).card := by
    by_cases empty : A = ∅
    · simp [empty]
    let S := A.image Subtype.val
    have sCard : S.card = A.card := Finset.card_image_of_injective A Subtype.val_injective
    have age : A.card ≤ 17 := by
      simpa only [Fintype.card_coe, qCard] using Finset.card_le_univ A
    have ns : S.Nonempty := (Finset.nonempty_iff_ne_empty.mpr empty).image _
    have many := smallSetExpansion S ns (sCard.symm ▸ age)
    have le := Finset.card_le_card_sdiff_add_card (s := halo S) (t := L)
    have eq : A.biUnion possible = halo S \ L := by
      ext l
      simp only [Finset.mem_biUnion, possible, Finset.mem_sdiff, halo, S, Finset.mem_image]
      constructor
      · rintro ⟨p, pA, near, fresh⟩
        exact ⟨⟨p.val, ⟨p, pA, rfl⟩, near⟩, fresh⟩
      · rintro ⟨⟨p, ⟨u, uA, rfl⟩, near⟩, fresh⟩
        exact ⟨u, uA, near, fresh⟩
    rw [eq]
    omega
  obtain ⟨f, inj, ok⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' possible).mp hall
  have near (p : {v // v ∈ Q}) : planeGraph.Adj p.val (f p) :=
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp (ok p)).1).2
  let g (p : {v // v ∈ Q}) : {v // v ∈ R} := ⟨f p,
    Finset.mem_sdiff.mpr ⟨edgeFromPoint (Finset.mem_sdiff.mp p.property).1 (near p),
      (Finset.mem_sdiff.mp (ok p)).2⟩⟩
  have bij : Function.Bijective g := by
    apply (Fintype.bijective_iff_injective_and_card g).mpr
    exact ⟨fun _ _ h => inj (congrArg Subtype.val h), by simp [qCard, rCard]⟩
  exact ⟨Equiv.ofBijective g bij, near⟩

set_option maxHeartbeats 1000000 in
theorem extendMatching (P L : Finset V) (pts : P ⊆ points) (lns : L ⊆ lines)
    (pc : P.card = 4) (lc : L.card = 4) (given : {p // p ∈ P} ≃ {l // l ∈ L})
    (edges : ∀ p, planeGraph.Adj p.val (given p).val) :
    ∃ mate : V → V, Function.Involutive mate ∧ (∀ v, planeGraph.Adj v (mate v)) ∧
      ∀ p : {v // v ∈ P}, mate p.val = (given p).val := by
  obtain ⟨free, freeEdges⟩ := matchAfterFour P L pts lns pc lc
  let all (p : {v // v ∈ points}) : {v // v ∈ lines} :=
    if h : p.val ∈ P then ⟨(given ⟨p.val,h⟩).val, lns (given ⟨p.val,h⟩).property⟩
    else ⟨(free ⟨p.val, Finset.mem_sdiff.mpr ⟨p.property,h⟩⟩).val,
      (Finset.mem_sdiff.mp (free ⟨p.val, Finset.mem_sdiff.mpr ⟨p.property,h⟩⟩).property).1⟩
  have agreement (p : {v // v ∈ points}) : (all p).val ∈ L ↔ p.val ∈ P := by
    by_cases hp : p.val ∈ P
    · simpa [all, hp] using (given ⟨p.val,hp⟩).property
    · simpa [all, hp] using (Finset.mem_sdiff.mp (free ⟨p.val,
        Finset.mem_sdiff.mpr ⟨p.property,hp⟩⟩).property).2
  have inj : Function.Injective all := by
    intro p q eq
    have same : p.val ∈ P ↔ q.val ∈ P := (agreement p).symm.trans (eq ▸ agreement q)
    have vals := congrArg Subtype.val eq
    apply Subtype.ext
    by_cases hp : p.val ∈ P
    · have hq := same.mp hp
      have hit : given ⟨p.val,hp⟩ = given ⟨q.val,hq⟩ := Subtype.ext (by simpa [all,hp,hq] using vals)
      exact congrArg (fun v : {x // x ∈ P} => v.val) (given.injective hit)
    · have hq : q.val ∉ P := fun e => hp (same.mpr e)
      have hit : free ⟨p.val, Finset.mem_sdiff.mpr ⟨p.property,hp⟩⟩ =
          free ⟨q.val, Finset.mem_sdiff.mpr ⟨q.property,hq⟩⟩ :=
        Subtype.ext (by simpa only [all, dite_eq_right hp, dite_eq_right hq] using vals)
      exact congrArg (fun v : {x // x ∈ points \ P} => v.val) (free.injective hit)
  have bij : Function.Bijective all := (Fintype.bijective_iff_injective_and_card all).mpr
    ⟨inj, by simp [pointsCard, linesCard]⟩
  let full := Equiv.ofBijective all bij
  have adj (p : {v // v ∈ points}) : planeGraph.Adj p.val (full p).val := by
    change planeGraph.Adj p.val (all p).val
    dsimp only [all]
    split
    · rename_i h
      exact edges ⟨p.val,h⟩
    · rename_i h
      exact freeEdges ⟨p.val,Finset.mem_sdiff.mpr ⟨p.property,h⟩⟩
  have inLines {v : V} (h : v ∉ points) : v ∈ lines := by
    by_contra bad
    exact h ((pointOrLine v).mpr bad)
  let mate (v : V) : V := if h : v ∈ points then (full ⟨v,h⟩).val else
    (full.symm ⟨v,inLines h⟩).val
  have matePoint (p : {v // v ∈ points}) : mate p.val = (full p).val := by
    simp [mate, p.property]
  have mateLine (l : {v // v ∈ lines}) : mate l.val = (full.symm l).val := by
    have absent : l.val ∉ points := fun h => (pointOrLine _).mp h l.property
    simp [mate, absent]
  refine ⟨mate, ?_, ?_, ?_⟩
  · intro v
    by_cases h : v ∈ points
    · rw [matePoint ⟨v,h⟩, mateLine (full ⟨v,h⟩), Equiv.symm_apply_apply]
    · rw [mateLine ⟨v,inLines h⟩, matePoint (full.symm ⟨v,inLines h⟩), Equiv.apply_symm_apply]
  · intro v
    by_cases h : v ∈ points
    · rw [matePoint ⟨v,h⟩]
      exact adj ⟨v,h⟩
    · let l : {v // v ∈ lines} := ⟨v,inLines h⟩
      have edge := (adj (full.symm l)).symm
      rw [Equiv.apply_symm_apply] at edge
      rw [mateLine l]
      exact edge
  · intro p
    rw [matePoint ⟨p.val, pts p.property⟩]
    change (all ⟨p.val, pts p.property⟩).val = (given p).val
    simp [all, p.property]

end PlaneMatchingExtension

namespace PlaneMatchingOperands

open PlaneCoverReadSets PlaneMatchingExtension
open scoped BigOperators

private def cover (mate : V → V) (v : V) : Finset V :=
  sideCover planeGraph.Adj planeColor (planeColor (mate v)) {mate v}

private theorem includesVertex {mate : V → V} {v : V} (near : planeGraph.Adj v (mate v)) :
    v ∈ cover mate v := by
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨mate v, by simp,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, near.symm⟩⟩)

private theorem excludesMate (mate : V → V) (v : V) : mate v ∉ cover mate v := by
  intro hit
  rcases Finset.mem_union.mp hit with h | h
  · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_singleton_self _)
  · obtain ⟨w, hw, near⟩ := Finset.mem_biUnion.mp h
    have equal := Finset.mem_singleton.mp hw
    exact planeGraph.loopless.irrefl _ (equal ▸ (Finset.mem_filter.mp near).2)

private theorem oppositeCoverMembers {mate : V → V} {v w : V}
    (other : planeColor w ≠ planeColor (mate v)) (mem : w ∈ cover mate v) :
    w ∈ neighbors planeGraph.Adj (mate v) := by
  rcases Finset.mem_union.mp mem with h | h
  · exact (other (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2).elim
  · simpa only [Finset.singleton_biUnion] using h

noncomputable def mixedOperands {J : Type} [Fintype J] [DecidableEq J] (sides : J → Finset V) : Finset J := by
  classical
  exact Finset.univ.filter fun s => ∃ p ∈ sides s, ∃ l ∈ sides s, planeColor p ≠ planeColor l

set_option maxHeartbeats 2000000 in
theorem tenMixedOperands {J : Type} [Fintype J] [DecidableEq J] (sides : J → Finset V)
    (slots : Fintype.card J = 40) (represents : RealizesCovers planeGraph.Adj sides)
    (mate : V → V) (inv : Function.Involutive mate) (edges : ∀ v, planeGraph.Adj v (mate v))
    (reserved : Finset J) (four : reserved.card = 4)
    (reserves : ∀ s ∈ reserved, ∃ p, sides s = {p, mate p}) :
    10 ≤ (mixedOperands sides).card := by
  classical
  have symm : Std.Symm planeGraph.Adj := ⟨fun _ _ h => h.symm⟩
  have choice (v : V) : ∃ s, v ∈ sides s ∧ sides s ⊆ cover mate v := by
    have m := smallSideCover planeGraph.Adj planeColor symm planeBipartite planeDegree planeThin
      (planeColor (mate v)) {mate v} (by simp [colorClass]) (by simp)
    exact represents _ m v (includesVertex (edges v))
  choose pick facts using choice
  let available := (Finset.univ : Finset J) \ reserved
  have availablePick (v : V) : pick v ∈ available := by
    apply Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
    intro used
    obtain ⟨p, eq⟩ := reserves (pick v) used
    have atSide := eq ▸ (facts v).1
    have includes : mate v ∈ sides (pick v) := by
      rw [eq]
      rcases Finset.mem_insert.mp atSide with rfl | h
      · simp
      · rw [Finset.mem_singleton.mp h, inv p]
        simp
    exact excludesMate mate v ((facts v).2 includes)
  have injectionOnColor {v w : V} (sameSide : pick v = pick w) (sameColor : planeColor v = planeColor w) :
      v = w := by
    by_contra distinct
    have mv := planeBipartite v (mate v) (edges v)
    have mw := planeBipartite w (mate w) (edges w)
    have crossV : planeColor v ≠ planeColor (mate w) := fun h => mw (sameColor.symm.trans h)
    have crossW : planeColor w ≠ planeColor (mate v) := fun h => mv (sameColor.trans h)
    have nv : v ∈ neighbors planeGraph.Adj (mate v) ∩ neighbors planeGraph.Adj (mate w) := by
      refine Finset.mem_inter.mpr ⟨oppositeCoverMembers mv (includesVertex (edges v)), ?_⟩
      exact oppositeCoverMembers crossV ((facts w).2 (sameSide ▸ (facts v).1))
    have nw : w ∈ neighbors planeGraph.Adj (mate v) ∩ neighbors planeGraph.Adj (mate w) := by
      refine Finset.mem_inter.mpr ⟨?_, oppositeCoverMembers mw (includesVertex (edges w))⟩
      exact oppositeCoverMembers crossW ((facts v).2 (sameSide.symm ▸ (facts w).1))
    exact distinct (Finset.card_le_one.mp (planeThin _ _ (fun eq => distinct (inv.injective eq))) v nv w nw)
  let fiber (s : J) := Finset.univ.filter fun v => pick v = s
  have fiberCap (s : J) : (fiber s).card ≤ 2 := by
    have colorInj : Set.InjOn planeColor ↑(fiber s) := by
      intro v hv w hw eq
      exact injectionOnColor ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) eq
    rw [← Finset.card_image_of_injOn colorInj]
    simpa using Finset.card_le_univ ((fiber s).image planeColor)
  let shared := available.filter fun s => 1 < (fiber s).card
  have all := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V) available pick
  simp only [availablePick, Finset.filter_true, Finset.card_univ, Fintype.card_fin] at all
  have cap : 42 ≤ available.card + shared.card := calc
    _ = ∑ s ∈ available, (fiber s).card := all.symm
    _ ≤ ∑ s ∈ available, (1 + if 1 < (fiber s).card then 1 else 0) := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs with h
      · exact fiberCap s
      · omega
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [shared]
  have remaining : available.card + reserved.card = 40 := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ reserved)
    simpa [available, slots] using h
  have mixedReserved : reserved ⊆ mixedOperands sides := by
    intro s hs
    obtain ⟨p, eq⟩ := reserves s hs
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, p, by simp [eq], mate p, by simp [eq], planeBipartite _ _ (edges p)⟩
  have mixedShared : shared ⊆ mixedOperands sides := by
    intro s hs
    obtain ⟨v, w, hv, hw, ne⟩ := Finset.one_lt_card_iff.mp (Finset.mem_filter.mp hs).2
    have vAt := (Finset.mem_filter.mp hv).2
    have wAt := (Finset.mem_filter.mp hw).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, vAt ▸ (facts v).1, w, wAt ▸ (facts w).1, ?_⟩
    exact fun eq => ne (injectionOnColor (vAt.trans wAt.symm) eq)
  have sep : Disjoint shared reserved := Finset.disjoint_left.mpr fun s hs =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hs).1).2
  have n := Finset.card_le_card (Finset.union_subset mixedShared mixedReserved)
  rw [Finset.card_union_of_disjoint sep] at n
  omega

set_option maxHeartbeats 2000000 in
theorem tenFromFourDisjoint {J : Type} [Fintype J] [DecidableEq J] (sides : J → Finset V)
    (slots : Fintype.card J = 40) (represents : RealizesCovers planeGraph.Adj sides)
    (reserved : Finset J) (four : reserved.card = 4)
    (pairs : ∀ s ∈ reserved, ∃ v w, planeGraph.Adj v w ∧ sides s = {v, w})
    (sep : (reserved : Set J).PairwiseDisjoint sides) :
    10 ≤ (mixedOperands sides).card := by
  classical
  have orient (s : {j // j ∈ reserved}) : ∃ p ∈ points, ∃ l ∈ lines,
      planeGraph.Adj p l ∧ sides s.val = {p, l} := by
    obtain ⟨v,w,edge,eq⟩ := pairs s.val s.property
    by_cases hp : v ∈ points
    · exact ⟨v,hp,w,edgeFromPoint hp edge,edge,eq⟩
    · have iv : v ∈ lines := by
        by_contra hn
        exact hp ((pointOrLine v).mpr hn)
      have wp : w ∈ points := by
        by_contra hw
        have wl : w ∈ lines := by
          by_contra hn
          exact hw ((pointOrLine w).mpr hn)
        exact planeBipartite v w edge ((Finset.mem_filter.mp iv).2.trans (Finset.mem_filter.mp wl).2.symm)
      exact ⟨w,wp,v,iv,edge.symm,by simpa [Finset.pair_comm] using eq⟩
  choose p op l ol edge listed using orient
  have alone (f : {j // j ∈ reserved} → V) (mem : ∀ s, f s ∈ sides s.val) : Function.Injective f := by
    intro s t eq
    apply Subtype.ext
    by_contra different
    exact Finset.disjoint_left.mp (sep s.property t.property different) (mem s) (eq.symm ▸ mem t)
  let embeds (f : {j // j ∈ reserved} → V) (inj : Function.Injective f) :
      {j // j ∈ reserved} ≃ {v // v ∈ Finset.univ.image f} :=
    Equiv.ofBijective (fun s => ⟨f s, Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩⟩)
      ⟨fun _ _ e => inj (congrArg Subtype.val e), fun v => by
        obtain ⟨s,_,eq⟩ := Finset.mem_image.mp v.property
        exact ⟨s,Subtype.ext eq⟩⟩
  let P := Finset.univ.image p
  let L := Finset.univ.image l
  have pinj := alone p (fun s => by simp [listed s])
  have linj := alone l (fun s => by simp [listed s])
  have pt : P ⊆ points := by
    intro v hv
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hv
    exact op s
  have line : L ⊆ lines := by
    intro v hv
    obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp hv
    exact ol s
  have pc : P.card = 4 := by
    simp [P, Finset.card_image_of_injective _ pinj, four]
  have lc : L.card = 4 := by
    simp [L, Finset.card_image_of_injective _ linj, four]
  let pe := embeds p pinj
  let le := embeds l linj
  let given := pe.symm.trans le
  have vals (s : {j // j ∈ reserved}) : (pe s).val = p s := rfl
  have valueL (s : {j // j ∈ reserved}) : (le s).val = l s := rfl
  have assigns : ∀ v : {v // v ∈ P}, planeGraph.Adj v.val (given v).val := by
    intro v
    have eq : p (pe.symm v) = v.val := (vals (pe.symm v)).symm.trans (congrArg Subtype.val (pe.apply_symm_apply v))
    rw [← eq]
    exact edge (pe.symm v)
  obtain ⟨mate,inv,edges,takes⟩ := extendMatching P L pt line pc lc given assigns
  apply tenMixedOperands sides slots represents mate inv edges reserved four
  intro s hs
  let x : {j // j ∈ reserved} := ⟨s,hs⟩
  refine ⟨p x, ?_⟩
  have hit := takes (pe x)
  change mate (p x) = (le (pe.symm (pe x))).val at hit
  rw [Equiv.symm_apply_apply, valueL] at hit
  rw [hit]
  exact listed x

open PEqualNP.AndCount

theorem tenForCircuit (C : AndCountCircuit 42) (computes : C.Computes planeGraph)
    (empty : C.outVars = ∅) (size : C.size = 20)
    (reserved : Finset (Fin C.size × Bool)) (four : 4 ≤ reserved.card)
    (pairs : ∀ s ∈ reserved, ∃ v w, planeGraph.Adj v w ∧ operand C.leftVars C.rightVars s = {v, w})
    (sep : (reserved : Set (Fin C.size × Bool)).PairwiseDisjoint (operand C.leftVars C.rightVars)) :
    10 ≤ (mixedOperands (operand C.leftVars C.rightVars)).card := by
  have realizes := operandsRealize C.leftVars C.rightVars
    (fun T min => PEqualNP.Outside.L_meta_8097 42 C planeGraph computes empty T min.1 min.2)
  obtain ⟨S, sub, count⟩ := Finset.exists_subset_card_eq four
  exact tenFromFourDisjoint (operand C.leftVars C.rightVars) (by simp [size]) realizes S count
    (fun s hs => pairs s (sub hs)) (fun _ ha _ hb different => sep (sub ha) (sub hb) different)

end PlaneMatchingOperands
