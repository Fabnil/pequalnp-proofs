import PEqualNP.Defs

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

def operand (A B : Fin 20 → Finset (Fin 42)) (j : Fin 20 × Bool) : Finset (Fin 42) :=
  if j.2 then A j.1 else B j.1

private theorem operandReads {A B : Fin 20 → Finset (Fin 42)}
    (separate : ∀ j, Disjoint (A j) (B j)) (v : Fin 42) :
    (Reads (operand A B) v).card = {j : Fin 20 | v ∈ A j ∨ v ∈ B j}.ncard := by
  classical
  let both := (Finset.univ : Finset (Fin 20)).filter fun j => v ∈ A j ∨ v ∈ B j
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
  have one : Set.InjOn Prod.fst (↑(Reads (operand A B) v) : Set (Fin 20 × Bool)) := by
    rintro ⟨i, s⟩ hs ⟨j, t⟩ ht (eq : i = j)
    subst j
    have hitS := (Finset.mem_filter.mp (Finset.mem_coe.mp hs)).2
    have hitT := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
    cases s <;> cases t <;> try rfl
    · exact (Finset.disjoint_left.mp (separate i) (by simpa [operand] using hitT)
        (by simpa [operand] using hitS)).elim
    · exact (Finset.disjoint_left.mp (separate i) (by simpa [operand] using hitS)
        (by simpa [operand] using hitT)).elim
  have setBoth : ({j : Fin 20 | v ∈ A j ∨ v ∈ B j} : Set (Fin 20)) = ↑both := by
    ext j
    simp [both]
  rw [setBoth, Set.ncard_coe_finset, ← onto, Finset.card_image_of_injOn one]

private theorem operandsRealize (A B : Fin 20 → Finset (Fin 42))
    (represent : ∀ C, MinimalCover planeGraph.Adj C → ∃ U W : Finset (Fin 20),
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

#print axioms PlaneCoverReadSets.planeFourPairSides
