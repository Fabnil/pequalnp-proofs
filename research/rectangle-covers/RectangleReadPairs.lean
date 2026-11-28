import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

namespace RectangleReadPairs

variable {P L : Type*}

def ZeroRectangle (incidence : P → L → Prop) (r : Finset P × Finset L) : Prop :=
  ∀ p ∈ r.1, ∀ l ∈ r.2, ¬incidence p l

def CoversZeros {I : Type*} (incidence : P → L → Prop) (rect : I → Finset P × Finset L) : Prop :=
  ∀ p l, ¬incidence p l → ∃ i, p ∈ (rect i).1 ∧ l ∈ (rect i).2

/-- If a point occurs in precisely two non-singleton point sets of a rectangle
cover, those sets meet only at that point and lie on a common line. -/
theorem twoPointSetsCollinear {I : Type*} [DecidableEq P] (incidence : P → L → Prop)
    (lineThrough : ∀ x y, x ≠ y → ∃ l, incidence x l ∧ incidence y l)
    (lineUnique : ∀ x y l m, x ≠ y → incidence x l → incidence y l →
      incidence x m → incidence y m → l = m)
    (separates : ∀ x y, x ≠ y → ∃ l, incidence x l ∧ ¬incidence y l)
    (rect : I → Finset P × Finset L) (zeros : ∀ i, ZeroRectangle incidence (rect i))
    (covers : CoversZeros incidence rect)
    (p : P) (r s : I) (pr : p ∈ (rect r).1) (ps : p ∈ (rect s).1)
    (only : ∀ i, p ∈ (rect i).1 → i = r ∨ i = s)
    (otherR : ∃ x ∈ (rect r).1, x ≠ p) (otherS : ∃ y ∈ (rect s).1, y ≠ p) :
    ∃ l, (rect r).1 ∩ (rect s).1 = {p} ∧
      (∀ x ∈ (rect r).1, incidence x l) ∧ ∀ y ∈ (rect s).1, incidence y l := by
  have common {x y l} (xr : x ∈ (rect r).1) (ys : y ∈ (rect s).1)
      (xl : incidence x l) (yl : incidence y l) : incidence p l := by
    by_contra absent
    obtain ⟨t, pt, lt⟩ := covers p l absent
    rcases only t pt with rfl | rfl
    · exact zeros _ x xr l lt xl
    · exact zeros _ y ys l lt yl
  have commonPoint {x} (xr : x ∈ (rect r).1) (xs : x ∈ (rect s).1) : x = p := by
    by_contra different
    obtain ⟨l, xl, pl⟩ := separates x p different
    exact pl (common xr xs xl xl)
  obtain ⟨x, xr, xp⟩ := otherR
  obtain ⟨y, ys, yp⟩ := otherS
  have xy : x ≠ y := fun eq => xp (commonPoint xr (eq.symm ▸ ys))
  obtain ⟨l, xl, yl⟩ := lineThrough x y xy
  have pl := common xr ys xl yl
  refine ⟨l, ?_, ?_, ?_⟩
  · ext v
    simp only [Finset.mem_inter, Finset.mem_singleton]
    exact ⟨fun h => commonPoint h.1 h.2, fun e => e ▸ ⟨pr, ps⟩⟩
  · intro v vr
    by_cases vp : v = p
    · simpa [vp] using pl
    have vy : v ≠ y := fun eq => vp (commonPoint vr (eq.symm ▸ ys))
    obtain ⟨m, vm, ym⟩ := lineThrough v y vy
    have same := lineUnique p y m l (Ne.symm yp) (common vr ys vm ym) ym pl yl
    exact same ▸ vm
  · intro v vs
    by_cases vp : v = p
    · simpa [vp] using pl
    have xv : x ≠ v := fun eq => xp (commonPoint xr (eq.symm ▸ vs))
    obtain ⟨m, xm, vm⟩ := lineThrough x v xv
    have same := lineUnique p x m l (Ne.symm xp) (common xr vs xm vm) xm pl xl
    exact same ▸ vm

theorem twoPointSetsSize [Fintype P] [DecidableEq P] (incidence : P → L → Prop)
    [DecidableRel incidence] (degree : ℕ)
    (lineSize : ∀ l, (Finset.univ.filter fun p => incidence p l).card = degree)
    (p : P) (A B : Finset P)
    (collinear : ∃ l, A ∩ B = {p} ∧
       (∀ x ∈ A, incidence x l) ∧ ∀ y ∈ B, incidence y l) :
    A.card + B.card ≤ degree + 1 := by
  obtain ⟨l, inter, ha, hb⟩ := collinear
  have bound : (A ∪ B).card ≤ degree := by
    rw [← lineSize l]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x,
      (Finset.mem_union.mp hx).elim (ha x) (hb x)⟩
  have equality := Finset.card_union_add_card_inter A B
  rw [inter, Finset.card_singleton] at equality
  omega


open scoped BigOperators

theorem pairedSlotCount {I : Type*} [Fintype L] [DecidableEq L] [DecidableEq I] [DecidableEq P]
    (slots : Finset I) (points : Finset P) (label : I → L) (center : P → L) (use : P → Finset I)
    (pointCap : ∀ l, (points.filter fun p => center p = l).card ≤ 6)
    (paired : ∀ p ∈ points, (use p).card = 2 ∧ use p ⊆ slots.filter (fun i => label i = center p))
    (unique : Set.InjOn use points) :
    2 * points.card ≤ 3 * slots.card := by
  classical
  have perLine (l : L) :
      2 * (points.filter fun p => center p = l).card ≤
        3 * (slots.filter fun i => label i = l).card := by
    let group := points.filter fun p => center p = l
    let localSlots := slots.filter fun i => label i = l
    change 2 * group.card ≤ 3 * localSlots.card
    have cap : group.card ≤ 6 := pointCap l
    by_cases large : 4 ≤ localSlots.card
    · omega
    have into : group.image use ⊆ localSlots.powersetCard 2 := by
      intro set mem
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp mem
      obtain ⟨point, onLine⟩ := Finset.mem_filter.mp hp
      obtain ⟨two, incl⟩ := paired p point
      rw [onLine] at incl
      exact Finset.mem_powersetCard.mpr ⟨incl, two⟩
    have incl := Finset.card_le_card into
    have inj : Set.InjOn use group := by
      intro p hp q hq eq
      exact unique (Finset.mem_filter.mp (show p ∈ group from hp)).1
        (Finset.mem_filter.mp (show q ∈ group from hq)).1 eq
    rw [Finset.card_image_of_injOn inj, Finset.card_powersetCard] at incl
    have small : localSlots.card < 4 := by omega
    have bound : ∀ k : Fin 4, 2 * Nat.choose k.val 2 ≤ 3 * k.val := by decide
    have inequality := bound ⟨localSlots.card, small⟩
    change 2 * Nat.choose localSlots.card 2 ≤ 3 * localSlots.card at inequality
    omega
  have pointSum : ∑ l : L, (points.filter fun p => center p = l).card = points.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter points (Finset.univ : Finset L) center
  have slotSum : ∑ l : L, (slots.filter fun i => label i = l).card = slots.card := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter slots (Finset.univ : Finset L) label
  calc
    2 * points.card = ∑ l : L, 2 * (points.filter fun p => center p = l).card := by
      rw [← Finset.mul_sum, pointSum]
    _ ≤ ∑ l : L, 3 * (slots.filter fun i => label i = l).card :=
      Finset.sum_le_sum fun l _ => perLine l
    _ = 3 * slots.card := by rw [← Finset.mul_sum, slotSum]


def slotsContaining {I : Type*} [Fintype I] [DecidableEq P]
    (rect : I → Finset P × Finset L) (p : P) : Finset I :=
  Finset.univ.filter fun i => p ∈ (rect i).1

theorem lowReadCount {I : Type*} [Fintype I] [Fintype P] [Fintype L] [Nonempty L]
    [DecidableEq I] [DecidableEq P] [DecidableEq L] (incidence : P → L → Prop)
    [DecidableRel incidence]
    (lineThrough : ∀ x y, x ≠ y → ∃ l, incidence x l ∧ incidence y l)
    (lineUnique : ∀ x y l m, x ≠ y → incidence x l → incidence y l →
      incidence x m → incidence y m → l = m)
    (separates : ∀ x y, x ≠ y → ∃ l, incidence x l ∧ ¬incidence y l)
    (missing : ∀ p, ∃ l, ¬incidence p l)
    (lineSize : ∀ l, (Finset.univ.filter fun p => incidence p l).card ≤ 6)
    (rect : I → Finset P × Finset L) (zeros : ∀ i, ZeroRectangle incidence (rect i))
    (covers : CoversZeros incidence rect) :
    2 * (Finset.univ.filter fun p => (slotsContaining rect p).card ≤ 2).card
      ≤ 3 * Fintype.card I := by
  classical
  let reads := slotsContaining rect
  have readsDef {p : P} {i : I} : i ∈ reads p ↔ p ∈ (rect i).1 := by
    simp [reads,slotsContaining]
  let low := Finset.univ.filter fun p => (reads p).card ≤ 2
  let singletonSlots := Finset.univ.filter fun i => (rect i).1.card = 1
  let nonsingletonSlots := (Finset.univ : Finset I) \ singletonSlots
  let singletonRows := low.filter fun p => ∃ i, (rect i).1 = {p}
  let pairRows := low \ singletonRows
  have onlyPair {p : P} (hp : p ∈ pairRows) : ¬∃ i, (rect i).1 = {p} := by
    have h := Finset.mem_sdiff.mp hp
    exact fun e => h.2 (Finset.mem_filter.mpr ⟨h.1,e⟩)
  have another {p : P} (hp : p ∈ pairRows) {i : I} (hi : i ∈ reads p) :
      ∃ q ∈ (rect i).1, q ≠ p := by
    by_contra! same
    apply onlyPair hp
    refine ⟨i, ?_⟩
    ext q
    simp only [Finset.mem_singleton]
    exact ⟨same q, fun e => e.symm ▸ readsDef.mp hi⟩
  have classification (p : P) (hp : p ∈ pairRows) :
      (reads p).card = 2 ∧ (∀ q, reads q = reads p → q = p) ∧
        ∃ l, incidence p l ∧ ∀ i ∈ reads p, ∀ q ∈ (rect i).1, incidence q l := by
    have cap := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    have nonempty : (reads p).Nonempty := by
      obtain ⟨l, absent⟩ := missing p
      obtain ⟨i, pi, _⟩ := covers p l absent
      exact ⟨i, readsDef.mpr pi⟩
    have notOne : (reads p).card ≠ 1 := by
      intro one
      obtain ⟨i, eq⟩ := Finset.card_eq_one.mp one
      have atI : i ∈ reads p := by simp [eq]
      obtain ⟨q, qi, apart⟩ := another hp atI
      obtain ⟨l, ql, pl⟩ := separates q p apart
      obtain ⟨j, pj, lj⟩ := covers p l pl
      have atJ := readsDef.mpr pj
      rw [eq, Finset.mem_singleton] at atJ
      subst j
      exact zeros i q qi l lj ql
    have pos := Finset.card_pos.mpr nonempty
    have two : (reads p).card = 2 := by omega
    obtain ⟨i, j, _, eq⟩ := Finset.card_eq_two.mp two
    have atI : i ∈ reads p := by simp [eq]
    have atJ : j ∈ reads p := by simp [eq]
    have buckets (k) (pk : p ∈ (rect k).1) : k = i ∨ k = j := by
      have mk := readsDef.mpr pk
      simpa [eq] using mk
    obtain ⟨l, inter, il, jl⟩ := twoPointSetsCollinear incidence lineThrough lineUnique separates
      rect zeros covers p i j (readsDef.mp atI) (readsDef.mp atJ) buckets
      (another hp atI) (another hp atJ)
    refine ⟨two, ?_, l, il p (readsDef.mp atI), ?_⟩
    · intro q same
      have qi : q ∈ (rect i).1 := readsDef.mp (same.symm ▸ atI)
      have qj : q ∈ (rect j).1 := readsDef.mp (same.symm ▸ atJ)
      have belong := Finset.mem_inter.mpr ⟨qi,qj⟩
      rwa [inter, Finset.mem_singleton] at belong
    · intro k hk
      rcases buckets k (readsDef.mp hk) with rfl | rfl
      · exact il
      · exact jl
  let arbitrary : L := Classical.choice ‹Nonempty L›
  let center (p : P) :=
    if h : p ∈ pairRows then Classical.choose (classification p h).2.2 else arbitrary
  have centerSpec (p : P) (hp : p ∈ pairRows) :
      incidence p (center p) ∧ ∀ i ∈ reads p, ∀ q ∈ (rect i).1, incidence q (center p) := by
    simp only [center, dif_pos hp]
    exact Classical.choose_spec (classification p hp).2.2
  let label (i : I) :=
    if h : ∃ l, ∀ q ∈ (rect i).1, incidence q l then Classical.choose h else arbitrary
  have sameLabel {p : P} (hp : p ∈ pairRows) {i : I} (hi : i ∈ reads p) :
      label i = center p := by
    have onCenter := (centerSpec p hp).2 i hi
    have existsLine : ∃ l, ∀ q ∈ (rect i).1, incidence q l := ⟨center p,onCenter⟩
    have onLabel : ∀ q ∈ (rect i).1, incidence q (label i) := by
      simp only [label, dif_pos existsLine]
      exact Classical.choose_spec existsLine
    obtain ⟨q, qi, apart⟩ := another hp hi
    exact lineUnique q p (label i) (center p) apart
      (onLabel q qi) (onLabel p (readsDef.mp hi)) (onCenter q qi) (onCenter p (readsDef.mp hi))
  have pairBound : 2 * pairRows.card ≤ 3 * nonsingletonSlots.card := by
    apply pairedSlotCount nonsingletonSlots pairRows label center reads
    · intro l
      refine (Finset.card_le_card (t := Finset.univ.filter fun p => incidence p l) ?_).trans (lineSize l)
      intro p mem
      obtain ⟨hp, eq⟩ := Finset.mem_filter.mp mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq ▸ (centerSpec p hp).1⟩
    · intro p hp
      refine ⟨(classification p hp).1, ?_⟩
      intro i hi
      have nonsingleton : i ∈ nonsingletonSlots := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro excluded
        obtain ⟨q, eq⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp excluded).2
        have pq : p = q := by simpa [eq] using (readsDef.mp hi)
        exact onlyPair hp ⟨i, pq ▸ eq⟩
      exact Finset.mem_filter.mpr ⟨nonsingleton, sameLabel hp hi⟩
    · intro p hp q _ eq
      exact ((classification p hp).2.1 q eq.symm).symm
  have singleBound : singletonRows.card ≤ singletonSlots.card := by
    have choices (p : {p // p ∈ singletonRows}) : ∃ i, (rect i).1 = {p.val} :=
      (Finset.mem_filter.mp p.property).2
    choose chooseSlot slotEq using choices
    let inject (p : {p // p ∈ singletonRows}) : {i // i ∈ singletonSlots} :=
      ⟨chooseSlot p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [slotEq p]⟩⟩
    have witness : Function.Injective inject := by
      intro p q eq
      have same : chooseSlot p = chooseSlot q := congrArg Subtype.val eq
      have eqSets : ({p.val} : Finset P) = {q.val} := by rw [← slotEq p, ← slotEq q, same]
      exact Subtype.ext (Finset.singleton_inj.mp eqSets)
    simpa using Fintype.card_le_of_injective inject witness
  have sumPoints : pairRows.card + singletonRows.card = low.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have sumSlots : nonsingletonSlots.card + singletonSlots.card = Fintype.card I := by
    simpa [nonsingletonSlots] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ singletonSlots)
  change 2 * low.card ≤ 3 * Fintype.card I
  omega


/-- For the parameters of the order-five incidence plane, a cover with at
most seventeen rectangles uses at least three rectangles at six points. -/
theorem sixHighReadVertices {I : Type*} [Fintype I] [DecidableEq I]
    (inc : Fin 31 → Fin 31 → Prop) [DecidableRel inc]
    (rowDegree : ∀ p, (Finset.univ.filter fun l => inc p l).card = 6)
    (columnDegree : ∀ l, (Finset.univ.filter fun p => inc p l).card = 6)
    (interDegree : ∀ p q, p ≠ q → (Finset.univ.filter fun l => inc p l ∧ inc q l).card = 1)
    (rect : I → Finset (Fin 31) × Finset (Fin 31))
    (zero : ∀ i, ZeroRectangle inc (rect i))
    (cover : CoversZeros inc rect)
    (budget : Fintype.card I ≤ 17) :
    6 ≤ (Finset.univ.filter fun p => 3 ≤ (slotsContaining rect p).card).card := by
  classical
  have through (p q : Fin 31) (apart : p ≠ q) : ∃ l, inc p l ∧ inc q l := by
    obtain ⟨l, eq⟩ := Finset.card_eq_one.mp (interDegree p q apart)
    have mem : l ∈ (Finset.univ.filter fun l => inc p l ∧ inc q l) := by simp [eq]
    exact ⟨l,(Finset.mem_filter.mp mem).2⟩
  have unique (p q l m : Fin 31) (apart : p ≠ q) (pl : inc p l) (ql : inc q l)
      (pm : inc p m) (qm : inc q m) : l = m := by
    have cap := Finset.card_le_one.mp (le_of_eq (interDegree p q apart))
    exact cap l (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl,ql⟩)
      m (Finset.mem_filter.mpr ⟨Finset.mem_univ _,pm,qm⟩)
  have separately (p q : Fin 31) (apart : p ≠ q) : ∃ l, inc p l ∧ ¬inc q l := by
    by_contra! missing
    have sub : (Finset.univ.filter fun l => inc p l) ⊆
        (Finset.univ.filter fun l => inc p l ∧ inc q l) := by
      intro l mem
      have pl := (Finset.mem_filter.mp mem).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl,missing l pl⟩
    have count := Finset.card_le_card sub
    rw [rowDegree,interDegree p q apart] at count
    omega
  have absent (p : Fin 31) : ∃ l, ¬inc p l := by
    by_contra! all
    have full : (Finset.univ.filter fun l => inc p l) = Finset.univ := by
      simp [all]
    have count := rowDegree p
    rw [full,Finset.card_univ,Fintype.card_fin] at count
    omega
  have low := lowReadCount inc through unique separately absent
    (fun l => le_of_eq (columnDegree l)) rect zero cover
  let lowSet := Finset.univ.filter fun p : Fin 31 => (slotsContaining rect p).card ≤ 2
  let highSet := Finset.univ.filter fun p : Fin 31 => 3 ≤ (slotsContaining rect p).card
  have comp : highSet = (Finset.univ : Finset (Fin 31)) \ lowSet := by
    ext p
    simp only [highSet, lowSet, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    omega
  have partition : highSet.card + lowSet.card = 31 := by
    rw [comp, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _),
      Finset.card_univ, Fintype.card_fin]
  change 2 * lowSet.card ≤ 3 * Fintype.card I at low
  change 6 ≤ highSet.card
  omega

def rows : List ℕ :=
  [1141899472, 136315297, 272630594, 545261188, 1090522376, 33561105, 67122210,
   134244420, 268488840, 536977680, 1073955360, 427073, 854146, 1708292, 3416584,
   6833168, 13666336, 27332672, 54665344, 109330688, 218661376, 437322752, 874645504,
   1749291008, 1351098369, 554713091, 1109426182, 71368717, 142737434, 285474868,
   570949736]

def incident (p l : Fin 31) : Prop := (rows.getD p.val 0).testBit l.val = true

instance incidentDecidable : DecidableRel incident :=
  fun p l => inferInstanceAs (Decidable ((rows.getD p.val 0).testBit l.val = true))

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem rowCount : ∀ p : Fin 31, (Finset.univ.filter fun l => incident p l).card = 6 := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem columnCount : ∀ l : Fin 31, (Finset.univ.filter fun p => incident p l).card = 6 := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem commonLineCount : ∀ p q : Fin 31, p ≠ q →
    (Finset.univ.filter fun l => incident p l ∧ incident q l).card = 1 := by
  decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem commonPointCount : ∀ l m : Fin 31, l ≠ m →
    (Finset.univ.filter fun p => incident p l ∧ incident p m).card = 1 := by
  decide +kernel

theorem sixRowsAndColumns (C : List (Finset (Fin 31) × Finset (Fin 31)))
    (budget : C.length ≤ 17)
    (zero : ∀ r ∈ C, ZeroRectangle incident r)
    (cover : ∀ p l, ¬incident p l → ∃ r ∈ C, p ∈ r.1 ∧ l ∈ r.2) :
    let original : Fin C.length → Finset (Fin 31) × Finset (Fin 31) := C.get
    let swapped : Fin C.length → Finset (Fin 31) × Finset (Fin 31) :=
      fun i => ((C.get i).2, (C.get i).1)
    6 ≤ (Finset.univ.filter fun p => 3 ≤ (slotsContaining original p).card).card ∧
      6 ≤ (Finset.univ.filter fun l => 3 ≤ (slotsContaining swapped l).card).card := by
  have zer (i : Fin C.length) : ZeroRectangle incident (C.get i) :=
    zero _ (List.getElem_mem i.isLt)
  have cov : CoversZeros incident C.get := by
    intro p l absent
    obtain ⟨r, hr, rp, rl⟩ := cover p l absent
    obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp hr
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · change p ∈ C[i].1
      rwa [value]
    · change l ∈ C[i].2
      rwa [value]
  have sz : Fintype.card (Fin C.length) ≤ 17 := by simpa using budget
  constructor
  · exact sixHighReadVertices incident rowCount columnCount commonLineCount C.get zer cov sz
  · let swapped : Fin C.length → Finset (Fin 31) × Finset (Fin 31) :=
      fun i => ((C.get i).2, (C.get i).1)
    exact sixHighReadVertices (fun l p => incident p l) columnCount rowCount commonPointCount
      swapped (fun i l il p ip => zer i p ip l il)
      (fun l p absent => by
        obtain ⟨i, ip, il⟩ := cov p l absent
        exact ⟨i, il, ip⟩) sz

end RectangleReadPairs
