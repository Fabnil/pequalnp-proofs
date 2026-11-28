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

theorem twoElementSubsetsBound {I : Type*} [DecidableEq I] [DecidableEq P]
    (points : Finset P) (slots : Finset I) (use : P → Finset I)
    (pairs : ∀ p ∈ points, (use p).card = 2 ∧ use p ⊆ slots)
    (injective : Set.InjOn use points) : points.card ≤ Nat.choose slots.card 2 := by
  classical
  have sub : points.image use ⊆ slots.powersetCard 2 := by
    intro pair mem
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp mem
    exact Finset.mem_powersetCard.mpr ⟨(pairs p hp).2,(pairs p hp).1⟩
  have h := Finset.card_le_card sub
  simpa only [Finset.card_image_of_injOn injective,Finset.card_powersetCard] using h

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
    have incl := twoElementSubsetsBound group localSlots use
      (fun p hp => by
        obtain ⟨hit,onLine⟩ := Finset.mem_filter.mp hp
        simpa only [onLine] using paired p hit)
      (fun p hp q hq eq => unique
        (Finset.mem_filter.mp (show p ∈ group from hp)).1
        (Finset.mem_filter.mp (show q ∈ group from hq)).1 eq)
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

structure LowReadAssignment {I : Type*} [Fintype I] [Fintype P]
    [DecidableEq I] [DecidableEq P] (incidence : P → L → Prop)
    (rect : I → Finset P × Finset L) where
  singletonRows : Finset P
  pairRows : Finset P
  singletonSlots : Finset I
  pairSlots : Finset I
  center : P → L
  label : I → L
  partition : pairRows.card + singletonRows.card =
    (Finset.univ.filter fun p => (slotsContaining rect p).card ≤ 2).card
  slotsDisjoint : Disjoint singletonSlots pairSlots
  singletonCount : singletonRows.card = singletonSlots.card
  singletonLow : ∀ i ∈ singletonSlots, ∀ p ∈ (rect i).1, (slotsContaining rect p).card ≤ 2
  rowIncidence : ∀ p ∈ pairRows, incidence p (center p)
  paired : ∀ p ∈ pairRows, (slotsContaining rect p).card = 2
  pairedLabel : ∀ p ∈ pairRows, ∀ i ∈ slotsContaining rect p, i ∈ pairSlots ∧ label i = center p
  pairedInjective : Set.InjOn (slotsContaining rect) pairRows
  slotIncidence : ∀ i ∈ pairSlots, ∀ p ∈ (rect i).1, incidence p (label i)
  slotUsed : ∀ i ∈ pairSlots, ∃ p ∈ pairRows, i ∈ slotsContaining rect p

theorem buildLowReadAssignment {I : Type*} [Fintype I] [Fintype P] [Fintype L] [Nonempty L]
    [DecidableEq I] [DecidableEq P] [DecidableEq L] (incidence : P → L → Prop)
    [DecidableRel incidence]
    (lineThrough : ∀ x y, x ≠ y → ∃ l, incidence x l ∧ incidence y l)
    (lineUnique : ∀ x y l m, x ≠ y → incidence x l → incidence y l →
      incidence x m → incidence y m → l = m)
    (separates : ∀ x y, x ≠ y → ∃ l, incidence x l ∧ ¬incidence y l)
    (missing : ∀ p, ∃ l, ¬incidence p l)
    (rect : I → Finset P × Finset L) (zeros : ∀ i, ZeroRectangle incidence (rect i))
    (covers : CoversZeros incidence rect) : Nonempty (LowReadAssignment incidence rect) := by
  classical
  let reads := slotsContaining rect
  have readsDef {p : P} {i : I} : i ∈ reads p ↔ p ∈ (rect i).1 := by
    simp [reads,slotsContaining]
  let low := Finset.univ.filter fun p => (reads p).card ≤ 2
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
  have choices (p : {p // p ∈ singletonRows}) : ∃ i, (rect i).1 = {p.val} :=
    (Finset.mem_filter.mp p.property).2
  choose chooseSlot slotEq using choices
  let singletonSlots := (Finset.univ : Finset {p // p ∈ singletonRows}).image chooseSlot
  have injective : Function.Injective chooseSlot := by
    intro p q eq
    have eqSets : ({p.val} : Finset P) = {q.val} := by rw [← slotEq p, ← slotEq q, eq]
    exact Subtype.ext (Finset.singleton_inj.mp eqSets)
  let pairSlots := pairRows.biUnion reads
  refine ⟨{
    singletonRows := singletonRows
    pairRows := pairRows
    singletonSlots := singletonSlots
    pairSlots := pairSlots
    center := center
    label := label
    partition := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
    slotsDisjoint := ?_
    singletonCount := ?_
    singletonLow := ?_
    rowIncidence := fun p hp => (centerSpec p hp).1
    paired := fun p hp => (classification p hp).1
    pairedLabel := ?_
    pairedInjective := ?_
    slotIncidence := ?_
    slotUsed := fun _ h => Finset.mem_biUnion.mp h
  }⟩
  · refine Finset.disjoint_left.mpr ?_
    intro i single paired
    obtain ⟨p, _, eq⟩ := Finset.mem_image.mp single
    obtain ⟨q, hq, used⟩ := Finset.mem_biUnion.mp paired
    have singleton : (rect i).1 = {p.val} := by rw [← eq,slotEq p]
    have qp : q = p.val := by simpa [singleton] using readsDef.mp used
    exact onlyPair hq ⟨i,qp ▸ singleton⟩
  · simp [singletonSlots, Finset.card_image_of_injective _ injective]
  · intro i hi p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hi
    have pq : p = q.val := by simpa [slotEq q] using hp
    rw [pq]
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp q.property).1).2
  · intro p hp i hi
    exact ⟨Finset.mem_biUnion.mpr ⟨p,hp,hi⟩,sameLabel hp hi⟩
  · intro p hp q _ eq
    exact ((classification p hp).2.1 q eq.symm).symm
  · intro i used p hp
    obtain ⟨q, hq, hread⟩ := Finset.mem_biUnion.mp used
    rw [sameLabel hq hread]
    exact (centerSpec q hq).2 i hread p hp

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
  obtain ⟨A⟩ := buildLowReadAssignment incidence lineThrough lineUnique separates missing rect zeros covers
  have pairs : 2 * A.pairRows.card ≤ 3 * A.pairSlots.card := by
    apply pairedSlotCount A.pairSlots A.pairRows A.label A.center (slotsContaining rect)
    · intro l
      refine (Finset.card_le_card (t := Finset.univ.filter fun p => incidence p l) ?_).trans (lineSize l)
      intro p mem
      obtain ⟨hp, eq⟩ := Finset.mem_filter.mp mem
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq ▸ A.rowIncidence p hp⟩
    · intro p hp
      refine ⟨A.paired p hp, ?_⟩
      intro i hi
      exact Finset.mem_filter.mpr (A.pairedLabel p hp i hi)
    · exact A.pairedInjective
  have slots : A.singletonSlots.card + A.pairSlots.card ≤ Fintype.card I := by
    rw [← Finset.card_union_of_disjoint A.slotsDisjoint]
    exact Finset.card_le_univ _
  rw [← A.partition]
  have singleton := A.singletonCount
  omega

theorem orderFiveRowGeometry (inc : Fin 31 → Fin 31 → Prop) [DecidableRel inc]
    (rowDegree : ∀ p, (Finset.univ.filter fun l => inc p l).card = 6)
    (interDegree : ∀ p q, p ≠ q → (Finset.univ.filter fun l => inc p l ∧ inc q l).card = 1) :
    (∀ p q, p ≠ q → ∃ l, inc p l ∧ inc q l) ∧
    (∀ p q l m, p ≠ q → inc p l → inc q l → inc p m → inc q m → l = m) ∧
    (∀ p q, p ≠ q → ∃ l, inc p l ∧ ¬inc q l) ∧
    (∀ p, ∃ l, ¬inc p l) := by
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
  exact ⟨through,unique,separately,absent⟩

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
  obtain ⟨through,unique,separately,absent⟩ := orderFiveRowGeometry inc rowDegree interDegree
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

theorem listCover {P L : Type*} (inc : P → L → Prop)
    (C : List (Finset P × Finset L))
    (zero : ∀ r ∈ C, ZeroRectangle inc r)
    (cover : ∀ p l, ¬inc p l → ∃ r ∈ C, p ∈ r.1 ∧ l ∈ r.2) :
    (∀ i : Fin C.length, ZeroRectangle inc (C.get i)) ∧ CoversZeros inc C.get := by
  have zer (i : Fin C.length) : ZeroRectangle inc (C.get i) :=
    zero _ (List.getElem_mem i.isLt)
  have cov : CoversZeros inc C.get := by
    intro p l absent
    obtain ⟨r, hr, rp, rl⟩ := cover p l absent
    obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp hr
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · change p ∈ C[i].1
      rwa [value]
    · change l ∈ C[i].2
      rwa [value]
  exact ⟨zer,cov⟩

theorem sixRowsAndColumns (C : List (Finset (Fin 31) × Finset (Fin 31)))
    (budget : C.length ≤ 17)
    (zero : ∀ r ∈ C, ZeroRectangle incident r)
    (cover : ∀ p l, ¬incident p l → ∃ r ∈ C, p ∈ r.1 ∧ l ∈ r.2) :
    let original : Fin C.length → Finset (Fin 31) × Finset (Fin 31) := C.get
    let swapped : Fin C.length → Finset (Fin 31) × Finset (Fin 31) :=
      fun i => ((C.get i).2, (C.get i).1)
    6 ≤ (Finset.univ.filter fun p => 3 ≤ (slotsContaining original p).card).card ∧
      6 ≤ (Finset.univ.filter fun l => 3 ≤ (slotsContaining swapped l).card).card := by
  obtain ⟨zer,cov⟩ := listCover incident C zero cover
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


/-- In an order-five incidence plane, a seventeen-slot cover needs at least
eleven rows that read three or more slots. -/
theorem elevenHighReadVertices {I : Type*} [Fintype I] [DecidableEq I]
    (inc : Fin 31 → Fin 31 → Prop) [DecidableRel inc]
    (lineThrough : ∀ p q, p ≠ q → ∃ l, inc p l ∧ inc q l)
    (lineUnique : ∀ p q l m, p ≠ q → inc p l → inc q l → inc p m → inc q m → l = m)
    (separates : ∀ p q, p ≠ q → ∃ l, inc p l ∧ ¬inc q l)
    (missing : ∀ p, ∃ l, ¬inc p l)
    (columnDegree : ∀ l, (Finset.univ.filter fun p => inc p l).card = 6)
    (intersects : ∀ l m, l ≠ m → ∃ p, inc p l ∧ inc p m)
    (rect : I → Finset (Fin 31) × Finset (Fin 31))
    (zero : ∀ i, ZeroRectangle inc (rect i))
    (cover : CoversZeros inc rect) (budget : Fintype.card I ≤ 17) :
    11 ≤ (Finset.univ.filter fun p => 3 ≤ (slotsContaining rect p).card).card := by
  classical
  obtain ⟨A⟩ := buildLowReadAssignment inc lineThrough lineUnique separates missing rect zero cover
  let rowsOn (l : Fin 31) := A.pairRows.filter fun p => A.center p = l
  let slotsOn (l : Fin 31) := A.pairSlots.filter fun i => A.label i = l
  let members (l : Fin 31) := Finset.univ.filter fun p => inc p l
  let r (l : Fin 31) := (rowsOn l).card
  let k (l : Fin 31) := (slotsOn l).card
  have rowSubset (l : Fin 31) : rowsOn l ⊆ members l := by
    intro p mem
    obtain ⟨hp,eq⟩ := Finset.mem_filter.mp mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq ▸ A.rowIncidence p hp⟩
  have memberCount (l : Fin 31) : (members l).card = 6 := columnDegree l
  have rowCap (l : Fin 31) : r l ≤ 6 := (Finset.card_le_card (rowSubset l)).trans_eq (memberCount l)
  have fullPoints (l : Fin 31) (full : r l = 6) : rowsOn l = members l := by
    apply Finset.eq_of_subset_of_card_le (rowSubset l)
    change (members l).card ≤ r l
    rw [memberCount,full]
  have counts (l : Fin 31) : r l ≤ Nat.choose (k l) 2 := by
    apply twoElementSubsetsBound (rowsOn l) (slotsOn l) (slotsContaining rect)
    · intro p hp
      obtain ⟨pIn,tag⟩ := Finset.mem_filter.mp hp
      refine ⟨A.paired p pIn, ?_⟩
      intro i hi
      obtain ⟨iIn,assign⟩ := A.pairedLabel p pIn i hi
      exact Finset.mem_filter.mpr ⟨iIn,assign.trans tag⟩
    · intro p hp q hq eq
      exact A.pairedInjective (Finset.mem_filter.mp (show p ∈ rowsOn l from hp)).1
        (Finset.mem_filter.mp (show q ∈ rowsOn l from hq)).1 eq
  have largeGroup (l : Fin 31) (five : 5 ≤ r l) : 4 ≤ k l := by
    by_contra! lt4
    have simple : ∀ b : Fin 4, Nat.choose b.val 2 ≤ 3 := by decide
    have h := simple ⟨k l,lt4⟩
    change Nat.choose (k l) 2 ≤ 3 at h
    have count := counts l
    omega
  let fullLines := Finset.univ.filter fun l : Fin 31 => r l = 6
  have oneFull : fullLines.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl m hm
    by_contra distinct
    obtain ⟨p,pl,pm⟩ := intersects l m distinct
    have lmem : p ∈ rowsOn l := by
      rw [fullPoints l (Finset.mem_filter.mp hl).2]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,pl⟩
    have mmem : p ∈ rowsOn m := by
      rw [fullPoints m (Finset.mem_filter.mp hm).2]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,pm⟩
    exact distinct ((Finset.mem_filter.mp lmem).2.symm.trans (Finset.mem_filter.mp mmem).2)
  let allowance (l : Fin 31) : ℕ := if r l = 6 then 4 else 0
  let deficit (l : Fin 31) := 5 * k l + allowance l - 4 * r l
  have cost (l : Fin 31) : 4 * r l ≤ 5 * k l + allowance l := by
    by_cases full : r l = 6
    · have lk := largeGroup l (by omega)
      simp only [allowance,full,if_true]
      omega
    · have rows := rowCap l
      by_cases lk : 4 ≤ k l
      · omega
      have small : k l < 4 := by omega
      have simple : ∀ b : Fin 4, 4 * Nat.choose b.val 2 ≤ 5 * b.val := by decide
      have h := simple ⟨k l,small⟩
      change 4 * Nat.choose (k l) 2 ≤ 5 * k l at h
      have count := counts l
      omega
  have smallDeficit (l : Fin 31) (pos : 0 < r l) (few : r l ≤ 4) : 3 ≤ deficit l := by
    change 3 ≤ 5 * k l + allowance l - 4 * r l
    by_cases enough : 4 ≤ k l
    · omega
    have ksmall : k l < 4 := by omega
    have rsmall : r l < 5 := by omega
    have valid : ∀ (i : Fin 4) (j : Fin 5), 0 < j.val → j.val ≤ Nat.choose i.val 2 →
        4 * j.val + 3 ≤ 5 * i.val := by decide
    have h := valid ⟨k l, ksmall⟩ ⟨r l,rsmall⟩ pos (counts l)
    change 4 * r l + 3 ≤ 5 * k l at h
    omega
  have rowSum : ∑ l : Fin 31, r l = A.pairRows.card := by
    simpa [r,rowsOn] using Finset.sum_card_fiberwise_eq_card_filter A.pairRows
      (Finset.univ : Finset (Fin 31)) A.center
  have slotSum : ∑ l : Fin 31, k l = A.pairSlots.card := by
    simpa [k,slotsOn] using Finset.sum_card_fiberwise_eq_card_filter A.pairSlots
      (Finset.univ : Finset (Fin 31)) A.label
  have allowanceSum : (∑ l : Fin 31, allowance l) = 4 * fullLines.card := by
    calc
      _ = ∑ l ∈ fullLines, (4 : ℕ) := by rw [Finset.sum_filter]
      _ = _ := by simp [Nat.mul_comm]
  have deficitSum : (∑ l : Fin 31, deficit l) + 4 * A.pairRows.card =
      5 * A.pairSlots.card + 4 * fullLines.card := by
    calc
      _ = ∑ l : Fin 31, (deficit l + 4 * r l) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, rowSum]
      _ = ∑ l : Fin 31, (5 * k l + allowance l) :=
        Finset.sum_congr rfl (fun l _ => Nat.sub_add_cancel (cost l))
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, slotSum, allowanceSum]
  let low := Finset.univ.filter fun p : Fin 31 => (slotsContaining rect p).card ≤ 2
  let high := (Finset.univ : Finset (Fin 31)) \ low
  have totalRows : high.card + low.card = 31 := by
    simpa [high] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ low)
  have lowAt (p : Fin 31) : p ∈ low ↔ (slotsContaining rect p).card ≤ 2 := by
    simp [low]
  have highAt (p : Fin 31) : p ∈ high ↔ 3 ≤ (slotsContaining rect p).card := by
    simp only [high,Finset.mem_sdiff,Finset.mem_univ,true_and,lowAt]
    omega
  have rowSplit : A.pairRows.card + A.singletonRows.card = low.card := A.partition
  let occupied := A.singletonSlots ∪ A.pairSlots
  let unused := (Finset.univ : Finset I) \ occupied
  have slotSplit : unused.card + A.singletonSlots.card + A.pairSlots.card = Fintype.card I := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ occupied)
    simpa [unused,occupied,Finset.card_union_of_disjoint A.slotsDisjoint, Nat.add_assoc] using h
  have singletonCount := A.singletonCount
  have highMin : 9 ≤ high.card := by omega
  have highShape : (Finset.univ.filter fun p => 3 ≤ (slotsContaining rect p).card) = high := by
    ext p
    simp [highAt]
  rw [highShape]
  by_contra! short
  have lowMin : 21 ≤ low.card := by omega
  have free : unused.card ≤ 1 := by omega
  have readOn (p : Fin 31) (hp : p ∈ high) : ∃ l, 0 < r l ∧ p ∈ members l := by
    have large := (highAt p).1 hp
    have taken : ∃ i ∈ A.pairSlots, i ∈ slotsContaining rect p := by
      by_contra untouched
      have sub : slotsContaining rect p ⊆ unused := by
        intro i hi
        have pin : p ∈ (rect i).1 := (Finset.mem_filter.mp hi).2
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro occupiedI
        rcases Finset.mem_union.mp occupiedI with single | pair
        · have bound := A.singletonLow i single p pin
          omega
        · exact untouched ⟨i,pair,hi⟩
      have h := Finset.card_le_card sub
      omega
    obtain ⟨i,hi,pin⟩ := taken
    obtain ⟨q,hq,hit⟩ := A.slotUsed i hi
    have tag := (A.pairedLabel q hq i hit).2
    have positive : 0 < r (A.label i) := Finset.card_pos.mpr
      ⟨q,Finset.mem_filter.mpr ⟨hq,tag.symm⟩⟩
    exact ⟨A.label i,positive,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,A.slotIncidence i hi p (Finset.mem_filter.mp pin).2⟩⟩
  have pairLow (p : Fin 31) (l : Fin 31) (hp : p ∈ rowsOn l) : p ∈ low :=
    (lowAt p).2 (le_of_eq (A.paired p (Finset.mem_filter.mp hp).1))
  let smallLines := Finset.univ.filter fun l : Fin 31 => 0 < r l ∧ r l ≤ 4
  have smallBudget : 3 * smallLines.card ≤ ∑ l : Fin 31, deficit l := by
    calc
      _ = ∑ l ∈ smallLines, (3 : ℕ) := by simp [Nat.mul_comm]
      _ ≤ ∑ l ∈ smallLines, deficit l := Finset.sum_le_sum fun l hl =>
        let h := (Finset.mem_filter.mp hl).2
        smallDeficit l h.1 h.2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
  by_cases existsFull : ∃ l : Fin 31, r l = 6
  · obtain ⟨base,hbase⟩ := existsFull
    have atMostOne : smallLines.card ≤ 1 := by omega
    have lowFive (l : Fin 31) (five : r l = 5) : members l ⊆ low := by
      have distinct : l ≠ base := by
        intro eq
        subst l
        omega
      obtain ⟨q,ql,qbase⟩ := intersects l base distinct
      have qFull : q ∈ rowsOn base := by
        rw [fullPoints base hbase]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,qbase⟩
      have notAssigned : q ∉ rowsOn l := by
        intro assigned
        exact distinct ((Finset.mem_filter.mp assigned).2.symm.trans (Finset.mem_filter.mp qFull).2)
      have coverLine : insert q (rowsOn l) = members l := by
        apply Finset.eq_of_subset_of_card_le
        · intro p mp
          rcases Finset.mem_insert.mp mp with rfl | rest
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ql⟩
          · exact rowSubset l rest
        · rw [Finset.card_insert_of_notMem notAssigned, memberCount]
          change 6 ≤ r l + 1
          omega
      intro p mp
      rw [← coverLine, Finset.mem_insert] at mp
      rcases mp with equal | inserted
      · exact equal.symm ▸ pairLow q base qFull
      · exact pairLow p l inserted
    have highSub : high ⊆ smallLines.biUnion members := by
      intro p hp
      obtain ⟨l,positive,pm⟩ := readOn p hp
      have noLow := (Finset.mem_sdiff.mp hp).2
      have notFull : r l ≠ 6 := fun whole => noLow (pairLow p l (fullPoints l whole ▸ pm))
      have notFive : r l ≠ 5 := fun five => noLow (lowFive l five pm)
      have cap := rowCap l
      exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _, positive, by omega⟩,pm⟩
    have highBound := calc
      high.card ≤ (smallLines.biUnion members).card := Finset.card_le_card highSub
      _ ≤ ∑ l ∈ smallLines, (members l).card := Finset.card_biUnion_le
      _ = 6 * smallLines.card := by simp [memberCount,Nat.mul_comm]
    omega
  · have none : fullLines.card = 0 := by
      have eq : fullLines = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro l hl
        exact existsFull ⟨l,(Finset.mem_filter.mp hl).2⟩
      simp [eq]
    have smallEmpty : smallLines.card = 0 := by omega
    let fiveLines := Finset.univ.filter fun l : Fin 31 => r l = 5
    have fiveBudget : 4 * fiveLines.card ≤ A.pairSlots.card := by
      calc
        _ = ∑ l ∈ fiveLines, (4 : ℕ) := by simp [Nat.mul_comm]
        _ ≤ ∑ l ∈ fiveLines, k l := Finset.sum_le_sum fun l hl =>
          largeGroup l (le_of_eq (Finset.mem_filter.mp hl).2.symm)
        _ ≤ ∑ l : Fin 31, k l := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
        _ = _ := slotSum
    let highOn (l : Fin 31) := (members l) ∩ high
    have capHigh (l : Fin 31) (hl : l ∈ fiveLines) : (highOn l).card ≤ 1 := by
      have five : r l = 5 := (Finset.mem_filter.mp hl).2
      have dis : Disjoint (rowsOn l) (highOn l) := by
        apply Finset.disjoint_left.mpr
        intro p a b
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp b).2).2 (pairLow p l a)
      have unionSub : rowsOn l ∪ highOn l ⊆ members l :=
        Finset.union_subset (rowSubset l) (fun _ h => (Finset.mem_inter.mp h).1)
      have h := Finset.card_le_card unionSub
      rw [Finset.card_union_of_disjoint dis,memberCount] at h
      change r l + (highOn l).card ≤ 6 at h
      omega
    have highSub : high ⊆ fiveLines.biUnion highOn := by
      intro p hp
      obtain ⟨l,positive,pm⟩ := readOn p hp
      have notSmall : ¬ r l ≤ 4 := fun small => by
        have hit : l ∈ smallLines := Finset.mem_filter.mpr ⟨Finset.mem_univ _, positive, small⟩
        have h := Finset.card_pos.mpr (show smallLines.Nonempty from ⟨l,hit⟩)
        omega
      have notFull : r l ≠ 6 := fun h => existsFull ⟨l,h⟩
      have cap := rowCap l
      have five : r l = 5 := by omega
      have lf : l ∈ fiveLines := Finset.mem_filter.mpr ⟨Finset.mem_univ _,five⟩
      exact Finset.mem_biUnion.mpr ⟨l,lf,Finset.mem_inter.mpr ⟨pm,hp⟩⟩
    have highBound := calc
      high.card ≤ (fiveLines.biUnion highOn).card := Finset.card_le_card highSub
      _ ≤ ∑ l ∈ fiveLines, (highOn l).card := Finset.card_biUnion_le
      _ ≤ ∑ _l ∈ fiveLines, (1 : ℕ) := Finset.sum_le_sum capHigh
      _ = fiveLines.card := by simp
    omega


theorem elevenRowsAndColumns (C : List (Finset (Fin 31) × Finset (Fin 31)))
    (budget : C.length ≤ 17)
    (zero : ∀ r ∈ C, ZeroRectangle incident r)
    (cover : ∀ p l, ¬incident p l → ∃ r ∈ C, p ∈ r.1 ∧ l ∈ r.2) :
    let original : Fin C.length → Finset (Fin 31) × Finset (Fin 31) := C.get
    let swapped : Fin C.length → Finset (Fin 31) × Finset (Fin 31) :=
      fun i => ((C.get i).2, (C.get i).1)
    11 ≤ (Finset.univ.filter fun p => 3 ≤ (slotsContaining original p).card).card ∧
      11 ≤ (Finset.univ.filter fun l => 3 ≤ (slotsContaining swapped l).card).card := by
  obtain ⟨zer,cov⟩ := listCover incident C zero cover
  have sz : Fintype.card (Fin C.length) ≤ 17 := by simpa using budget
  obtain ⟨through,unique,sep,absent⟩ := orderFiveRowGeometry incident rowCount commonLineCount
  obtain ⟨throughT,uniqueT,sepT,absentT⟩ :=
    orderFiveRowGeometry (fun l p => incident p l) columnCount commonPointCount
  constructor
  · exact elevenHighReadVertices incident through unique sep absent columnCount throughT C.get zer cov sz
  · let swapped : Fin C.length → Finset (Fin 31) × Finset (Fin 31) :=
      fun i => ((C.get i).2, (C.get i).1)
    exact elevenHighReadVertices (fun l p => incident p l) throughT uniqueT sepT absentT rowCount through
      swapped (fun i l il p ip => zer i p ip l il)
      (fun l p absent => by
        obtain ⟨i, ip, il⟩ := cov p l absent
        exact ⟨i, il, ip⟩) sz

end RectangleReadPairs
