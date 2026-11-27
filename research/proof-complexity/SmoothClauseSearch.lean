import PEqualNP.Defs

namespace SmoothClauseSearch

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V] [Fintype V]

def flip (v : V) (x : V → Bool) : V → Bool := Function.update x v (!x v)

omit [Fintype V] in
private theorem flipTwice (v : V) : Function.Involutive (flip v) := by
  intro x
  funext u
  by_cases eq : u = v
  · subst u
    simp [flip]
  · simp [flip, Function.update_of_ne eq]

def Smooth (μ : (V → Bool) → ℝ) (R : ℕ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ 0 < ∑ x, μ x ∧ ∀ x v, μ x ≤ (R : ℝ) * μ (flip v x)

noncomputable def cylinder (x : V → Bool) (pins : Finset V) : Finset (V → Bool) := by
  classical
  exact Finset.univ.filter fun y => ∀ v ∈ pins, y v = x v

/-- Conditioning on one coordinate costs at most a factor of `R+1`. -/
private theorem pinMass (μ : (V → Bool) → ℝ) (R : ℕ) (smooth : Smooth μ R)
    (src : Finset (V → Bool)) (v : V) (bit : Bool)
    (stable : ∀ y, flip v y ∈ src ↔ y ∈ src) :
    (∑ y ∈ src, μ y) ≤ ((R : ℝ) + 1) * ∑ y ∈ src.filter (fun y => y v = bit), μ y := by
  classical
  let pass := src.filter fun y => y v = bit
  let fail := src.filter fun y => ¬ y v = bit
  have opposite (y : V → Bool) : flip v y v = bit ↔ y v ≠ bit := by
    simp only [flip, Function.update_self]
    cases y v <;> cases bit <;> decide
  have onto : fail.image (flip v) = pass := by
    ext y
    simp only [Finset.mem_image, fail, pass, Finset.mem_filter]
    constructor
    · rintro ⟨z, ⟨mem, wrong⟩, rfl⟩
      exact ⟨(stable z).mpr mem, (opposite z).mpr wrong⟩
    · intro mem
      refine ⟨flip v y, ⟨(stable y).mpr mem.1, ?_⟩, flipTwice v y⟩
      intro eq
      exact (opposite y).mp eq mem.2
  have failBound : (∑ y ∈ fail, μ y) ≤ (R : ℝ) * ∑ y ∈ pass, μ y := by
    calc
      _ ≤ ∑ y ∈ fail, (R : ℝ) * μ (flip v y) := Finset.sum_le_sum fun y _ => smooth.2.2 y v
      _ = ∑ y ∈ fail.image (flip v), (R : ℝ) * μ y := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ eq => (flipTwice v).injective eq
      _ = _ := by rw [onto, Finset.mul_sum]
  have splitMass : (∑ y ∈ pass, μ y) + (∑ y ∈ fail, μ y) = ∑ y ∈ src, μ y :=
    Finset.sum_filter_add_sum_filter_not src (fun y => y v = bit) _
  change _ ≤ ((R : ℝ) + 1) * ∑ y ∈ pass, μ y
  rw [← splitMass, add_mul, one_mul]
  linarith

theorem conditionalCylinderMass (μ : (V → Bool) → ℝ) (R : ℕ) (smooth : Smooth μ R)
    (src : Finset (V → Bool)) (x : V → Bool) (pins : Finset V)
    (stable : ∀ v ∈ pins, ∀ y, flip v y ∈ src ↔ y ∈ src) :
    (∑ y ∈ src, μ y) ≤ ((R : ℝ) + 1)^pins.card * ∑ y ∈ src ∩ cylinder x pins, μ y := by
  classical
  induction pins using Finset.induction_on with
  | empty => simp [cylinder]
  | @insert v pins fresh prior =>
    have previous := prior (fun u hu => stable u (Finset.mem_insert_of_mem hu))
    have keepPinned (y : V → Bool) : flip v y ∈ cylinder x pins ↔ y ∈ cylinder x pins := by
      simp only [cylinder, Finset.mem_filter, Finset.mem_univ, true_and, flip]
      apply forall₂_congr
      intro u hu
      have different : u ≠ v := fun eq => fresh (eq ▸ hu)
      rw [Function.update_of_ne different]
    have keeps (y : V → Bool) : flip v y ∈ src ∩ cylinder x pins ↔ y ∈ src ∩ cylinder x pins := by
      simp only [Finset.mem_inter, stable v (Finset.mem_insert_self _ _) y, keepPinned]
    have addPin : (src ∩ cylinder x pins).filter (fun y => y v = x v) =
        src ∩ cylinder x (insert v pins) := by
      ext y
      simp [cylinder, and_left_comm, and_comm]
    have mass := pinMass μ R smooth (src ∩ cylinder x pins) v (x v) keeps
    rw [addPin] at mass
    rw [Finset.card_insert_of_notMem fresh, pow_succ, mul_assoc]
    exact previous.trans (mul_le_mul_of_nonneg_left mass (by positivity))

theorem cylinderMass (μ : (V → Bool) → ℝ) (R : ℕ) (smooth : Smooth μ R)
    (x : V → Bool) (pins : Finset V) :
    (∑ y, μ y) ≤ ((R : ℝ) + 1)^pins.card * ∑ y ∈ cylinder x pins, μ y := by
  simpa using conditionalCylinderMass μ R smooth Finset.univ x pins (by simp)

/-- One true literal in each clause suffices to preserve all of them. -/
theorem satisfyingCylinder (C : Finset (Clause V)) (x : V → Bool)
    (sat : ∀ cl ∈ C, ClauseSat x cl) :
    ∃ pins : Finset V, pins.card ≤ C.card ∧
      ∀ y ∈ cylinder x pins, ∀ cl ∈ C, ClauseSat y cl := by
  classical
  induction C using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | @insert cl C fresh prior =>
    obtain ⟨pins, count, holds⟩ := prior (fun a ha => sat a (Finset.mem_insert_of_mem ha))
    obtain ⟨l, inClause, trueL⟩ := sat cl (Finset.mem_insert_self _ _)
    refine ⟨insert l.1 pins, ?_, ?_⟩
    · exact (Finset.card_insert_le _ _).trans (by rw [Finset.card_insert_of_notMem fresh]; omega)
    · intro y mem a ha
      have agrees : ∀ u ∈ insert l.1 pins, y u = x u := (Finset.mem_filter.mp mem).2
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact ⟨l, inClause, (agrees l.1 (Finset.mem_insert_self _ _)).trans trueL⟩
      · exact holds y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun u hu => agrees u (Finset.mem_insert_of_mem hu)⟩) a ha

/-- A satisfiable union of listed clauses gives an accuracy ceiling. -/
theorem accuracyLeUnion (μ : (V → Bool) → ℝ) (R h : ℕ) (smooth : Smooth μ R)
    (C : Finset (Clause V)) (x : V → Bool) (sat : ∀ cl ∈ C, ClauseSat x cl)
    (bad : Finset (V → Bool)) (allSatisfiedBad : ∀ y, (∀ cl ∈ C, ClauseSat y cl) → y ∈ bad)
    (accurate : (2 : ℝ)^h * (∑ y ∈ bad, μ y) ≤ ∑ y, μ y) :
    h ≤ Nat.clog 2 (R+1) * C.card := by
  classical
  obtain ⟨pins, count, satis⟩ := satisfyingCylinder C x sat
  have mass := cylinderMass μ R smooth x pins
  have sub : cylinder x pins ⊆ bad := fun y mem => allSatisfiedBad y (satis y mem)
  have more : (∑ y ∈ cylinder x pins, μ y) ≤ ∑ y ∈ bad, μ y :=
    Finset.sum_le_sum_of_subset_of_nonneg sub (fun y _ _ => smooth.1 y)
  have positive : 0 < ∑ y ∈ bad, μ y := by
    by_contra! nonpos
    exact (not_le_of_gt smooth.2.1) (mass.trans (mul_nonpos_of_nonneg_of_nonpos
      (by positivity) (more.trans nonpos)))
  have ceiling : (2 : ℝ)^h ≤ ((R : ℝ)+1)^pins.card := by
    apply le_of_mul_le_mul_right _ positive
    exact accurate.trans (mass.trans (mul_le_mul_of_nonneg_left more (by positivity)))
  have power : ((R : ℝ)+1) ≤ (2 : ℝ)^Nat.clog 2 (R+1) := by
    exact_mod_cast (Nat.le_pow_clog (by decide : 1 < 2) (R+1))
  have bound : (2 : ℝ)^h ≤ (2 : ℝ)^(Nat.clog 2 (R+1) * C.card) := calc
    _ ≤ ((R : ℝ)+1)^pins.card := ceiling
    _ ≤ ((2 : ℝ)^Nat.clog 2 (R+1))^pins.card := by gcongr
    _ ≤ _ := by
      rw [← pow_mul]
      gcongr
      norm_num
  exact (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mp bound

noncomputable def hitsEveryRow (rows : List (Finset V)) : Finset (V → Bool) := by
  classical
  exact Finset.univ.filter fun y => ∀ row ∈ rows, ∃ v ∈ row, y v = true

/-- On disjoint rows, the mass of seeing no all-zero row decays geometrically
even when the source coordinates are correlated. -/
theorem allRowsHitMass (μ : (V → Bool) → ℝ) (R d : ℕ) (smooth : Smooth μ R)
    (rows : List (Finset V)) (disjoint : rows.Pairwise Disjoint)
    (width : ∀ row ∈ rows, row.card ≤ d) :
    let Z := ((R : ℝ) + 1)^d
    Z^rows.length * (∑ y ∈ hitsEveryRow rows, μ y) ≤ (Z-1)^rows.length * ∑ y, μ y := by
  classical
  let Z := ((R : ℝ) + 1)^d
  have oneBase : 1 ≤ (R : ℝ) + 1 := by
    have nonneg : 0 ≤ (R : ℝ) := by positivity
    linarith
  have large : 1 ≤ Z := one_le_pow₀ oneBase
  have base : 0 ≤ Z := le_trans (by norm_num) large
  have residual : 0 ≤ Z-1 := sub_nonneg.mpr large
  change Z^rows.length * (∑ y ∈ hitsEveryRow rows, μ y) ≤ (Z-1)^rows.length * ∑ y, μ y
  induction rows with
  | nil => simp [hitsEveryRow]
  | cons row rows prior =>
    obtain ⟨apart, tail⟩ := List.pairwise_cons.mp disjoint
    let src := hitsEveryRow rows
    let zero := cylinder (fun _ : V => false) row
    have memSrc (y : V → Bool) : y ∈ src ↔ ∀ r ∈ rows, ∃ v ∈ r, y v = true := by
      simp [src, hitsEveryRow]
    have stable (v : V) (inRow : v ∈ row) (y : V → Bool) : flip v y ∈ src ↔ y ∈ src := by
      simp only [memSrc]
      apply forall₂_congr
      intro r hr
      apply exists_congr
      intro u
      apply and_congr_right
      intro hu
      have ne : u ≠ v := fun eq => (Finset.disjoint_left.mp (apart r hr)) inRow (eq ▸ hu)
      simp [flip, Function.update_of_ne ne]
    have cond := conditionalCylinderMass μ R smooth src (fun _ => false) row stable
    change (∑ y ∈ src, μ y) ≤ ((R : ℝ)+1)^row.card * (∑ y ∈ src ∩ zero, μ y) at cond
    have scaled : (∑ y ∈ src, μ y) ≤ Z * (∑ y ∈ src ∩ zero, μ y) := by
      apply cond.trans (mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun y _ => smooth.1 y))
      exact pow_right_mono₀ oneBase (width row (by simp))
    have hasHit (y : V → Bool) : (∃ v ∈ row, y v = true) ↔ y ∉ zero := by
      simp [zero, cylinder, not_forall, not_imp]
    have keep : src.filter (fun y => y ∉ zero) = hitsEveryRow (row :: rows) := by
      ext y
      simp only [Finset.mem_filter, memSrc, hitsEveryRow, Finset.mem_univ, true_and,
        List.forall_mem_cons, and_comm]
      exact and_congr (by simpa only [and_comm] using (hasHit y).symm) Iff.rfl
    have drop : src.filter (fun y => ¬ y ∉ zero) = src ∩ zero := by
      ext y
      simp
    have split : (∑ y ∈ hitsEveryRow (row :: rows), μ y) + (∑ y ∈ src ∩ zero, μ y) = ∑ y ∈ src, μ y := by
      rw [← keep, ← drop]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    have step : Z * (∑ y ∈ hitsEveryRow (row :: rows), μ y) ≤ (Z-1) * (∑ y ∈ src, μ y) := by
      linarith only [scaled, congrArg (fun x : ℝ => Z*x) split, split]
    have previous := prior tail (fun r hr => width r (List.mem_cons_of_mem _ hr))
    change _ ≤ (Z-1)^rows.length * ∑ y, μ y at previous
    calc
      _ = Z^rows.length * (Z * (∑ y ∈ hitsEveryRow (row :: rows), μ y)) := by
        rw [List.length_cons, pow_succ, mul_assoc]
      _ ≤ Z^rows.length * ((Z-1) * ∑ y ∈ src, μ y) :=
        mul_le_mul_of_nonneg_left step (pow_nonneg base _)
      _ = (Z-1) * (Z^rows.length * ∑ y ∈ src, μ y) := by ring
      _ ≤ (Z-1) * ((Z-1)^rows.length * ∑ y, μ y) := mul_le_mul_of_nonneg_left previous residual
      _ = _ := by rw [List.length_cons, pow_succ]; ring

private theorem halfAfterBlock (n : ℕ) (pos : 0 < n) :
    (((n : ℝ)-1)/(n : ℝ))^n ≤ 1/2 := by
  obtain one | large := eq_or_lt_of_le (Nat.succ_le_of_lt pos)
  · subst n
    norm_num
  · have oneLt : 1 < (n : ℝ) := by exact_mod_cast large
    have denom : 0 < (n : ℝ)-1 := sub_pos.mpr oneLt
    have ratio : 1 ≤ (n : ℝ)/((n : ℝ)-1) := (le_div_iff₀ denom).mpr (by linarith)
    have bern := one_add_mul_sub_le_pow (by linarith : -1 ≤ (n : ℝ)/((n : ℝ)-1)) n
    have term : (n : ℝ) * ((n : ℝ)/((n : ℝ)-1)-1) = (n : ℝ)/((n : ℝ)-1) := by
      field_simp [ne_of_gt denom]
      ring
    rw [term] at bern
    have two : (2 : ℝ) ≤ ((n : ℝ)/((n : ℝ)-1))^n := by linarith
    rw [div_pow] at two ⊢
    have h := (le_div_iff₀ (pow_pos denom n)).mp two
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < (n : ℝ)) n)).mpr
    linarith

theorem rowTestingAccuracy (μ : (V → Bool) → ℝ) (R d h : ℕ) (smooth : Smooth μ R)
    (rows : List (Finset V)) (disjoint : rows.Pairwise Disjoint)
    (width : ∀ row ∈ rows, row.card ≤ d) (enough : (R+1)^d*h ≤ rows.length) :
    (2 : ℝ)^h * (∑ y ∈ hitsEveryRow rows, μ y) ≤ ∑ y, μ y := by
  let n := (R+1)^d
  let Z : ℝ := n
  let q := (Z-1)/Z
  have nPos : 0 < n := by dsimp [n]; positivity
  have zPos : 0 < Z := by
    change 0 < (n : ℝ)
    exact_mod_cast nPos
  have zOne : 1 ≤ Z := by
    change 1 ≤ (n : ℝ)
    exact_mod_cast Nat.succ_le_of_lt nPos
  have qNonneg : 0 ≤ q := div_nonneg (by linarith) zPos.le
  have qOne : q ≤ 1 := (div_le_iff₀ zPos).mpr (by linarith)
  have zEq : ((R : ℝ)+1)^d = Z := by simp [Z, n, Nat.cast_pow]
  have raw := allRowsHitMass μ R d smooth rows disjoint width
  dsimp only at raw
  rw [zEq] at raw
  have mass : (∑ y ∈ hitsEveryRow rows, μ y) ≤ q^rows.length * ∑ y, μ y := by
    dsimp only [q]
    rw [div_pow, div_mul_eq_mul_div]
    exact (le_div_iff₀ (pow_pos zPos _)).mpr (by simpa only [mul_comm] using raw)
  have half : q^n ≤ (1/2 : ℝ) := halfAfterBlock n nPos
  have decay : q^rows.length ≤ (1/2 : ℝ)^h := calc
    _ ≤ q^(n*h) := pow_le_pow_of_le_one qNonneg qOne enough
    _ = (q^n)^h := pow_mul _ _ _
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg qNonneg _) half h
  calc
    _ ≤ (2 : ℝ)^h * (q^rows.length * ∑ y, μ y) :=
      mul_le_mul_of_nonneg_left mass (by positivity)
    _ ≤ (2 : ℝ)^h * ((1/2 : ℝ)^h * ∑ y, μ y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right decay smooth.2.1.le) (by positivity)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; norm_num

end SmoothClauseSearch

#print axioms SmoothClauseSearch.accuracyLeUnion
#print axioms SmoothClauseSearch.rowTestingAccuracy
