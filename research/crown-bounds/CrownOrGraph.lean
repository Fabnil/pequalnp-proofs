import CrownOrSupport

namespace CrownOrGraph

open CrownForks CrownFourNetwork CrownFourNormal CrownFirstAnd CrownAllOrModel CrownOrSupport CrownOrReaders

def word4 (a b c d : Bool) : ℕ := a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat

def word6 (a b c d e f : Bool) : ℕ :=
  a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat + 16 * e.toNat + 32 * f.toNat

theorem word4_range : ∀ a b c d : Bool, word4 a b c d < 16 := by decide +kernel

theorem word6_range : ∀ a b c d e f : Bool, word6 a b c d e f < 64 := by decide +kernel

theorem word4_bits : ∀ a b c d : Bool,
    (word4 a b c d).testBit 0 = a ∧ (word4 a b c d).testBit 1 = b ∧
    (word4 a b c d).testBit 2 = c ∧ (word4 a b c d).testBit 3 = d := by decide +kernel

theorem word6_bits : ∀ a b c d e f : Bool,
    (word6 a b c d e f).testBit 0 = a ∧ (word6 a b c d e f).testBit 1 = b ∧
    (word6 a b c d e f).testBit 2 = c ∧ (word6 a b c d e f).testBit 3 = d ∧
    (word6 a b c d e f).testBit 4 = e ∧ (word6 a b c d e f).testBit 5 = f := by decide +kernel

variable {I : Type} [DecidableEq I]

def uses (N : Network I) (s : Fin 3) (t : Fin 4) : Bool :=
  decide (0 < N.readsFlag s t)

def starts (N : Network I) (i : I) (t : Fin 4) : Bool :=
  decide (0 < N.stages.rawAt t i)

def activeBit (N : Network I) (i : I) (t : Fin 4) : Bool :=
  signal N.forest t.val (singletonInput i)

def graph (N : Network I) : Fin 64 :=
  ⟨word6 (uses N 0 1) (uses N 0 2) (uses N 0 3) (uses N 1 2) (uses N 1 3) (uses N 2 3),
    word6_range _ _ _ _ _ _⟩

def roots (N : Network I) (i : I) : Fin 16 :=
  ⟨word4 (starts N i 0) (starts N i 1) (starts N i 2) (starts N i 3), word4_range _ _ _ _⟩

def actual (N : Network I) (i : I) : Fin 16 :=
  ⟨word4 (activeBit N i 0) (activeBit N i 1) (activeBit N i 2) (activeBit N i 3),
    word4_range _ _ _ _⟩

theorem roots_bits (N : Network I) (i : I) (t : Fin 4) :
    (roots N i).val.testBit t.val = starts N i t := by
  obtain ⟨a, b, c, d⟩ := word4_bits (starts N i 0) (starts N i 1) (starts N i 2) (starts N i 3)
  fin_cases t <;> first | exact a | exact b | exact c | exact d

theorem actual_bits (N : Network I) (i : I) (t : Fin 4) :
    (actual N i).val.testBit t.val = activeBit N i t := by
  obtain ⟨a, b, c, d⟩ := word4_bits (activeBit N i 0) (activeBit N i 1) (activeBit N i 2) (activeBit N i 3)
  fin_cases t <;> first | exact a | exact b | exact c | exact d

theorem use_forward (N : Network I) (s : Fin 3) (t : Fin 4) (h : t.val ≤ s.val) :
    uses N s t = false := by
  apply Bool.eq_false_of_not_eq_true
  intro on
  have lt := N.readsFlag_forward s t (of_decide_eq_true on)
  omega

theorem nonzero_of_link (N : Network I) {s : Fin 3} {t : Fin 4} (read : 0 < N.readsFlag s t) :
    (graph N).val ≠ 0 := by
  intro zero
  have bits := word6_bits (uses N 0 1) (uses N 0 2) (uses N 0 3) (uses N 1 2) (uses N 1 3) (uses N 2 3)
  change word6 (uses N 0 1) (uses N 0 2) (uses N 0 3) (uses N 1 2) (uses N 1 3) (uses N 2 3) = 0 at zero
  rw [zero] at bits
  obtain ⟨a, b, c, d, e, f⟩ := bits
  have on : uses N s t = true := decide_eq_true read
  have lt := N.readsFlag_forward s t read
  fin_cases s <;> fin_cases t
  all_goals
    first
    | (revert lt; decide)
    | exact Bool.false_ne_true (a.trans on)
    | exact Bool.false_ne_true (b.trans on)
    | exact Bool.false_ne_true (c.trans on)
    | exact Bool.false_ne_true (d.trans on)
    | exact Bool.false_ne_true (e.trans on)
    | exact Bool.false_ne_true (f.trans on)

private def evaluateClosed (g r : ℕ) : ℕ :=
  let a := r.testBit 0
  let b := r.testBit 1 || (g.testBit 0 && a)
  let c := r.testBit 2 || ((g.testBit 1 && a) || (g.testBit 3 && b))
  let d := r.testBit 3 || ((g.testBit 2 && a) || ((g.testBit 4 && b) || (g.testBit 5 && c)))
  word4 a b c d

private theorem closure_computed :
    ∀ g : Fin 64, ∀ r : Fin 16, CrownOrProfiles.closure g.val r.val = evaluateClosed g.val r.val := by
  decide +kernel

variable {N : Network Ten}

private theorem stage_relation (C : Case N) (i : Ten) (t : Fin 4) :
    activeBit N i t = (starts N i t || ((uses N 0 t && activeBit N i 0) ||
      ((uses N 1 t && activeBit N i 1) || (uses N 2 t && activeBit N i 2)))) := by
  have pure := orPrefix_mono N.forest (Nat.succ_le_of_lt t.isLt) C.pure
  have previous (s : Fin 3) (used : uses N s t = true) (on : activeBit N i s.castSucc = true) :
      activeBit N i t = true :=
    Bool.le_iff_imp.mp (N.or_flag_implies s t pure (of_decide_eq_true used) _) on
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · intro on
    rcases N.or_stage_reason t pure i on with raw | ⟨s, used, yes⟩
    · exact Or.inl (decide_eq_true raw)
    · have use : uses N s t = true := decide_eq_true used
      fin_cases s
      · exact Or.inr (Or.inl ⟨use, yes⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨use, yes⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨use, yes⟩))
  · rintro (raw | ⟨u, on⟩ | ⟨u, on⟩ | ⟨u, on⟩)
    · exact N.direct_or_on t i pure (of_decide_eq_true raw)
    · exact previous 0 u on
    · exact previous 1 u on
    · exact previous 2 u on

/-- The singleton's active signals are exactly the forward closure of the
    stages which read the singleton directly. -/
theorem actual_eq_closure (C : Case N) (i : Ten) :
    (actual N i).val = CrownOrProfiles.closure (graph N).val (roots N i).val := by
  have p : activeBit N i 0 = starts N i 0 := by
    simpa only [use_forward N 0 0 (by decide), use_forward N 1 0 (by decide), use_forward N 2 0 (by decide),
      Bool.false_and, Bool.or_false] using stage_relation C i 0
  have q : activeBit N i 1 = (starts N i 1 || (uses N 0 1 && activeBit N i 0)) := by
    simpa only [use_forward N 1 1 (by decide), use_forward N 2 1 (by decide),
      Bool.false_and, Bool.or_false] using stage_relation C i 1
  have r : activeBit N i 2 = (starts N i 2 ||
      ((uses N 0 2 && activeBit N i 0) || (uses N 1 2 && activeBit N i 1))) := by
    simpa only [use_forward N 2 2 (by decide), Bool.false_and, Bool.or_false] using stage_relation C i 2
  have d := stage_relation C i 3
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ :=
    word6_bits (uses N 0 1) (uses N 0 2) (uses N 0 3) (uses N 1 2) (uses N 1 3) (uses N 2 3)
  rw [closure_computed]
  change word4 _ _ _ _ = evaluateClosed
    (word6 (uses N 0 1) (uses N 0 2) (uses N 0 3) (uses N 1 2) (uses N 1 3) (uses N 2 3)) (roots N i).val
  have r0 : (roots N i).val.testBit 0 = starts N i 0 := roots_bits N i 0
  have r1 : (roots N i).val.testBit 1 = starts N i 1 := roots_bits N i 1
  have r2 : (roots N i).val.testBit 2 = starts N i 2 := roots_bits N i 2
  have r3 : (roots N i).val.testBit 3 = starts N i 3 := roots_bits N i 3
  simp only [evaluateClosed, g0, g1, g2, g3, g4, g5, r0, r1, r2, r3]
  rw [← p, ← q, ← r, ← d]

theorem included_bits : ∀ a b : Fin 16,
    CrownOrProfiles.includes b.val a.val = true ↔
      ∀ k : Fin 4, a.val.testBit k.val = true → b.val.testBit k.val = true := by decide +kernel

end CrownOrGraph
