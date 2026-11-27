import PlaneCompletion

namespace PlaneCompletion

private def shifts : Fin 4 → ℕ := ![0, 1, 3, 9]

private def shiftPoint (shift : Fin 4) (line : Fin 12) : Fin 25 :=
  Fin.ofNat 25 ((line.val + shifts shift + 1) % 13)

private def shiftLine (line : Fin 12) : Fin 25 := Fin.natAdd 13 line

private def shiftEdge (shift : Fin 4) (line : Fin 12) : Fin 25 × Fin 25 :=
  (shiftPoint shift line, shiftLine line)

private def shiftEnd (shift : Fin 4) (line : Fin 12) (left : Bool) : Fin 25 :=
  if left then shiftPoint shift line else shiftLine line

private theorem shiftAdj : ∀ d i, G.Adj (shiftPoint d i) (shiftLine i) := by
  decide +kernel

private theorem shiftSides : ∀ d i, (shiftPoint d i).val < 13 ∧ 13 ≤ (shiftLine i).val := by
  decide +kernel

private theorem shiftsDisjoint : ∀ d e : Fin 4, d ≠ e → ∀ i j : Fin 12,
    shiftEdge d i ≠ shiftEdge e j := by decide +kernel

private theorem withinShiftDisjoint : ∀ d : Fin 4, ∀ i j : Fin 12, i ≠ j → ∀ a b : Bool,
    shiftEnd d i a ≠ shiftEnd d j b := by decide +kernel

private theorem intactShift (removed : Finset (Fin 25 × Fin 25)) (small : removed.card ≤ 3) :
    ∃ d : Fin 4, ∀ i : Fin 12, shiftEdge d i ∉ removed := by
  classical
  by_contra! exhausted
  choose hit inside using exhausted
  let f := fun d : Fin 4 => shiftEdge d (hit d)
  have inj : Function.Injective f := by
    intro d e eq
    by_contra different
    exact shiftsDisjoint d e different _ _ eq
  have subset : Finset.univ.image f ⊆ removed := by
    intro e member
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp member
    exact inside d
  have cards := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at cards
  omega

/-- Three point-to-line edge deletions leave at least one whole shift matching. -/
theorem minCoverAfterThree (removed : Finset (Fin 25 × Fin 25)) (small : removed.card ≤ 3)
    (T : Finset (Fin 25))
    (covers : ∀ u v, u.val < 13 → 13 ≤ v.val → G.Adj u v → (u, v) ∉ removed →
      u ∈ T ∨ v ∈ T) :
    12 ≤ T.card := by
  obtain ⟨d, intact⟩ := intactShift removed small
  let f (i : Fin 12) := shiftEnd d i (decide (shiftPoint d i ∈ T))
  have inj : Function.Injective f := by
    intro i j eq
    by_contra different
    exact withinShiftDisjoint d i j different _ _ eq
  have subset : Finset.univ.image f ⊆ T := by
    intro w member
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
    obtain ⟨point, line⟩ := shiftSides d i
    rcases covers _ _ point line (shiftAdj d i) (intact i) with left | right
    · simp [f, shiftEnd, left]
    · by_cases h : shiftPoint d i ∈ T
      · simp [f, shiftEnd, h]
      · simpa [f, shiftEnd, h] using right
  have cards := Finset.card_le_card subset
  rwa [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at cards

theorem allLineDegreesFour : ∀ l : Fin 12,
    (Finset.univ.filter fun p : Fin 25 => G.Adj p (shiftLine l)).card = 4 := by decide +kernel

theorem degreeBetweenThreeAndFour : ∀ v : Fin 25,
    3 ≤ (Finset.univ.filter (G.Adj v)).card ∧ (Finset.univ.filter (G.Adj v)).card ≤ 4 := by
  decide +kernel

theorem fourDegreePoints :
    (Finset.univ.filter (fun p : Fin 25 => p.val < 13 ∧
      (Finset.univ.filter (G.Adj p)).card = 4)).card = 9 := by
  decide +kernel

end PlaneCompletion
