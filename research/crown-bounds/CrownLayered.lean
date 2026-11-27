import CrownBlocks

/-! Necessary support constraints in the transposed OR layer. -/

namespace CrownLayered

variable {A : Type*} [DecidableEq A]

def CrownCover (row col : Fin 4 → Finset A) : Prop :=
  ∀ i j, (row i ∩ col j).Nonempty ↔ i ≠ j

theorem row_antichain {row col : Fin 4 → Finset A} (cover : CrownCover row col)
    {i j : Fin 4} (different : i ≠ j) : ¬row i ⊆ row j := by
  intro sub
  obtain ⟨v, hv⟩ := (cover i j).2 different
  obtain ⟨vr, vc⟩ := Finset.mem_inter.mp hv
  exact (cover j j).1 ⟨v, Finset.mem_inter.mpr ⟨sub vr, vc⟩⟩ rfl

theorem cover_swap {row col : Fin 4 → Finset A} (cover : CrownCover row col) :
    CrownCover col row := by
  intro i j
  simpa [Finset.inter_comm, ne_comm] using cover j i

theorem no_common_column_slot {row col : Fin 4 → Finset A} (cover : CrownCover row col)
    (used : ∀ a, (∃ j, a ∈ col j) → ∃ i, a ∈ row i) (a : A) :
    ¬∀ j, a ∈ col j := by
  intro common
  obtain ⟨i, hr⟩ := used a ⟨0, common 0⟩
  exact (cover i i).1 ⟨a, Finset.mem_inter.mpr ⟨hr, common i⟩⟩ rfl

/-- A non-singleton output needs a gate. An output of size at least three
    has a prior nontrivial operand with strictly smaller support. -/
structure DemandGates (S : Fin 4 → Finset A) (gates : Finset (Finset A)) : Prop where
  output : ∀ i, 2 ≤ (S i).card → S i ∈ gates
  operand : ∀ i, 3 ≤ (S i).card → ∃ h ∈ gates, 2 ≤ h.card ∧ h ⊂ S i

theorem six_of_large_columns {row col : Fin 4 → Finset A}
    {gates : Finset (Finset A)} (cover : CrownCover row col)
    (used : ∀ a, (∃ j, a ∈ col j) → ∃ i, a ∈ row i)
    (realize : DemandGates col gates) (large : ∀ i, 3 ≤ (col i).card) :
    6 ≤ gates.card := by
  classical
  have antichain := fun {i j : Fin 4} => row_antichain (cover_swap cover) (i := i) (j := j)
  have injective : Function.Injective col := by
    intro i j eq
    by_contra ne
    exact antichain ne (by rw [eq])
  let outputs : Finset (Finset A) := Finset.univ.image col
  have count : outputs.card = 4 := by simp [outputs, Finset.card_image_of_injective _ injective]
  have outputsSub : outputs ⊆ gates := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact realize.output i (by have := large i; omega)
  have helperOutside (i : Fin 4) : ∃ h ∈ gates \ outputs, 2 ≤ h.card ∧ h ⊂ col i := by
    obtain ⟨h, gate, nontrivial, smaller⟩ := realize.operand i (large i)
    refine ⟨h, Finset.mem_sdiff.mpr ⟨gate, ?_⟩, nontrivial, smaller⟩
    intro mem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp mem
    by_cases same : j = i
    · subst j
      exact (lt_irrefl (col i)) smaller
    · exact antichain same smaller.subset
  by_contra tooSmall
  have helpers : (gates \ outputs).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset outputsSub, count]
    omega
  obtain ⟨h, hh, hn, _⟩ := helperOutside 0
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < h.card)
  apply no_common_column_slot cover used a
  intro i
  obtain ⟨other, existing, _, smaller⟩ := helperOutside i
  have same := Finset.card_le_one.mp helpers h hh other existing
  exact smaller.subset (same ▸ ha)

end CrownLayered
