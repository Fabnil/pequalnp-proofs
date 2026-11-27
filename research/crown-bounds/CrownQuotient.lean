import CrownBlocks

namespace CrownQuotient

open CrownThreshold

/-- Rows retain their labels. A column moves to the other group under the
    straight cross-block matching. -/
def column (v : Fin 8) : Fin 8 := Fin.ofNat 8 (v.val + 4)

def adj (u v : Fin 8) : Bool :=
  decide (u.val / 4 ≠ v.val / 4 ∧ u.val % 4 ≠ v.val % 4)

theorem column_twice (v : Fin 8) : column (column v) = v := by
  fin_cases v <;> decide

theorem adj_column (u v : Fin 8) : adj u (column v) = CrownBlocks.adj (blocks := 2) u v := by
  fin_cases u <;> fin_cases v <;> decide

/-- The original promise after the eight ORs tests every quotient pair,
    including singleton inputs and two inputs on the same quotient side. -/
theorem pairedPromise_iff (f : (Fin 8 → Bool) → Bool) :
    (∀ u v : Fin 8, f (pairInput u (column v)) = CrownBlocks.adj (blocks := 2) u v) ↔
      ∀ u v : Fin 8, f (pairInput u v) = adj u v := by
  constructor
  · intro h u v
    have result := h u (column v)
    rw [column_twice] at result
    rw [← adj_column u (column v), column_twice] at result
    exact result
  · intro h u v
    exact (h u (column v)).trans (adj_column u v)

/-- A paired label has both a row port and a column port. An unpaired label
    keeps one port when the other is set to zero. -/
def rowKept (missing rows : Finset (Fin 8)) (a : Fin 8) : Prop :=
  a ∉ missing ∨ a ∈ rows

def colKept (missing rows : Finset (Fin 8)) (a : Fin 8) : Prop :=
  a ∉ missing ∨ a ∉ rows

def visible (missing rows : Finset (Fin 8)) (a b : Fin 8) : Prop :=
  (rowKept missing rows a ∧ colKept missing rows b) ∨
    (rowKept missing rows b ∧ colKept missing rows a)

theorem hidden_iff (missing rows : Finset (Fin 8)) (a b : Fin 8) :
    ¬visible missing rows a b ↔ a ∈ missing ∧ b ∈ missing ∧
      ((a ∈ rows ∧ b ∈ rows) ∨ (a ∉ rows ∧ b ∉ rows)) := by
  unfold visible rowKept colKept
  tauto

theorem visible_of_missing_le_two (missing : Finset (Fin 8)) (bound : missing.card ≤ 2) :
    ∃ rows : Finset (Fin 8), ∀ a b, a ≠ b → visible missing rows a b := by
  by_cases nonempty : missing.Nonempty
  · obtain ⟨t, ht⟩ := nonempty
    refine ⟨{t}, fun a b ne => ?_⟩
    by_contra hidden
    obtain ⟨ha, hb, side⟩ := (hidden_iff missing {t} a b).mp hidden
    rcases side with both | neither
    · exact ne ((Finset.mem_singleton.mp both.1).trans (Finset.mem_singleton.mp both.2).symm)
    · have included : ({a, b} : Finset (Fin 8)) ⊆ missing.erase t := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_erase.mpr ⟨by simpa using neither.1, ha⟩
        · exact Finset.mem_erase.mpr ⟨by simpa using neither.2, hb⟩
      have count := Finset.card_le_card included
      simp [ne, Finset.card_erase_of_mem ht] at count
      omega
  · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
    subst missing
    exact ⟨∅, fun _ _ _ => by simp [visible, rowKept, colKept]⟩

private theorem pairInput_comm (a b : Fin 8) : pairInput a b = pairInput b a := by
  funext i
  simp [pairInput, or_comm]

private theorem adj_comm (a b : Fin 8) : adj a b = adj b a := by
  unfold adj
  congr 1
  exact propext ⟨fun ⟨p, q⟩ => ⟨p.symm, q.symm⟩, fun ⟨p, q⟩ => ⟨p.symm, q.symm⟩⟩

private theorem negative_partner (a : Fin 8) : ∃ b : Fin 8, b ≠ a ∧ adj a b = false := by
  fin_cases a <;> decide

/-- Visible pairs keep their prescribed value. Each singleton also keeps its
    value when it has a visible negative superset. -/
theorem quotient_on_visible {f : (Fin 8 → Bool) → Bool} {missing rows : Finset (Fin 8)}
    (mono : ∀ x y, (∀ i, x i ≤ y i) → f x ≤ f y)
    (negatives : ∀ a, ∃ b, visible missing rows a b ∧ adj a b = false)
    (values : ∀ a b, rowKept missing rows a → colKept missing rows b →
      f (pairInput a b) = adj a b) :
    (∀ a b, visible missing rows a b → f (pairInput a b) = adj a b) ∧
      ∀ a, f (pairInput a a) = false := by
  have pair (a b : Fin 8) (visiblePair : visible missing rows a b) : f (pairInput a b) = adj a b := by
    rcases visiblePair with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact values a b ha hb
    · rw [pairInput_comm a b, adj_comm a b]
      exact values b a hb ha
  refine ⟨pair, fun a => ?_⟩
  obtain ⟨b, seen, neg⟩ := negatives a
  have pointwise (i : Fin 8) : pairInput a a i ≤ pairInput a b i := by
    by_cases h : i = a <;> simp [pairInput, h]
  have lower := mono (pairInput a a) (pairInput a b) pointwise
  rw [pair a b seen, neg] at lower
  exact Bool.eq_false_of_le_false lower

/-- Keeping opposite ports for at most two missing pairs gives the full
    quotient promise. Monotonicity supplies the singleton tests. -/
theorem quotient_of_visible {f : (Fin 8 → Bool) → Bool} {missing rows : Finset (Fin 8)}
    (mono : ∀ x y, (∀ i, x i ≤ y i) → f x ≤ f y)
    (covers : ∀ a b, a ≠ b → visible missing rows a b)
    (values : ∀ a b, rowKept missing rows a → colKept missing rows b →
      f (pairInput a b) = adj a b) :
    ∀ a b, f (pairInput a b) = adj a b := by
  obtain ⟨pair, singleton⟩ := quotient_on_visible mono (fun a => by
    obtain ⟨b, ne, neg⟩ := negative_partner a
    exact ⟨b, covers a b ne.symm, neg⟩) values
  intro a b
  by_cases eq : a = b
  · subst b
    simpa [adj] using singleton a
  · exact pair a b (covers a b eq)

end CrownQuotient
